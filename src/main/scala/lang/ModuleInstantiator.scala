package uclid
package lang

import scala.collection.immutable.Map

class ModuleInstanceCheckerPass(modules : List[Module]) extends ReadOnlyPass[List[ModuleError]] {
  val moduleMap = modules.map(m => (m.id -> m)).toMap

  def doesInstanceTypeMatch(modT : ModuleType, instT : ModuleInstanceType, in : List[ModuleError]) : List[ModuleError] = {
    // check the types of a list of pairs of identifiers and types..
    def checkTypes(args : List[(Identifier, Type)], in : List[ModuleError], argType : String, typeMap : Map[Identifier, Type]) : List[ModuleError] = {
      args.foldLeft(in) {
        (acc, arg) => {
          val id = arg._1
          val actualTyp = arg._2
          typeMap.get(id) match {
            case Some(expTyp) =>
              if (actualTyp.matches(expTyp)) {
                acc
              } else {
                val msg = "Incorrect type for module " + argType + ": " + id.toString + ". Expected " + 
                          actualTyp.toString + ", got " + expTyp.toString + " instead."
                ModuleError(msg, id.position) :: acc
              }
            case None =>
              // we've already reported this.
              acc
          }
        }
      }
    }
  
    // first check there are no unknown arguments (arguments that don't correspond to the I/Os of module).
    val badArgs = instT.args.map(_._1).filter(a => !modT.argSet.contains(a))
    val errs1 = badArgs.foldLeft(in) { 
      (acc, arg) => {
        ModuleError("Unknown module input/output: " + arg.toString, arg.position) :: acc
      }
    }
    // for this first let's filter out the inputs who are "wired"
    val wiredInputs = instT.args.filter((a) => modT.inputMap.contains(a._1) && a._2.isDefined).map((a) => (a._1, a._2.get))
    // now check that all input types match.
    val errs2 = checkTypes(wiredInputs, errs1, "input", modT.inputMap)

    // filter out wired outputs.
    val wiredOutputs = instT.args.filter((a) => modT.outputMap.contains(a._1) && a._2.isDefined).map((a) => (a._1, a._2.get))
    // check output types.
    val errs3 = checkTypes(wiredOutputs, errs2, "output", modT.outputMap)
    errs3
  }
  
  def checkInstance(inst : InstanceDecl, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    moduleMap.get(inst.moduleId) match {
      case None =>
        val error = ModuleError("Unknown module being instantiated: " + inst.moduleId.toString, inst.moduleId.position)
        error :: in
      case Some(targetMod) =>
        val targetModT = targetMod.moduleType
        Utils.assert(inst.instType.isDefined, "Instance type must be defined at this point!")
        val err1 = doesInstanceTypeMatch(targetModT, inst.instType.get, in)
        // make sure all outputs are wired to identifiers.
        val outputExprs = inst.arguments.filter(a => targetModT.outputMap.contains(a._1) && a._2.isDefined).map(_._2.get)
        outputExprs.foldLeft(err1) { 
          (acc, arg) => {
            arg match {
              case Identifier(name) =>
                acc
              case _ =>
                val msg = "Invalid module output: " + arg.toString() + "."
                ModuleError(msg, arg.position) :: acc
            }
          }
        }
    }
  }

  override def applyOnInstance(d : TraversalDirection.T, inst : InstanceDecl, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      // only need to check in one direction.
      checkInstance(inst, in, context)
    } else {
      in
    }
  }
}

class ModuleInstanceChecker(modules : List[Module]) extends ASTAnalyzer(
    "ModuleInstanceChecker", new ModuleInstanceCheckerPass(modules))
{
  override def reset() {
    in = Some(List.empty[ModuleError])
  }
  override def finish() {
    val errors = out.get
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map((e) => (e.msg, e.position)))
    }
  }
}

class ModuleDependencyFinderPass extends ReadOnlyPass[Map[Identifier, Set[Identifier]]] {
  type T = Map[Identifier, Set[Identifier]]
  override def applyOnInstance(d : TraversalDirection.T, inst : InstanceDecl, in : T, context : ScopeMap) : T = {
    if (d == TraversalDirection.Down) {
      // this module calls inst.moduleId
      val moduleName = context.module.get.id
      in.get(moduleName) match {
        case Some(modules) => in + (moduleName -> (modules + inst.moduleId))
        case None => in + (moduleName -> Set(inst.moduleId))
      }
    } else {
      in
    }
  }
}

class ModuleDependencyFinder(modules : List[Module], mainModuleName : Identifier) extends ASTAnalyzer(
    "LeafModuleFinder", new ModuleDependencyFinderPass())
{
  var moduleInstantiationOrder : Option[List[Identifier]] = None
  override def reset() {
    in = Some(Map.empty[Identifier, Set[Identifier]])
  }
  override def finish() {
    val depGraph = out.get
    def visit(mod : Identifier, visitOrder : Map[Identifier, Int]) : Map[Identifier, Int] = {
      if (visitOrder.contains(mod)) {
        visitOrder
      } else {
        val visitOrderP = visitOrder + (mod -> visitOrder.size)
        depGraph.get(mod) match {
          case Some(modules) =>
            modules.foldLeft(visitOrderP)((acc, m) => visit(m, acc))
          case None =>
            visitOrderP
        }
      }
    }
    // now walk through the dep graph
    val order = visit(mainModuleName, Map.empty[Identifier, Int])
    val instantiationOrder = order.toList.sortWith((p1, p2) => p1._2 > p2._2).map(p => p._1)
    moduleInstantiationOrder = Some(instantiationOrder)
    // println("order: " + instantiationOrder.toString)
  }
}



class ModuleInstantiatorPass(modules : List[Module], moduleName : Identifier) extends RewritePass {
  sealed abstract class InstanceVarRenaming(val ident : Identifier) 
  case class BoundInput(id : Identifier, expr : Expr) extends InstanceVarRenaming(id)
  case class UnboundInput(id : Identifier) extends InstanceVarRenaming(id)
  case class Output(id : Identifier) extends InstanceVarRenaming(id)
  case class StateVariable(id : Identifier) extends InstanceVarRenaming(id)
  
  val module = modules.find(_.id == moduleName).get

  def extractId (e : Expr) : Option[Identifier] = {
    e match {
      case id : Identifier => Some(id)
      case _ => None
    }
  }

  type VarMap = Map[Identifier, InstanceVarRenaming]
  type RewriteMap = Map[Expr, Expr]
  
  def toRewriteMap(varMap : VarMap) : RewriteMap = {
    val empty : RewriteMap = Map.empty
    varMap.foldLeft(empty) { 
      (acc, mapping) => acc + (mapping._1 -> mapping._2.ident)
    }
  }

  def instantiate(inst : InstanceDecl) = {
    val targetMod = modules.find(m => m.id == inst.moduleId).get
    val nameProvider = new ContextualNameProvider(ScopeMap.empty + module, "$inst:" + inst.instanceId.toString)
    
    val idMap0 : VarMap = Map.empty
    // map each input
    val idMap1 = targetMod.inputs.foldLeft(idMap0) {
      (mapAcc, inp) => {
        inst.argMap.get(inp.id) match {
          case Some(expr) =>  mapAcc + (inp.id -> BoundInput(nameProvider(inp.id, "bound_input"), expr))
          case None => mapAcc + (inp.id -> UnboundInput(nameProvider(inp.id, "unbound_input"))) 
        }
      }
    }
    // map each output
    val idMap2 = targetMod.outputs.foldLeft(idMap1) {
      (mapAcc, out) => {
        inst.argMap.get(out.id) match {
          case Some(expr) => mapAcc + (out.id -> Output(extractId(expr).get))
          case None => mapAcc + (out.id -> Output(nameProvider(out.id, "unbound_output")))
        }
      }
    }
    // map each state variable.
    val idMap3 = targetMod.vars.foldLeft(idMap2) {
      (mapAcc, v) => mapAcc + (v.id -> StateVariable(nameProvider(v.id, "var")))
    }
    
    val varMap = idMap3
    val rewriteMap = toRewriteMap(varMap)
    val rewriter = new ExprRewriter("ModuleInstantiator:" + inst.instanceId.toString, rewriteMap)
    val targetModP = rewriter.visit(targetMod)
    
    println("rewriteMap: " + rewriteMap.toString)
    println("******** TARGET MODULE *******")
    println(targetModP.get)
    println("***** END TARGET MODULE ******")
  }
  
  override def rewriteInstance(inst : InstanceDecl, ctx : ScopeMap) : Option[InstanceDecl] = {
    instantiate(inst)
    Some(inst)
  }
}

class ModuleInstantiator(modules : List[Module], moduleName : Identifier) extends ASTRewriter(
    "ModuleInstantiator", new ModuleInstantiatorPass(modules, moduleName))