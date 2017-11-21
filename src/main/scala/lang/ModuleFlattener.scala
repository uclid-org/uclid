/*
 * UCLID5 Verification and Synthesis Engine
 * 
 * Copyright (c) 2017. The Regents of the University of California (Regents). 
 * All Rights Reserved. 
 * 
 * Permission to use, copy, modify, and distribute this software
 * and its documentation for educational, research, and not-for-profit purposes,
 * without fee and without a signed licensing agreement, is hereby granted,
 * provided that the above copyright notice, this paragraph and the following two
 * paragraphs appear in all copies, modifications, and distributions. 
 * 
 * Contact The Office of Technology Licensing, UC Berkeley, 2150 Shattuck Avenue,
 * Suite 510, Berkeley, CA 94720-1620, (510) 643-7201, otl@berkeley.edu,
 * http://ipira.berkeley.edu/industry-info for commercial licensing opportunities.
 * 
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
 * INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING OUT OF
 * THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS
 * PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 * 
 * Author: Pramod Subramanyan

 * Module Instantiation.
 *
 */
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
  
  def checkInstance(inst : InstanceDecl, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    val targetModOption = moduleMap.get(inst.moduleId)
    targetModOption match {
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

  override def applyOnInstance(d : TraversalDirection.T, inst : InstanceDecl, in : List[ModuleError], context : Scope) : List[ModuleError] = {
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
  override def applyOnInstance(d : TraversalDirection.T, inst : InstanceDecl, in : T, context : Scope) : T = {
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
  var cyclicalDependency : Option[Boolean] = None
  override def reset() {
    in = Some(Map.empty[Identifier, Set[Identifier]])
  }
  def findCyclicDependencies(graph : Map[Identifier, Set[Identifier]], start : Identifier) : List[ModuleError] = {
    def visit(node : Identifier, stack : Set[Identifier], errorsIn : List[ModuleError]) : List[ModuleError] = {
      if (stack contains node) {
        val msg = "Cyclical dependency among modules: " + Utils.join(stack.map(_.toString).toList, ", ") + "."
        val error = ModuleError(msg, node.position)
        error :: errorsIn
      } else {
        graph.get(node) match {
          case Some(nodes) =>
            nodes.foldLeft(errorsIn)((acc, n) => visit(n, stack + node, acc))
          case None =>
            errorsIn
        }
      }
    }
    visit(start, Set.empty[Identifier], List.empty[ModuleError])
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
    val errors = findCyclicDependencies(depGraph, mainModuleName)
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
  }
}

object ModuleInstantiatorPass {
  sealed abstract class InstanceVarRenaming(val ident : Identifier, val typ : Type) 
  case class BoundInput(id : Identifier, t : Type, expr : Expr) extends InstanceVarRenaming(id, t)
  case class UnboundInput(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class BoundOutput(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class UnboundOutput(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class StateVariable(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class Constant(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class Function(id : Identifier, sig : FunctionSig) extends InstanceVarRenaming(id, sig.typ)
  type VarMap = Map[Identifier, InstanceVarRenaming]
  type RewriteMap = Map[Expr, Expr]

  // Convert an expression to an identifier. (if possible)
  def extractId (e : Expr) : Option[Identifier] = {
    e match {
      case id : Identifier => Some(id)
      case _ => None
    }
  }

  // Convert a RewriteMap into a VarMap
  def toRewriteMap(varMap : VarMap) : RewriteMap = {
    val empty : RewriteMap = Map.empty
    varMap.foldLeft(empty) { 
      (acc, mapping) => acc + (mapping._1 -> mapping._2.ident)
    }
  }
}

class ModuleInstantiatorPass(module : Module, inst : InstanceDecl, targetModule : Module) extends RewritePass {
  val MIP = ModuleInstantiatorPass
  type VarMap = MIP.VarMap
  type RewriteMap = MIP.RewriteMap

  def createVarMap() : VarMap = {
    // sanity check
    Utils.assert(targetModule.instances.size == 0, "All instances in target module must have been flattened by now!")

    val nameProvider = new ContextualNameProvider(Scope.empty + module, "$inst:" + inst.instanceId.toString)
    
    val idMap0 : VarMap = Map.empty
    // map each input
    val idMap1 = targetModule.inputs.foldLeft(idMap0) {
      (mapAcc, inp) => {
        inst.argMap.get(inp.id) match {
          case Some(expr) =>  mapAcc + (inp.id -> MIP.BoundInput(nameProvider(inp.id, "bound_input"), inp.typ, expr))
          case None => mapAcc + (inp.id -> MIP.UnboundInput(nameProvider(inp.id, "unbound_input"), inp.typ)) 
        }
      }
    }
    // map each output
    val idMap2 = targetModule.outputs.foldLeft(idMap1) {
      (mapAcc, out) => {
        inst.argMap.get(out.id) match {
          case Some(expr) => mapAcc + (out.id -> MIP.BoundOutput(MIP.extractId(expr).get, out.typ))
          case None => mapAcc + (out.id -> MIP.UnboundOutput(nameProvider(out.id, "unbound_output"), out.typ))
        }
      }
    }
    // map each state variable.
    val idMap3 = targetModule.vars.foldLeft(idMap2) {
      (mapAcc, v) => mapAcc + (v.id -> MIP.StateVariable(nameProvider(v.id, "var"), v.typ))
    }
    // map each constant.
    val idMap4 = targetModule.constants.foldLeft(idMap3) {
      (mapAcc, v) => mapAcc + (v.id -> MIP.Constant(nameProvider(v.id, "const"), v.typ))
    }
    // map each function.
    val idMap5 = targetModule.functions.foldLeft(idMap4) {
      (mapAcc, f) => mapAcc + (f.id -> MIP.Function(nameProvider(f.id, "function"), f.sig))
    }
    idMap5
  }

  def createNewModule(varMap : VarMap) : Module = {
    val rewriteMap = MIP.toRewriteMap(varMap)
    val rewriter = new ExprRewriter("MIP:" + inst.instanceId.toString, rewriteMap)
    rewriter.visit(targetModule, Scope.empty).get
  }

  def createNewVariables(varMap : VarMap) : List[Decl] = {
    varMap.map {
      v => {
        v._2 match {
          case MIP.BoundInput(id, t, _t) => Some(StateVarDecl(id, t))
          case MIP.UnboundOutput(id, t) => Some(StateVarDecl(id, t))
          case MIP.StateVariable(id, t) => Some(StateVarDecl(id, t))
          case MIP.Constant(id, t) => Some(ConstantDecl(id, t))
          case MIP.Function(id, sig) => Some(FunctionDecl(id, sig))
          case MIP.UnboundInput(_, _) | MIP.BoundOutput(_, _) => None
        }
      }
    }.toList.flatten
  }

  def createNewInputs(varMap : VarMap) : List[InputVarDecl] = {
    varMap.map {
      v => {
        v._2 match {
          case MIP.UnboundInput(id, t) => Some(InputVarDecl(id, t))
          case MIP.BoundInput(_, _, _) | MIP.BoundOutput(_, _) |
               MIP.UnboundOutput(_, _) | MIP.StateVariable(_, _) |
               MIP.Constant(_, _) | MIP.Function(_, _) =>
             None
        }
      }
    }.toList.flatten
  }

  def createInputAssignments(varMap : VarMap) : List[Statement] = {
    varMap.map {
      v => {
        v._2 match {
          case MIP.BoundInput(id, t, expr) =>
            Some(AssignStmt(List(LhsId(id)), List(expr)))
          case _ => 
            None
        }
      }
    }.toList.flatten
  }

  val varMap = createVarMap()
  val newModule = createNewModule(varMap)
  
  val newVariables = createNewVariables(varMap)
  val newInputs = createNewInputs(varMap)
  val newInputAssignments = createInputAssignments(varMap)
  val newNextStatements = newModule.next match {
    case Some(nextD) => nextD.body
    case _ => List.empty[Statement]
  }

  // rewrite SelectFromInstance operations.
  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    opapp.op match {
      case SelectFromInstance(field) =>
        val instance = opapp.operands(0)
        if (instance == inst.instanceId) {
          val fldP = varMap.get(field)
          Utils.assert(fldP.isDefined, "Non-existent field should have been detected by now!")
          Some(fldP.get.ident)
        } else {
          Some(opapp)
        }
      case _ => Some(opapp)
    }
  }
  // add initialization for the instance.
  override def rewriteInit(init : InitDecl, context : Scope) : Option[InitDecl] = {
    newModule.init match {
      case Some(initD) => Some(InitDecl(initD.body ++ init.body))
      case None => Some(init)
    }
  }

  // "delete" this instance.
  override def rewriteInstance(instD : InstanceDecl, context : Scope) : Option[InstanceDecl] = {
    if (instD == inst) {
      None
    } else {
      Some(instD)
    }
  }

  // add new variables and inputs.
  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    val declsP : List[Decl] = newVariables ++ newInputs ++ module.decls 
    val moduleP = Module(module.id, declsP, module.cmds)
    Some(moduleP)
  }

  // rewrite module.
  override def rewriteModuleCall(modCall : ModuleCallStmt, context : Scope) : List[Statement] = {
    newInputAssignments ++ newNextStatements
  }
}

class ModuleInstantiator(passName : String, module : Module, inst : InstanceDecl, targetModule : Module) extends ASTRewriter(
    passName, new ModuleInstantiatorPass(module, inst, targetModule))

class ModuleFlattenerPass(modules : List[Module], moduleName : Identifier) extends RewritePass {
  val MIP = ModuleInstantiatorPass
  type VarMap = MIP.VarMap
  type RewriteMap = MIP.RewriteMap

  val module = modules.find(_.id == moduleName).get

  def rewrite(module : Module) : Module = {
    module.instances match {
      case inst :: rest =>
        val targetModule = modules.find(_.id == inst.moduleId).get
        val passName = "ModuleInstantiator:" + module.id + ":" + inst.instanceId
        val rewriter = new ModuleInstantiator(passName, module, inst, targetModule)
        val modP = rewriter.visit(module, Scope.empty).get
        rewrite(modP)
      case Nil =>
        module
    }
  }
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val modP = rewrite(module)
    Some(modP)
  }
}

class ModuleFlattener(modules : List[Module], moduleName : Identifier) extends ASTRewriter(
    "ModuleFlattener", new ModuleFlattenerPass(modules, moduleName))