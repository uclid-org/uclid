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

class ModuleInstanceCheckerPass() extends ReadOnlyPass[List[ModuleError]] {
  def doesInstanceTypeMatch(modT : ModuleType, instT : ModuleInstanceType, in : List[ModuleError], pos : ASTPosition) : List[ModuleError] = {
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
                val msg = "Incorrect type for module " + argType + ": " + id.toString + ". Got " +
                          actualTyp.toString + ", expected " + expTyp.toString + " instead"
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

    // filter out shared variables.
    val wiredSharedVars = instT.args.filter((a) => modT.sharedVarMap.contains(a._1) && a._2.isDefined).map((a) => (a._1, a._2.get))
    val errs4 = checkTypes(wiredSharedVars, errs3, "sharedvar", modT.sharedVarMap)

    // ensure all shared variables are mapped.
    val unwiredSharedVars = modT.sharedVarMap.filter(v => !instT.argMap.contains(v._1))
    val unwiredSharedVarsErrors = unwiredSharedVars.map(v => ModuleError("Unmapped shared variable: " + v._1.toString, pos))
 
    errs4 ++ unwiredSharedVarsErrors
  }

  def checkInstance(inst : InstanceDecl, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    val targetModNamedExpr = context.map.get(inst.moduleId)
    targetModNamedExpr match {
      case None =>
        val error = ModuleError("Unknown module being instantiated: " + inst.moduleId.toString, inst.moduleId.position)
        error :: in
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.ModuleDefinition(targetMod) =>
            val targetModT = targetMod.moduleType
            Utils.assert(inst.instType.isDefined, "Instance type must be defined at this point!")
            val err1 = doesInstanceTypeMatch(targetModT, inst.instType.get, in, inst.position)
            // make sure all outputs are wired to identifiers.
            val outputExprs = inst.arguments.filter(a => targetModT.outputMap.contains(a._1) && a._2.isDefined).map(a => (a._2.get, "module output"))
            val sharedVarExprs = inst.arguments.filter(a => targetModT.sharedVarMap.contains(a._1) && a._2.isDefined).map(a => (a._2.get, "shared variable"))
            val identExprs = outputExprs ++ sharedVarExprs
            identExprs.foldLeft(err1) {
              (acc, arg) => {
                arg._1 match {
                  case Identifier(name) =>
                    acc
                  case _ =>
                    val msg = "Invalid %s : '%s'".format(arg._2.toString, arg._1.toString)
                    ModuleError(msg, arg._1.position) :: acc
                }
              }
            }
          case _ =>
            val error = ModuleError("Module not in scope: " + inst.moduleId.toString, inst.moduleId.position)
            error :: in
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

class ModuleInstanceChecker() extends ASTAnalyzer(
    "ModuleInstanceChecker", new ModuleInstanceCheckerPass())
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

class ModuleDependencyFinder(mainModuleName : Identifier) extends ASTAnalyzer(
    "ModuleDependencyFinder", new ModuleDependencyFinderPass())
{
  var moduleInstantiationOrder : Option[List[Identifier]] = None
  var cyclicalDependency : Option[Boolean] = None
  override def reset() {
    in = Some(Map.empty[Identifier, Set[Identifier]])
  }

  override def finish() {
    val depGraph = out.get
    val moduleInstantiationOrder = Some(Utils.topoSort(List(mainModuleName), depGraph))
    def cyclicModuleError(node : Identifier, stack : List[Identifier]) : ModuleError = {
      val msg = "Cyclical dependency among modules: " + Utils.join(stack.map(_.toString).toList, ", ") + "."
      ModuleError(msg, node.position)
    }
    val errors = Utils.findCyclicDependencies(depGraph, List(mainModuleName), cyclicModuleError)
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
  case class SharedVariable(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
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

class ModuleInstantiatorPass(module : Module, inst : InstanceDecl, targetModule : Module, initExternalSymbolMap : ExternalSymbolMap) extends RewritePass {
  val MIP = ModuleInstantiatorPass
  val targetModuleName = targetModule.id

  type VarMap = MIP.VarMap
  type RewriteMap = MIP.RewriteMap

  def createVarMap() : (VarMap, ExternalSymbolMap) = {
    // sanity check
    Utils.assert(targetModule.instances.size == 0, "All instances in target module must have been flattened by now. Module: %s. Instance: %s.\n%s".format(module.id.toString, inst.toString, targetModule.toString))
    val nameProvider = new ContextualNameProvider(Scope.empty + module, "$inst:" + inst.instanceId.toString)

    val idMap0 : VarMap = Map.empty
    // map each input
    val idMap1 = targetModule.inputs.foldLeft(idMap0) {
      (mapAcc, inp) => {
        inst.argMap.get(inp._1) match {
          case Some(expr) =>  mapAcc + (inp._1 -> MIP.BoundInput(nameProvider(inp._1, "bound_input"), inp._2, expr))
          case None => mapAcc + (inp._1 -> MIP.UnboundInput(nameProvider(inp._1, "unbound_input"), inp._2))
        }
      }
    }
    // map each output
    val idMap2 = targetModule.outputs.foldLeft(idMap1) {
      (mapAcc, out) => {
        inst.argMap.get(out._1) match {
          case Some(expr) => mapAcc + (out._1 -> MIP.BoundOutput(MIP.extractId(expr).get, out._2))
          case None => mapAcc + (out._1 -> MIP.UnboundOutput(nameProvider(out._1, "unbound_output"), out._2))
        }
      }
    }
    // map each shared variable
    val idMap3 = targetModule.sharedVars.foldLeft(idMap2) {
      (mapAcc, sharedVar) => {
        val mapping = inst.argMap.get(sharedVar._1)
        Utils.assert(mapping.isDefined, "All shared variables must be mapped.")
        val origVar = MIP.extractId(mapping.get).get
        mapAcc + (sharedVar._1 -> MIP.SharedVariable(origVar, sharedVar._2))
      }
    }
    // map each state variable.
    val idMap4 = targetModule.vars.foldLeft(idMap3) {
      (mapAcc, v) => mapAcc + (v._1 -> MIP.StateVariable(nameProvider(v._1, "var"), v._2))
    }
    // map each constant.
    val map5 = targetModule.constants.foldLeft((idMap4, initExternalSymbolMap)) {
      (acc, c) => {
        val (extSymMapP, newName) = acc._2.getOrAdd(ExternalIdentifier(targetModuleName, c._1), ConstantsDecl(List(c._1), c._2))
        (acc._1 + (c._1 -> MIP.Constant(newName, c._2)), extSymMapP)
      }
    }
    // map each function.
    val map6 = targetModule.functions.foldLeft(map5) {
      (acc, f) => {
        val (extSymMapP, newName) = acc._2.getOrAdd(ExternalIdentifier(targetModuleName, f.id), f)
        (acc._1 + (f.id -> MIP.Function(newName, f.sig)), extSymMapP)
      }
    }
    map6
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
          case MIP.BoundInput(id, t, _t) => Some(StateVarsDecl(List(id), t))
          case MIP.UnboundOutput(id, t) => Some(StateVarsDecl(List(id), t))
          case MIP.StateVariable(id, t) => Some(StateVarsDecl(List(id), t))
          case MIP.Constant(_, _) | MIP.Function(_, _) | MIP.UnboundInput(_, _) | 
               MIP.BoundOutput(_, _) | MIP.SharedVariable(_, _) =>  None
        }
      }
    }.toList.flatten
  }

  def createNewInputs(varMap : VarMap) : List[InputVarsDecl] = {
    varMap.map {
      v => {
        v._2 match {
          case MIP.UnboundInput(id, t) => Some(InputVarsDecl(List(id), t))
          case MIP.BoundInput(_, _, _) | MIP.BoundOutput(_, _) |
               MIP.UnboundOutput(_, _) | MIP.StateVariable(_, _) |
               MIP.SharedVariable(_, _) | MIP.Constant(_, _) | MIP.Function(_, _) =>
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

  val (varMap, externalSymbolMap) = createVarMap()
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
          if (fldP.isEmpty && context.cmd.isDefined) {
            Some(opapp)
          } else { 
            Utils.assert(fldP.isDefined, "Non-existent field should have been detected by now!")
            Some(fldP.get.ident)
          }
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
    if (modCall.id == inst.instanceId) {
      newInputAssignments ++ newNextStatements
    } else {
      List(modCall)
    }
  }
}

class ModuleInstantiator(passName : String, module : Module, inst : InstanceDecl, targetModule : Module, externalSymbolMap : ExternalSymbolMap) extends ASTRewriter(
    passName, new ModuleInstantiatorPass(module, inst, targetModule, externalSymbolMap))

class ModuleFlattenerPass(mainModule : Identifier) extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val externalSymbolAnalysis = manager.pass("ExternalSymbolAnalysis").asInstanceOf[ExternalSymbolAnalysis]

  val MIP = ModuleInstantiatorPass
  type VarMap = MIP.VarMap
  type RewriteMap = MIP.RewriteMap

  var extSymMap : ExternalSymbolMap = null;
  def rewrite(module : Module, ctx : Scope) : Module = {
    module.instances match {
      case inst :: rest =>
        val targetModule = ctx.map.find(p => p._1 == inst.moduleId).get._2.asInstanceOf[Scope.ModuleDefinition].mod // modules.find(_.id == inst.moduleId).get
        val passName = "ModuleInstantiator:" + module.id + ":" + inst.instanceId
        val rewriter = new ModuleInstantiator(passName, module, inst, targetModule, extSymMap)
        // println("rewriting module:%s inst:%s targetModule:%s.".format(module.id.toString, inst.instanceId.toString, targetModule.id.toString))
        // update external symbolm map.
        extSymMap = rewriter.pass.asInstanceOf[ModuleInstantiatorPass].externalSymbolMap
        // println("original module:\n%s".format(module.toString))
        val modP = rewriter.visit(module, ctx).get
        // println("rewritten module:\n%s".format(modP.toString))
        rewrite(modP, ctx)
      case Nil =>
        if (module.id == mainModule) {
          val rewriter = new ExternalSymbolRewriter(extSymMap)
          rewriter.visit(module, ctx).get
        } else {
          module
        }
    }
  }

  override def reset() {
    extSymMap = externalSymbolAnalysis.out.get
  }
  override def rewriteModule(moduleIn : Module, ctx : Scope) : Option[Module] = {
    val modP = rewrite(moduleIn, ctx)
    Some(modP)
  }
}

class ModuleFlattener(mainModule : Identifier) extends ASTRewriter(
    "ModuleFlattener", new ModuleFlattenerPass(mainModule))