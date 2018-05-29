/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Pramod Subramanyan

 * Module Instantiation.
 *
 */
package uclid
package lang

import scala.collection.immutable.Map
import com.typesafe.scalalogging.Logger

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
  var cyclicalDependency : Option[Boolean] = None
  override def reset() {
    in = Some(Map.empty[Identifier, Set[Identifier]])
  }

  override def finish() {
    val depGraph = out.get
    def cyclicModuleError(node : Identifier, stack : List[Identifier]) : ModuleError = {
      val msg = "Cyclical dependency among modules: " + Utils.join(stack.map(_.toString).toList, ", ")
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
  case class BoundOutput(lhs : Lhs, t : Type) extends InstanceVarRenaming(lhs.ident, t)
  case class UnboundOutput(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class StateVariable(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class SharedVariable(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class Constant(id : Identifier, t : Type) extends InstanceVarRenaming(id, t)
  case class Function(id : Identifier, sig : FunctionSig) extends InstanceVarRenaming(id, sig.typ)
  type VarMap = Map[Identifier, InstanceVarRenaming]
  type InstVarMap = Map[List[Identifier], Identifier]
  type RewriteMap = Map[Expr, Expr]

  // Convert an expression to an Identifier (if possible).
  def extractId (e : Expr) : Option[Identifier] = {
    e match {
      case id : Identifier => Some(id)
      case _ => None
    }
  }
  // Convert an expression to an Lhs (if possible).
  def extractLhs (e : Expr) : Option[Lhs] = {
    e match {
      case Identifier(id) =>
        Some(LhsId(Identifier(id)))
      case OperatorApplication(GetNextValueOp(), List(Identifier(id))) =>
        Some(LhsNextId(Identifier(id)))
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
  lazy val logger = Logger(classOf[ModuleInstantiatorPass])
  val MIP = ModuleInstantiatorPass
  val targetModuleName = targetModule.id

  type VarMap = MIP.VarMap
  type InstVarMap = MIP.InstVarMap
  type RewriteMap = MIP.RewriteMap
  val nameProvider = new ContextualNameProvider(Scope.empty + module, "_inst_" + inst.instanceId.toString)

  def createVarMap() : (VarMap, ExternalSymbolMap) = {
    // sanity check
    Utils.assert(targetModule.instances.size == 0, "All instances in target module must have been flattened by now. Module: %s. Instance: %s.\n%s".format(module.id.toString, inst.toString, targetModule.toString))

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
          case Some(expr) => mapAcc + (out._1 -> MIP.BoundOutput(MIP.extractLhs(expr).get, out._2))
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
    val map5 = targetModule.constants.foldLeft((idMap4)) {
      (acc, c) => acc + (c._1 -> MIP.Constant(nameProvider(c._1, "const"), c._2))
    }
    // map each function.
    val map6 = targetModule.functions.foldLeft(map5, initExternalSymbolMap) {
      (acc, f) => {
        val (extSymMapP, newName) = acc._2.getOrAdd(ExternalIdentifier(targetModuleName, f.id), f)
        (acc._1 + (f.id -> MIP.Function(newName, f.sig)), extSymMapP)
      }
    }
    map6
  }

  def createInstVarMap(varMap : VarMap) : InstVarMap = {
    val instVarMap1 = varMap.foldLeft(Map.empty[List[Identifier], Identifier]) {
      (instVarMap, renaming) => {
        renaming._2 match {
          case MIP.BoundInput(_, _, _) | MIP.UnboundInput(_, _) |
               MIP.BoundOutput(_, _) | MIP.UnboundOutput(_, _)  |
               MIP.StateVariable(_, _) | MIP.SharedVariable(_, _) |
               MIP.Constant(_, _) =>
            instVarMap + (List(inst.instanceId, renaming._1) -> renaming._2.ident)
          case _ =>
            instVarMap
        }
      }
    }
    val initInstVarMap : InstVarMap = (targetModule.getAnnotation[InstanceVarMapAnnotation]()).get.iMap
    val instVarMap2 = (initInstVarMap.map {
      p => {
        val key1 = List(inst.instanceId, p._2)
        val result = instVarMap1.get(key1).get
        (inst.instanceId :: p._1) -> result
      }
    }).toMap
    val instVarMap = instVarMap1 ++ instVarMap2
    instVarMap
  }

  def createNewModule(varMap : VarMap) : Module = {
    val rewriteMap = MIP.toRewriteMap(varMap)
    val rewriter = new ExprRewriter("MIP:" + inst.instanceId.toString, rewriteMap)
    rewriter.visit(targetModule, Scope.empty).get
  }

  def fixPosition[T <: PositionedNode](node : Option[T], pos : ASTPosition) : Option[T] = {
    ASTNode.introducePos(true, true, node, pos)
  }
  def fixPosition[T <: PositionedNode](nodes : List[T], pos : ASTPosition) : List[T] = {
    ASTNode.introducePos(true, true, nodes, pos)
  }
  def createNewVariables(varMap : VarMap) : List[Decl] = {
    varMap.map {
      v => {
        v._2 match {
          case MIP.BoundInput(id, t, _t) => fixPosition(Some(StateVarsDecl(List(id), t)), id.position)
          case MIP.UnboundOutput(id, t) => fixPosition(Some(StateVarsDecl(List(id), t)), id.position)
          case MIP.StateVariable(id, t) => fixPosition(Some(StateVarsDecl(List(id), t)), id.position)
          case MIP.Constant(id, t) => fixPosition(Some(ConstantsDecl(List(id), t)), id.position)
          case MIP.Function(_, _) | MIP.UnboundInput(_, _) |
               MIP.BoundOutput(_, _) | MIP.SharedVariable(_, _) =>  None
        }
      }
    }.toList.flatten
  }

  def createNewInputs(varMap : VarMap) : List[InputVarsDecl] = {
    varMap.map {
      v => {
        v._2 match {
          case MIP.UnboundInput(id, t) => fixPosition(Some(InputVarsDecl(List(id), t)), id.position)
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
            fixPosition(Some(AssignStmt(List(LhsId(id)), List(expr))), id.position)
          case _ =>
            None
        }
      }
    }.toList.flatten
  }

  val (varMap, externalSymbolMap) = createVarMap()
  val instVarMap = createInstVarMap(varMap)
  val newModule = createNewModule(varMap)

  val newVariables = createNewVariables(varMap)
  val newInputs = createNewInputs(varMap)
  val newInputAssignments = createInputAssignments(varMap)
  val newAxioms = newModule.axioms.map {
    ax => {
      val idP = ax.id.flatMap(axId => Some(nameProvider(axId, "axiom")))
      AxiomDecl(idP, ax.expr)
    }
  }
  val newNextStatements = newModule.next match {
    case Some(nextD) => List(nextD.body)
    case _ => List.empty[Statement]
  }

  override def rewriteAnnotation(note : Annotation, context : Scope) : Option[Annotation] = {
    note match {
      case ivmNote : InstanceVarMapAnnotation => Some(InstanceVarMapAnnotation(ivmNote.iMap ++ instVarMap))
      case _ => Some(note)
    }
  }

  // rewrite SelectFromInstance operations.
  def flattenSelectFromInstance(expr : Expr) : List[Identifier] = {
    expr match {
      case OperatorApplication(SelectFromInstance(field), List(e)) =>
        flattenSelectFromInstance(e) ++ List(field)
      case id : Identifier =>
        List(id)
      case _ =>
        throw new Utils.AssertionError("Unexpected AST node: " + expr.toString())
    }
  }

  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    val opappP = opapp.op match {
      case SelectFromInstance(field) =>
        val flatList = flattenSelectFromInstance(opapp)
        instVarMap.get(flatList) match {
          case Some(id) => Some(id)
          case None => Some(opapp)
        }
      case _ => Some(opapp)
    }
    fixPosition(opappP, opapp.position)
  }
  // add initialization for the instance.
  override def rewriteInit(init : InitDecl, context : Scope) : Option[InitDecl] = {
    newModule.init match {
      case Some(initD) => Some(InitDecl(BlockStmt(List.empty, newInputAssignments ++ List(initD.body) ++ List(init.body))))
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
    logger.debug("axioms:\n{}", newAxioms.map("  " + _.toString()))
    val declsP : List[Decl] = newVariables ++ newInputs ++ newAxioms ++ module.decls
    val moduleP = Module(module.id, declsP, module.cmds, module.notes)
    Some(moduleP)
  }

  // rewrite module.
  override def rewriteModuleCall(modCall : ModuleCallStmt, context : Scope) : Option[Statement] = {
    if (modCall.id == inst.instanceId) {
      Some(BlockStmt(List.empty, newInputAssignments ++ newNextStatements))
    } else {
      Some(modCall)
    }
  }
}

class ModuleInstantiator(
    passName : String, module : Module, inst : InstanceDecl,
    targetModule : Module, externalSymbolMap : ExternalSymbolMap)
extends ASTRewriter(passName, new ModuleInstantiatorPass(module, inst, targetModule, externalSymbolMap), false, false)

class ModuleFlattenerPass(mainModule : Identifier) extends RewritePass {
  val logger = Logger(classOf[ModuleFlattenerPass])
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
        logger.debug("rewriting module:%s inst:%s targetModule:%s.".format(module.id.toString, inst.instanceId.toString, targetModule.id.toString))
        // update external symbol map.
        extSymMap = rewriter.pass.asInstanceOf[ModuleInstantiatorPass].externalSymbolMap
        logger.debug("original module:\n%s".format(module.toString))
        val modP = rewriter.visit(module, ctx).get
        logger.debug("rewritten module:\n%s".format(modP.toString))
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
