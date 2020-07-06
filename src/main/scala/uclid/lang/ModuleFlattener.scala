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
 * Author: Pramod Subramanyan, Kevin Cheang, Pranav Gaddamadugu

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
  override def applyOnInstanceArray(d : TraversalDirection.T, inst : InstanceArrayDecl, in : T, context : Scope) : T = {
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
  def toRewriteMap(varMap : VarMap, instVarMap : InstVarMap) : RewriteMap = {
    val empty : RewriteMap = Map.empty
    val rewriteMap1 = varMap.foldLeft(empty) {
      (acc, mapping) => acc + (mapping._1 -> mapping._2.ident)
    }
    val rewriteMap2 = instVarMap.foldLeft(rewriteMap1) {
      (acc, mapping) => {
        rewriteMap1.exists(_._1 == mapping._1(1)) match {
          case true => acc                                    // don't replace any shared var mappings or shadowed variables from instances
          case false => acc + (mapping._1(1) -> mapping._2)
        } 
      }
    }
    rewriteMap2
  }
}

class ModuleInstantiatorPass(module : Module, inst : Either[InstanceDecl, InstanceArrayDecl], targetModule : Module, initExternalSymbolMap : ExternalSymbolMap) extends RewritePass {
  lazy val logger = Logger(classOf[ModuleInstantiatorPass])
  val MIP = ModuleInstantiatorPass
  val targetModuleName = targetModule.id

  type VarMap = MIP.VarMap
  type InstVarMap = MIP.InstVarMap
  type RewriteMap = MIP.RewriteMap
  val ctx = Scope.empty + module

  val instArgMap = inst match {
    case Left(i) => i.argMap
    case Right(i) => i.argMap
  }
  val instId = inst match {
    case Left(i) => i.instanceId
    case Right(i) => i.instanceId
  }

  def createVarMap() : (VarMap, ExternalSymbolMap) = {
    // sanity check
    Utils.assert(targetModule.instances.size == 0, "All instances in target module must have been flattened by now. Module: %s. Instance: %s.\n%s".format(module.id.toString, inst.toString, targetModule.toString))
    Utils.assert(targetModule.instanceArrays.size == 0, "All instance arrays in target module must have been flattened by now. Module: %s. Instance: %s.\n%s".format(module.id.toString, inst.toString, targetModule.toString))

    val idMap0 : VarMap = Map.empty
    // map each input

    val idMap1 = inst match {
      case Left(_) => {
        targetModule.inputs.foldLeft(idMap0) {
          (mapAcc, inp) => {
            instArgMap.get(inp._1) match {
              case Some(expr) =>  mapAcc + (inp._1 -> MIP.BoundInput(NameProvider.get(inp._1.toString + "_bound_input"), inp._2, expr))
              case None => mapAcc + (inp._1 -> MIP.UnboundInput(NameProvider.get(inp._1.toString + "_unbound_input"), inp._2))
            }
          }
        }
      }
      case Right(i) => {
        targetModule.inputs.foldLeft(idMap0) {
          (mapAcc, inp) => {
            instArgMap.get(inp._1) match {
              case Some(expr) =>  mapAcc + (inp._1 -> MIP.BoundInput(NameProvider.get(inp._1.toString + "_bound_input"), ArrayType(i.inTypes, inp._2), expr))
              case None => mapAcc + (inp._1 -> MIP.UnboundInput(NameProvider.get(inp._1.toString + "_unbound_input"), ArrayType(i.inTypes, inp._2)))
            }
          }
        }
      } 
    }

    // map each output
    val idMap2 = inst match {
      case Left(_) => {
        targetModule.outputs.foldLeft(idMap1) {
          (mapAcc, out) => {
            instArgMap.get(out._1) match {
              case Some(expr) => mapAcc + (out._1 -> MIP.BoundOutput(MIP.extractLhs(expr).get, out._2))
              case None => mapAcc + (out._1 -> MIP.UnboundOutput(NameProvider.get(out._1.toString() + "_unbound_output"), out._2))
            }
          }
        }
      }
      case Right(i) => {
        targetModule.outputs.foldLeft(idMap1) {
          (mapAcc, out) => {
            instArgMap.get(out._1) match {
              case Some(expr) => mapAcc + (out._1 -> MIP.BoundOutput(MIP.extractLhs(expr).get, ArrayType(i.inTypes, out._2)))
              case None => mapAcc + (out._1 -> MIP.UnboundOutput(NameProvider.get(out._1.toString() + "_unbound_output"), ArrayType(i.inTypes, out._2)))
            }
          }
        }
      } 
    }

    // map each shared variable
    val idMap3 = inst match {
      case Left(_) => {
        targetModule.sharedVars.foldLeft(idMap2) {
          (mapAcc, sharedVar) => {
            val mapping = instArgMap.get(sharedVar._1)
            Utils.assert(mapping.isDefined, "All shared variables must be mapped.")
            val origVar = MIP.extractId(mapping.get).get
            mapAcc + (sharedVar._1 -> MIP.SharedVariable(origVar, sharedVar._2))
          }
        }
      }
      case Right(i) => {
        targetModule.sharedVars.foldLeft(idMap2) {
          (mapAcc, sharedVar) => {
            val mapping = instArgMap.get(sharedVar._1)
            Utils.assert(mapping.isDefined, "All shared variables must be mapped.")
            val origVar = MIP.extractId(mapping.get).get
            mapAcc + (sharedVar._1 -> MIP.SharedVariable(origVar, ArrayType(i.inTypes, sharedVar._2)))
          }
        }
      } 
    }

    // map each state variable.
    val idMap4 = inst match {
      case Left(_) => {
        targetModule.vars.foldLeft(idMap3) {
          (mapAcc, v) => {
            mapAcc + (v._1 -> MIP.StateVariable(NameProvider.get(v._1.toString() + "_var"), v._2))
          }
        }
      }
      case Right(i) => {
        targetModule.vars.foldLeft(idMap3) {
          (mapAcc, v) => {
            mapAcc + (v._1 -> MIP.StateVariable(NameProvider.get(v._1.toString() + "_var"), ArrayType(i.inTypes, v._2)))
          }
        }
      }
    } 
    // map each constant.
    val map5 = inst match {
      case Left(_) => {
        targetModule.constants.foldLeft((idMap4)) {
          (acc, c) => {
            acc + (c._1 -> MIP.Constant(NameProvider.get(c._1.toString() + "_const"), c._2))
          }
        }
      }
      case Right(i) => {
        targetModule.constants.foldLeft((idMap4)) {
          (acc, c) => {
            acc + (c._1 -> MIP.Constant(NameProvider.get(c._1.toString() + "_const"), ArrayType(i.inTypes, c._2)))
          }
        }
      }
    }
    // map each function.
    val map6 = targetModule.functions.foldLeft(map5, initExternalSymbolMap) {
      (acc, f) => {
        val (extSymMapP, newName) = acc._2.getOrAdd(ExternalIdentifier(targetModuleName, f.id), f, ctx)
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
            instVarMap + (List(instId, renaming._1) -> renaming._2.ident)
          case _ =>
            instVarMap
        }
      }
    }
    val initInstVarMap : InstVarMap = (targetModule.getAnnotation[InstanceVarMapAnnotation]()).get.iMap
    val instVarMap2 = (initInstVarMap.map {
      p => {
        val key1 = List(instId, p._2)
        val result = instVarMap1.get(key1).get
        (instId :: p._1) -> result
      }
    }).toMap
    val instVarMap = instVarMap1 ++ instVarMap2
    instVarMap
  }

  def createNewModule() : Module = {
    // TODO: Generalize for instance arrays!
    inst match {
      case Left(i) => rewriter.visit(targetModule, Scope.empty).get
      case Right(i) =>
        val tmpRewriter = new ModuleInitGeneralizerRewriter("InlineAddIndxs", i.inTypes)
        tmpRewriter.visit(rewriter.visit(targetModule, Scope.empty).get, Scope.empty).get
    }
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
          case MIP.BoundInput(id, t, _) => fixPosition(Some(StateVarsDecl(List(id), t)), id.position)
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

  def createNextInputAssignments(varMap : VarMap) : List[Statement] = {
    varMap.map {
      v => {
        v._2 match {
          case MIP.BoundInput(id, _, expr) =>
            fixPosition(Some(AssignStmt(List(LhsId(id)), List(expr))), id.position)
          case _ =>
            None
        }
      }
    }.toList.flatten
  }

  val (varMap, externalSymbolMap) = createVarMap()
  val targetInstVarMap = targetModule.getAnnotation[InstanceVarMapAnnotation].get.iMap

  val rewriteMap = MIP.toRewriteMap(varMap, targetInstVarMap)
  val rewriter = new ExprRewriter("MIP:" + instId.toString, rewriteMap)

  val instVarMap = createInstVarMap(varMap)
  val newModule = createNewModule()

  val newVariables = createNewVariables(varMap)
  val newInputs = createNewInputs(varMap)
  val newInputAssignments = createNextInputAssignments(varMap)
  val newAxioms = newModule.axioms.map {
    ax => {
      val idP = ax.id.flatMap(axId => Some(NameProvider.get(axId.toString() + "_axiom")))
      AxiomDecl(idP, ax.expr, ax.params)
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
      case OperatorApplication(SelectFromInstance(field), List(OperatorApplication(ArraySelect(idx), List(Identifier(e))))) => 
        List(Identifier(e)) ++ List(field)
      case OperatorApplication(SelectFromInstance(field), List(e)) =>
        flattenSelectFromInstance(e) ++ List(field)
      case id : Identifier =>
        List(id)
      case _ =>
        throw new Utils.AssertionError("Unexpected AST node: " + expr.toString())
    }
  }

  // rewrite a list of identifiers as a nested select from instance
  def unflattenSelectFromInstance(ids : List[Identifier]) : OperatorApplication = {
    if (ids.length == 2) {
      return OperatorApplication(SelectFromInstance(ids.last), List(ids.head))
    } else {
      return OperatorApplication(SelectFromInstance(ids.last), List(unflattenSelectFromInstance(ids.init)))
    }
  }

  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    val opappP = opapp match {
      case OperatorApplication(SelectFromInstance(_), List(OperatorApplication(ArraySelect(idx), List(Identifier(e))))) =>
        val flatList = flattenSelectFromInstance(opapp)
        instVarMap.get(flatList) match {
          case Some(id) => 
            Some(OperatorApplication(ArraySelect(idx), List(id)))
          case None => 
            Some(opapp)
        }
      case OperatorApplication(SelectFromInstance(_), _) =>
        val flatList = flattenSelectFromInstance(opapp)
        instVarMap.get(flatList) match {
          case Some(id) => 
            Some(id)
          case None => 
            Some(opapp)
        }
      case _ => 
        Some(opapp)
    }
    fixPosition(opappP, opapp.position)
  }

  
  /*
   * Rewrites havoc statements into the appropriate form. Reduces 
   * HavocableInstanceIds into HavocableIds by retrieving the appropriate 
   * instance state variable.
   *
   * @param st The havoc statement that we are rewriting
   * @param ctx The current scope
   * @returns Returns a HavocStmt.
   */
  override def rewriteHavoc(st : HavocStmt, ctx : Scope) : Option[Statement] = {
    st.havocable match {
      case HavocableInstanceId(opapp) => {
        val newOppApp = rewriteOperatorApp(opapp, ctx).get
        if (newOppApp.isInstanceOf[Identifier]) {
          Some(HavocStmt(HavocableId(newOppApp.asInstanceOf[Identifier])))
        } else if (newOppApp.isInstanceOf[OperatorApplication]) {
          Some(HavocStmt(HavocableInstanceId(newOppApp.asInstanceOf[OperatorApplication])))
        } else {
          throw new Utils.AssertionError("HavocInstanceId should not be rewritten in any other form")
        }
      }
      case _ => Some(st)
    }
  }

  // add initialization for the instance.
  override def rewriteInit(init : InitDecl, context : Scope) : Option[InitDecl] = {
    newModule.init match {
      case Some(initD) => Some(InitDecl(BlockStmt(List.empty, newInputAssignments ++ List(initD.body) ++ List(init.body))))
      case None => Some(init)
    }
  }

  // "delete" this instance.
  override def rewriteInstanceOrInstanceArray(instD : Either[InstanceDecl, InstanceArrayDecl], context : Scope) : Option[Either[InstanceDecl, InstanceArrayDecl]] = {
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
    if (modCall.id == instId) {
      Some(BlockStmt(List.empty, newInputAssignments ++ newNextStatements))
    } else {
      Some(modCall)
    }
  }
  // rewrite module array.
  override def rewriteModuleArrayCall(modCall : ModuleArrayCallStmt, context : Scope) : Option[Statement] = {
    if (modCall.id == instId) {
      val idxmap : Map[Expr, Expr] = instVarMap.map({ case (a, b) => b -> OperatorApplication(ArraySelect(List(modCall.expr)), List(b))})
      val tmprewriter = new ModuleNextGeneralizerRewriter("InlineAddIndxs", modCall.expr, idxmap)
      val newins = tmprewriter.rewriteStatements(newInputAssignments, context)
      val newnexts = tmprewriter.rewriteStatements(newNextStatements, context)
      Some(BlockStmt(List.empty, newins ++ newnexts))
    } else {
      Some(modCall)
    }
  }

  /*
   * Inlines procedure calls that either depend on an instance procedure call,
   * or those that have not been inlined in ProcedureInline. This handles
   * procedures that are 'noinlined'.
   *
   * @param callStmt The procedure call statement to be inlined
   * @param proc The procedure declaration corresponding to callStmt
   * @param context The current scope
   * @returns Returns a new BlockStmt containing the inlined procedure.
   */
  def inlineProcedureCall(callStmt : ProcedureCallStmt, proc : ProcedureDecl, context : Scope) : Statement = {
    val procSig = proc.sig
    def getModifyLhs(id : Identifier) = LhsId(id)

    // formal and actual argument pairs.
    val argPairs : List[(Identifier, Expr)] = ((procSig.inParams.map(p => p._1)) zip (callStmt.args))
    // formal and actual return value pairs.
    val retPairs : List[(Identifier, (Identifier, Type))] = procSig.outParams.map(p => (p._1 -> (NameProvider.get("ret_" + p._1.toString()), p._2)))
    // list of new return variables.
    val retIds = retPairs.map(r => r._2._1)
    // map from formal to actual arguments.
    val argMap : Map[Expr, Expr] = argPairs.map(p => p._1.asInstanceOf[Expr] -> p._2).toMap
    // map from formal to the fake variables created for return values.
    val retMap : Map[Expr, Expr] = retPairs.map(p => p._1.asInstanceOf[Expr] -> p._2._1).toMap
    // map from modified state variables to new variables created for them. ignore modified "instances"
    // should only use modify exprs that contain a ModifiableId
    val modifyRenameList: List[(ModifiableEntity, Identifier)] = proc.modifies.filter(m =>  m match {
      case ModifiableId(id) => context.get(id) match {
                                 case Some(Scope.Instance(_)) | Some(Scope.InstanceArray(_)) => false
                                 case None => false // Instance already flattened
                                 case _ => true
                                }
      case ModifiableInstanceId(_)  => true
    }).flatMap(m => m match {
      case ModifiableId(id) => Some((m, NameProvider.get("modifies_" + id.toString())))
      case ModifiableInstanceId(opapp) => {
        instVarMap.get(flattenSelectFromInstance(opapp)) match {
          case Some(name) => Some((m, NameProvider.get("modifies_" + name)))
          // Not in the current instance we are flattening
          case _ => None 
        }
      }
    }).toList

    /*  
     * For each variable that is modified, get the appropriate renamed identifier.
     */
     val modifyPairs : List[(Identifier, Identifier)] = modifyRenameList.flatMap(p => p._1 match {
      case ModifiableId(id) => Some((id, p._2))
      case ModifiableInstanceId(opapp) => {
        instVarMap.get(flattenSelectFromInstance(opapp)) match {
          case Some(name) => Some((name, p._2))
          case _ => None
        }
      }
    })

    val notModifiesMap : Map[Expr, Expr] = if (callStmt.instanceId == None) {
        val flattenedModifiedInstanceIds : Set[List[Identifier]] = proc.modifies.filter(p => p.isInstanceOf[ModifiableInstanceId]).map(p => flattenSelectFromInstance(p.expr))
        instVarMap.filterKeys(k => !flattenedModifiedInstanceIds.contains(k)).map(p => (unflattenSelectFromInstance(p._1) -> p._2))
      } else {
        val modifiedIds : Set[Identifier] = proc.modifies.filter(p => p.isInstanceOf[ModifiableId]).map(p => p.asInstanceOf[ModifiableId].id)
        varMap.filter(p => !modifiedIds.contains(p._1) && p._2.isInstanceOf[MIP.StateVariable]).map(p => (p._1 -> p._2.asInstanceOf[MIP.StateVariable].id))
      }
    

        
    // map from st_var -> modify_var.
    // Does not inclide instance state variables
    val modifiesMap : Map[Expr, Expr] = modifyRenameList.map(p => (p._1.expr -> p._2)).toMap

    // full rewrite map.
    val rewriteMap = argMap ++ retMap ++ modifiesMap ++ notModifiesMap
    // rewriter object.
    val rewriter = new ExprRewriter("InlineRewriter", rewriteMap)
    
    // Note that oldRenameMap contains the 'modifies' name and the 'old' name
    // example entry ['a', 'old_a')]
    val oldRenameMap : Map[ModifiableEntity, Identifier] = modifyRenameList.flatMap(p => p._1 match {
      case ModifiableId(id) =>  Some((p._1 -> NameProvider.get("old_" + id.toString())))
      case ModifiableInstanceId(opapp) => {
        instVarMap.get(flattenSelectFromInstance(opapp)) match {
          case Some(name) => Some((p._1 -> NameProvider.get("old_" + name)))
          // Shouldn't hit this case since we are taking this from modifyRenameList
          case _ => None
        }
      }
    }).toMap

    // We know that notModifiesMap is compatible with both modifiesId and modifiesInstanceId
    val notModifiesOldMap : Map[ModifiableEntity, Identifier] = notModifiesMap.flatMap(p => (p._1, p._2) match {
      case (o : OperatorApplication, id : Identifier) => Some((ModifiableInstanceId(o) -> id))
      case (id1 : Identifier, id2 : Identifier) => Some((ModifiableId(id1) -> id2))
      case _ => None
    })
    // rewriter object.
    val oldRewriter = new OldExprRewriter(oldRenameMap ++ notModifiesOldMap)

    val oldPairs : List[(Identifier, Identifier)] = oldRenameMap.flatMap(p => p._1 match {
      case ModifiableId(id) => Some((id, p._2))
      case ModifiableInstanceId(opapp) => {
        instVarMap.get(flattenSelectFromInstance(opapp)) match {
          case Some(name) => Some((name, p._2))
          // Shouldn't hit this case
          case _ => None
        }
      }
    }).toList

    // variable declarations for return values.
    val retVars = retPairs.map(r => BlockVarsDecl(List(r._2._1), r._2._2))
    // variable declarations for the modify variables.
    
    val modifyVars : List[BlockVarsDecl] = modifyPairs.map(p => BlockVarsDecl(List(p._2), context.get(p._1) match {
      case Some(v) => v.typ
      case _ => {
        val stateVarTypeMap : Map[Identifier, Type] = varMap.flatMap(p => p._2 match {
          case MIP.StateVariable(id, t) => Some(id -> t)
          case _ => None
        })
        val instTyp = stateVarTypeMap.get(p._1)
        if (instTyp != None) {
          instTyp.get
        } else {
          context.get(callStmt.moduleId.get).get.asInstanceOf[Scope.ModuleDefinition].mod.vars.find(v => v._1.name == p._1.name).get._2
        }
      }
    }))
    // variable declarations for old values
    val oldVars : List[BlockVarsDecl] = oldPairs.map(p => BlockVarsDecl(List(p._2), (context + modifyVars).get(p._1) match {
      case Some(v) => v.typ
      case _ => {
        val stateVarTypeMap : Map[Identifier, Type] = varMap.flatMap(p => p._2 match {
          case MIP.StateVariable(id, t) => Some(id -> t)
          case _ => None
        })
        val instTyp = stateVarTypeMap.get(p._1)
        if (instTyp != None) {
          instTyp.get
        } else {
          lang.UndefinedType()
        }
      }
    }))
    // list of all variable declarations.
    val varsToDeclare = retVars ++ modifyVars ++ oldVars

    // statements assigning state variables to modify vars.
    val modifyInitAssigns : List[AssignStmt] = modifyPairs.map(p => AssignStmt(List(LhsId(p._2)), List(p._1)))
    // statements tracking variables before procedure call
    val oldAssigns : List[AssignStmt] = oldPairs.map(p => AssignStmt(List(LhsId(p._2)), List(p._1)))
    // havoc'ing of the modified variables.
    val modifyHavocs : List[HavocStmt] = modifyPairs.map(p => HavocStmt(HavocableId(p._2)))
    // statements updating the state variables at the end.
    val modifyFinalAssigns : List[AssignStmt] = modifyPairs.map(p => AssignStmt(List(getModifyLhs(p._1)), List(p._2)))
    // create precondition asserts
    val preconditionAsserts : List[Statement] = proc.requires.map {
      (req) => {
        val exprP = oldRewriter.rewriteExpr(rewriter.rewriteExpr(req, context), context)
        val node = AssertStmt(exprP, Some(Identifier("precondition")))
        ASTNode.introducePos(true, true, node, req.position)
      }
    }
    // create postcondition asserts
    val postconditionAsserts : List[Statement] = if (proc.shouldInline) {
      proc.ensures.map {
        (ens) => {
          val exprP = oldRewriter.rewriteExpr(rewriter.rewriteExpr(ens, context), context)
          val node = AssertStmt(exprP, Some(Identifier("postcondition")))
        ASTNode.introducePos(true, true, node, ens.position)
        }
      }
    } else {
      List.empty
    }
    // body of the procedure.
    val bodyP = if (proc.shouldInline) {
      oldRewriter.rewriteStatement(rewriter.rewriteStatement(proc.body, Scope.empty).get, context).get
    } else {
      val postconditionAssumes : List[Statement] = proc.ensures.map {
        (ens) => {
          val exprP = oldRewriter.rewriteExpr(rewriter.rewriteExpr(ens, context), context)
          AssumeStmt(exprP, None)
        }
      }
      BlockStmt(List.empty, modifyHavocs ++ postconditionAssumes)
    }
    val stmtsP = if (callStmt.callLhss.size > 0) {
      val returnAssign = AssignStmt(callStmt.callLhss, retIds)
      modifyInitAssigns ++ oldAssigns ++ preconditionAsserts ++ List(bodyP, returnAssign) ++ postconditionAsserts ++ modifyFinalAssigns
    } else {
      modifyInitAssigns ++ oldAssigns ++ preconditionAsserts ++ List(bodyP) ++ postconditionAsserts ++ modifyFinalAssigns
    }
    BlockStmt(varsToDeclare, stmtsP)
  }

  /*
   * Rewrites procedure call statements. At this point, all procedure that do not modify any instances or should be inlined have been handled.
   *
   * @param callStmt The procedure call statement being analyzed
   * @param context The current scope
   * @returns Returns a BlockStmt containing the internals of the procedure call.
   */
  override def rewriteProcedureCall(callStmt : ProcedureCallStmt, context : Scope) : Option[Statement] = {
    // Handle any instance procedure call.
    if (callStmt.instanceId != None && callStmt.instanceId.get.name == instId.name) {
            // Replace the instance procedure call if we're flattening that particular instance    
      val procInst = context.module.get.instances.find(inst => instId.name == callStmt.instanceId.get.name).get
      val procModule = context.get(procInst.moduleId).get.asInstanceOf[Scope.ModuleDefinition].mod
      val procOption = procModule.procedures.find(p => p.id.name == callStmt.id.name)
      val blkStmt = inlineProcedureCall(callStmt, procOption.get, Scope.empty + procModule)
      rewriter.visitStatement(blkStmt, context)
    } else {
      val procOption = context.module.get.procedures.find(p => p.id == callStmt.id)
      var modifiesInst = false
      if (!procOption.isEmpty) {
        modifiesInst = procOption.get.modifies.exists(
                          modifiable => modifiable match {
                            case _ : ModifiableId => false
                            case _ : ModifiableInstanceId => true
                          })
        modifiesInst = true
      }
      
      // Handle noinlined procedures that modify instances 
      if (!procOption.isEmpty) {
        val blkStmt = inlineProcedureCall(callStmt, procOption.get, context)
        rewriter.visitStatement(blkStmt, context)
      } else {
        //TODO: Verify that this is not a reachable state
        Some(callStmt)
      }
    }
  }
}

class ModuleInstantiator(
    passName : String, module : Module, inst : Either[InstanceDecl, InstanceArrayDecl],
    targetModule : Module, externalSymbolMap : ExternalSymbolMap)
extends ASTRewriter(passName, new ModuleInstantiatorPass(module, inst, targetModule, externalSymbolMap), false, false) {

    /*
     * Overwrites inherited visitModifiableEntity method and flattens modify
     * clauses that refer to an instance state variable.
     *
     * @param modifiable The modifiable entity to be flattened
     * @returns A flattened modifiable entity.
     *
     */
    override def visitModifiableEntity(modifiable : ModifiableEntity, context : Scope) : Option[ModifiableEntity] = {
      val modifiableP = modifiable match {
        case ModifiableId(id) => {
          visitIdentifier(id, context).flatMap((idP) => {
            idP match {
              case id : Identifier =>
                pass.rewriteModifiableEntity(ModifiableId(id), context)
              case _ => 
                Some(modifiable)
            }
          })
        }
        case ModifiableInstanceId(opapp) => {
          opapp match {
            case OperatorApplication(SelectFromInstance(_), _) => {
              val flatName = pass.asInstanceOf[ModuleInstantiatorPass].flattenSelectFromInstance(opapp) 
              val newName = pass.asInstanceOf[ModuleInstantiatorPass].instVarMap.get(flatName)
              if (newName != None) {
                pass.rewriteModifiableEntity(ModifiableId(newName.get), context)
              } else {
                Some(modifiable)
              }
            }
            case _ =>
              None
          }
        }
      }
      return ASTNode.introducePos(true, true, modifiableP, modifiable.position)
    }
}

class ModuleFlattenerPass(mainModule : Identifier) extends RewritePass {
  val logger = Logger(classOf[ModuleFlattenerPass])
  lazy val manager : PassManager = analysis.manager
  lazy val externalSymbolAnalysis = manager.pass("ExternalSymbolAnalysis").asInstanceOf[ExternalSymbolAnalysis]

  val MIP = ModuleInstantiatorPass
  type VarMap = MIP.VarMap
  type RewriteMap = MIP.RewriteMap

  var extSymMap : ExternalSymbolMap = null;
  def rewrite(module : Module, ctx : Scope) : Module = {
    val instances : List[Either[InstanceDecl, InstanceArrayDecl]] = module.instances.map(i => Left(i)) ++ module.instanceArrays.map(a => Right(a))
    instances match {
      case Left(inst) :: _ =>
        val targetModule = ctx.map.find(p => p._1 == inst.moduleId).get._2.asInstanceOf[Scope.ModuleDefinition].mod // modules.find(_.id == inst.moduleId).get
        val passName = "ModuleInstantiator:" + module.id + ":" + inst.instanceId
        val rewriter = new ModuleInstantiator(passName, module, Left(inst), targetModule, extSymMap)
        logger.debug("rewriting module:%s inst:%s targetModule:%s.".format(module.id.toString, inst.instanceId.toString, targetModule.id.toString))
        // update external symbol map.
        extSymMap = rewriter.pass.asInstanceOf[ModuleInstantiatorPass].externalSymbolMap
        logger.debug("original module:\n%s".format(module.toString))
        val modP = rewriter.visit(module, ctx).get
        logger.debug("rewritten module:\n%s".format(modP.toString))
        rewrite(modP, ctx)
      case Right(inst) :: _ =>
        val targetModule = ctx.map.find(p => p._1 == inst.moduleId).get._2.asInstanceOf[Scope.ModuleDefinition].mod // modules.find(_.id == inst.moduleId).get
        val passName = "ModuleInstantiator:" + module.id + ":" + inst.instanceId
        val rewriter = new ModuleInstantiator(passName, module, Right(inst), targetModule, extSymMap)
        logger.debug("rewriting module array:%s inst:%s targetModule:%s.".format(module.id.toString, inst.instanceId.toString, targetModule.id.toString))
        // update external symbol map.
        extSymMap = rewriter.pass.asInstanceOf[ModuleInstantiatorPass].externalSymbolMap
        logger.debug("original module array:\n%s".format(module.toString))
        val modP = rewriter.visit(module, ctx).get
        logger.debug("rewritten module array:\n%s".format(modP.toString))
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


// Generalize module that will be used for instance array
class ModuleInitGeneralizerRewriterPass(inTypes : List[Type]) extends RewritePass
{

}

class ModuleInitGeneralizerRewriter(name: String, inTypes : List[Type])
  extends ASTRewriter(name, new ModuleInitGeneralizerRewriterPass(inTypes))
{
  override def visitType(typ: Type, context: Scope): Option[Type] = {
    Some(ArrayType(inTypes, typ))
  }
}

class ModuleNextGeneralizerRewriter(name: String, idx : Expr, rewrites : Map[Expr, Expr])
  extends ExprRewriter(name, rewrites)
{
  override def visitAssignStatement(st : AssignStmt, ctx : Scope) : Option[Statement] = {
    st match {
      case AssignStmt(List(x), List(y)) =>
        rewrites.get(x.ident) match {
          case Some(e) => Some(st)
          case None => 
            val update = rewriteExpr(OperatorApplication(ArrayUpdate(List(idx), y), List(x.ident)), ctx)
            Some(AssignStmt(List(x), List(update)))
        }
      case _ => Some(st)
    }
  }
}