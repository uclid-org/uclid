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
 *
 * Inlines all procedure calls.
 *
 */

package uclid
package lang

import scala.collection.immutable.{Set => Set}
import scala.collection.mutable.ListBuffer
import com.typesafe.scalalogging.Logger


class FindProcedureDependencyPass extends ReadOnlyPass[Map[Identifier, Set[Identifier]]] {
  type T = Map[Identifier, Set[Identifier]]
  override def applyOnProcedureCall(d : TraversalDirection.T, proc : ProcedureCallStmt, in : T, context : Scope) : T = {
    def addEdge(caller : Identifier, callee : Identifier) : T = {
      in.get(caller) match {
        case Some(procedures) => in + (caller -> (procedures + callee))
        case None => in + (caller -> Set(callee))
      }
    }
    if (d == TraversalDirection.Down) {
      context.procedure match {
        case Some(currentProc) => addEdge(currentProc.id, proc.id)
        case None => addEdge(Identifier("_top"), proc.id)
      }
    } else { in }
  }
}

class FindProcedureDependency extends ASTAnalyzer("FindProcedureDependency", new FindProcedureDependencyPass())
{
  var procInliningOrder : List[Identifier] = List.empty

  override def visit(module : Module, context : Scope) : Option[Module] = {
    def recursionError(proc : Identifier, stack : List[Identifier]) : ModuleError = {
      val msg = "Recursion involving procedures: " + Utils.join(stack.map(_.toString).toList, ", ")
      ModuleError(msg, proc.position)
    }

    val procDepGraph = visitModule(module, Map.empty[Identifier, Set[Identifier]], context)
    val errors = Utils.findCyclicDependencies(procDepGraph, List(Identifier("_top")), recursionError)
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
    procInliningOrder = Utils.topoSort(List(Identifier("_top")), procDepGraph)
    Some(module)
  }
}

trait NewProcedureInlinerPass extends RewritePass {
  //def getProcedureCallStmts(stmt : Statement, collection : ListBuffer[ProcedureCallStmt]) : ListBuffer[ProcedureCallStmt] = {
  //  stmt match {
  //    case s : ProcedureCallStmt => collection += s
  //    case s : IfElseStmt => getProcedureCallStmts(s.elseblock, getProcedureCallStmts(s.ifblock, collection))
  //    case s : ForStmt => getProcedureCallStmts(s.body, collection)
  //    case s : WhileStmt => getProcedureCallStmts(s.body, collection)
  //    case s : BlockStmt => s.stmts.foldLeft(collection) { (c, s) => getProcedureCallStmts(s, c) }
  //    case s : CaseStmt => s.body.foldLeft(collection) { (c, tup) => getProcedureCallStmts(tup._2, c) }
  //    case _ => collection
  //  }
  //}

  //def getInstanceModifiesExprs(proc : ProcedureDecl, instId : Expr, buf : ListBuffer[Expr], context : Scope) : ListBuffer[Expr] = {
  // 
  //  var procCalls = getProcedureCallStmts(proc.body, new ListBuffer[ProcedureCallStmt])

  //  println("Printing initial procCalls")
  //  println(procCalls)
  //  while (!procCalls.isEmpty) {
  //    val call = procCalls.remove(0)
  //    if (call.instanceId != None) {
  //      //TODO: this needs to be nested properly if we are looking at nested instances
  //      val procInstOption = context.module.get.instances.find(inst => inst.instanceId == call.instanceId.get)
  //      val modId = procInstOption.get.moduleId
  //      if (context.get(modId) == None) {
  //        println("ModId is None")
  //        println(call)
  //        println(instId)
  //        println(procInstOption)
  //        println(modId)
  //      }
  //
  //      if (context.get(modId) != None) {
  //        val instMod = context.get(modId).get.asInstanceOf[Scope.ModuleDefinition].mod
  //        val modScope = Scope.empty + instMod 
  //        val instProc = instMod.procedures.find(p => p.id == call.id)
  //        val instIdMatch = instId match {
  //          case id : Identifier => 
  //            { call.instanceId.get == id }
  //          case OperatorApplication(SelectFromInstance(f), List(es)) =>
  //            { call.instanceId.get == f }
  //          case _  => 
  //            { 
  //              throw new Utils.ParserError("Instance Identifier: %s has an unknown form".format(instId), None, None)
  //              false
  //            }
  //        }
  //        if (instIdMatch) {
  //          instProc.get.modifies.filter(m => modScope.get(m) match {
  //            case Some(Scope.Instance(_)) => false
  //            case _ => true
  //          }).foreach(m => buf += OperatorApplication(SelectFromInstance(m), List(instId)))
  //        }
  //        // recursively add modifies set of sub-instances 
  //        instProc.get.modifies.filter(m => modScope.get(m) match {
  //          case Some(Scope.Instance(_)) => true
  //          case _ => false
  //        }).foreach(m => buf ++ getInstanceModifiesExprs(instProc.get, OperatorApplication(SelectFromInstance(m), List(instId)), ListBuffer.empty, modScope))
  //      }
  //    } else if (call.instanceId == None) {
  //      val procId = call.id
  //      val procOption = context.module.get.procedures.find(p => p.id == procId)
  //      getProcedureCallStmts(procOption.get.body, procCalls)
  //    }
  //  }
  //  buf 

  //}



  //def getInstanceModifies(proc : ProcedureDecl, instId : Identifier, buf : ListBuffer[(Identifier, Identifier)],  context : Scope) : ListBuffer[(Identifier, Identifier)] = {
  //  var procCalls = getProcedureCallStmts(proc.body, new ListBuffer[ProcedureCallStmt])

  //  while (!procCalls.isEmpty) {
  //    val call = procCalls.remove(0)
  //    if (call.instanceId != None) {
  //      val procInstOption = context.module.get.instances.find(inst => inst.instanceId == call.instanceId.get)
  //      val modId = procInstOption.get.moduleId
  //      val instMod = context.get(modId).get.asInstanceOf[Scope.ModuleDefinition].mod
  //      val modScope = Scope.empty + instMod 
  //      val instProc = instMod.procedures.find(p => p.id == call.id)
  //      if (call.instanceId.get == instId) {
  //        instProc.get.modifies.filter(m => modScope.get(m) match {
  //          case Some(Scope.Instance(_)) => false
  //          case _ => true
  //        }).foreach(m => buf += ((instId, m)))
  //      }

  //      //TODO: add other instances here
  //    } else if (call.instanceId == None) {
  //      val procId = call.id
  //      val procOption = context.module.get.procedures.find(p => p.id == procId)
  //      getProcedureCallStmts(procOption.get.body, procCalls)
  //    }
  //  }
  //  buf 
  //}
  
  def inlineProcedureCall(callStmt : ProcedureCallStmt, proc : ProcedureDecl, context : Scope) : Statement = {
    val procSig = proc.sig
    def getModifyLhs(id : Identifier) = {
      if (context.environment.isProcedural) { LhsId(id) }
      else { LhsNextId(id) }
    }

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
    val modifyPairs : List[(Identifier, Identifier)] = proc.modifies.filter(m =>  m match {
      case ModifiableId(id) => context.get(id) match {
                                 case Some(Scope.Instance(_)) => false
                                 case None => false
                                 case _ => true 
                                }
      case _ => false
    }).asInstanceOf[Set[ModifiableId]].map(m => (m.id, NameProvider.get("modifies_" + m.toString()))).toList


    // map from st_var -> modify_var.
    val modifiesMap : Map[Expr, Expr] = modifyPairs.map(p => (p._1 -> p._2)).toMap
    // full rewrite map.
    val rewriteMap = argMap ++ retMap ++ modifiesMap
    // rewriter object.
    val rewriter = new ExprRewriter("InlineRewriter", rewriteMap)

    // map from old(var) -> var.
    val oldMap : Map[Identifier, Identifier] = modifyPairs.map(p => p._2 -> p._1).toMap
    // Note that the map contains the 'modifies' name and the 'old' name
    val oldRenameMap : Map[Identifier, (Identifier, Identifier)] = modifyPairs.map(p => p._2 -> (p._1, NameProvider.get("old_" + p._2.toString()))).toMap
    // rewriter object
    val oldRewriter = new OldExprRewriter(oldRenameMap)
    
    val oldPairs : List[(Identifier, Identifier)] = oldRenameMap.toList.map(p => (p._1, p._2._2))

    // variable declarations for return values.
    val retVars = retPairs.map(r => BlockVarsDecl(List(r._2._1), r._2._2))
    // variable declarations for the modify variables.
    val modifyVars : List[BlockVarsDecl] = modifyPairs.map(p => BlockVarsDecl(List(p._2), context.get(p._1) match {
      case Some(v) => v.typ
      case _ => lang.UndefinedType()
    }))
    // variable declarations for old values
    val oldVars : List[BlockVarsDecl] = oldPairs.map(p => BlockVarsDecl(List(p._2), (context + modifyVars).get(p._1) match {
      case Some(v) => v.typ
      case _ => lang.UndefinedType()
    }))

    // list of all variable declarations.
    val varsToDeclare = retVars ++ modifyVars ++ oldVars

    // statements assigning state variables to modify vars.
    val modifyInitAssigns : List[AssignStmt] = modifyPairs.map(p => AssignStmt(List(LhsId(p._2)), List(p._1)))

    // create assign statements to keep track of old values
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

      //val instanceMods : Set[Identifier] = proc.modifies.filter(m => context.get(m) match {
      //  case Some(Scope.Instance(_)) => true 
      //  case _ => false 
      //})

      //var instanceIdMods : ListBuffer[(Identifier, Identifier)] = ListBuffer.empty
      //instanceMods.foldLeft(instanceIdMods) { (set, instId) => getInstanceModifies(proc, instId, set, context) }

      //var instIdModExprs : ListBuffer[Expr] = ListBuffer.empty
      //instanceMods.foldLeft(instIdModExprs) { (buf , instId) => getInstanceModifiesExprs(proc, instId, buf, context) }
      //println("InstanceIdModExprs here")
      //println(instIdModExprs)

      //val instanceHavocs : List[Statement] = instanceIdMods.map(m => HavocStmt(HavocableInstanceId(OperatorApplication(SelectFromInstance(m._2), List(m._1))))).toList
      BlockStmt(List.empty, modifyHavocs ++ postconditionAssumes)
    }
    val stmtsP = if (callStmt.callLhss.size > 0) {
      val returnAssign = AssignStmt(callStmt.callLhss, retIds)
      modifyInitAssigns ++ oldAssigns ++ preconditionAsserts ++ List(bodyP, returnAssign) ++ postconditionAsserts ++ modifyFinalAssigns
    } else {
      modifyInitAssigns ++ oldAssigns  ++ preconditionAsserts ++ List(bodyP) ++ postconditionAsserts ++ modifyFinalAssigns
    }
    BlockStmt(varsToDeclare, stmtsP)
  }

  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val instProcMap = module.procedures.foldLeft(Map.empty[List[Identifier], ProcedureDecl])((acc, proc) => acc + (List(module.id, proc.id) -> proc))
    val moduleP = module.withReplacedAnnotation[InstanceProcMapAnnotation](InstanceProcMapAnnotation(instProcMap))
    Some(moduleP)
  }
}

class NewInternalProcedureInlinerPass extends NewProcedureInlinerPass() {
  override def rewriteProcedureCall(callStmt : ProcedureCallStmt, context : Scope) : Option[Statement] = {
    val procId = callStmt.id
    val procOption = context.module.get.procedures.find(p => p.id == procId)
    //var modifiesInst = false;
    //if (!procOption.isEmpty) {
    //  modifiesInst = procOption.get.modifies.exists(
    //                      id => context.get(id) match {
    //                        case Some(Scope.Instance(_)) => true
    //                        case _ => false
    //                      })
    //}
    //if (!procOption.isEmpty && !procOption.get.body.hasInternalCall &&
    //                    (procOption.get.shouldInline || !modifiesInst)) {
    if (!procOption.isEmpty && !procOption.get.body.hasInternalCall) {
      Some(inlineProcedureCall(callStmt, procOption.get, context))
    } else {
      // Update the ProcedureCallStmt moduleId for external procedure inliner in module flattener
      callStmt.instanceId match {
        case Some(iid) => {
          val procInstOption = context.module.get.instances.find(inst => inst.instanceId.name == callStmt.instanceId.get.name)
          val modId = procInstOption.get.moduleId
          Some(ProcedureCallStmt(callStmt.id, callStmt.callLhss, callStmt.args, callStmt.instanceId, Some(modId)))
        }
        case None => Some(ProcedureCallStmt(callStmt.id, callStmt.callLhss, callStmt.args, callStmt.instanceId, None))
      }
    }
  }
}

class NewInternalProcedureInliner() extends ASTRewriter("InternalProcedureInliner", new NewInternalProcedureInlinerPass()) {
  override val repeatUntilNoChange = true
}
