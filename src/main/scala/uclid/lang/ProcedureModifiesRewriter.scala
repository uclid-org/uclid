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
 * Author: Pranav Gaddamadugu
 *
 * Adds in write set of instance procedure calls.
 *
 */

package uclid
package lang

import scala.collection.immutable.{Set => Set}
// Vector class has faster operations
import scala.collection.immutable.Vector
import scala.collection.mutable.ListBuffer
import com.typesafe.scalalogging.Logger

/*
 * Rewrites a modify clause that refers to a specific instance as a modify 
 * clause that refers to all state variables of an instance modified by 
 * a procedure.
 */
class ProcedureModifiesRewriterPass extends RewritePass {
  
  /* 
   * Identifies the set of instances that are modified by some
   * procedure declaration.
   *
   * @param proc The ProcedureDeclaration to be analyzed
   * @param ctx Current scope
   * @returns Returns a set of identifiers for the modified instances.
   *
   */
  def getInstanceModifies(proc : ProcedureDecl, ctx : Scope) : Set[Identifier] = {
    // The associated scope must always contain a module
    val mod = ctx.module.get

    // If we are visiting this procedure, then 'modify instance statements' should not have been written in yet.
    val procModIds : Set[Identifier] = proc.modifies.flatMap(m => m match {
      case ModifiableId(id : Identifier) => Some(id)
      case _ => None
    })
    val instanceIds = procModIds.filter(id => mod.instances.contains(id))
    instanceIds
  }

  /*
   * Identifies the set of state variables modified by a procedure.
   *
   * @param proc The ProcedureDeclaration to be analyzed
   * @param ctx Current scope
   * @returns Returns a vector of identifiers.
   */
  def getStateVarModifies(proc : ProcedureDecl, ctx : Scope) : Vector[Identifier] = {
    // The associated scope must always contain a module
    val mod = ctx.module.get
    
    // If we are visiting this procedure, then 'modify instance id statements' should not have been written in yet.
    val procModIds : Vector[Identifier] = proc.modifies.flatMap(m => m match {
      case ModifiableId(id : Identifier) => Some(id)
      case _ => None
    }).toVector
    val stateVars = procModIds.filter(id => !mod.instances.map(decl => decl.instanceId).contains(id))
    stateVars
  }
    
  /*
   * Get all procedure call statements within some statement.
   *
   * @param stmt The statement being searched
   * @returns Returns a vector containing ProcedureCallStmts
   */
  def getProcedureCallStmts(stmt : Statement) : Vector[ProcedureCallStmt] = {
    stmt match {
      case s : ProcedureCallStmt => Vector(s)
      case s : IfElseStmt => getProcedureCallStmts(s.ifblock) ++ getProcedureCallStmts(s.elseblock)
      case s : ForStmt => getProcedureCallStmts(s.body)
      case s : WhileStmt => getProcedureCallStmts(s.body)
      case s : BlockStmt => s.stmts.foldLeft(Vector.empty[ProcedureCallStmt])((c, s) => c ++ getProcedureCallStmts(s))
      case s : CaseStmt => s.body.foldLeft(Vector.empty[ProcedureCallStmt])((c, tup) => c ++ getProcedureCallStmts(tup._2))
      case _ => Vector.empty[ProcedureCallStmt]
    }
  }

  //Note: Consider architecting this pass like ModuleFlattener
  //  - In order to do this we need find the ModuleDependency graph

  // proc : ProcedureDecl
  // instId : 
  //    -> None, if we are at the top level procedure
  //    -> Some(OperatorApplication), if are recursing into an instance
  //

  /*
   * This function identifies and returns the modifies set of a procedure. This
   * function also handles nested instance procedure calls
   *
   * @param proc The ProcedureDeclaration to be analyzed
   * @param instId An optional parameter that tells us if we shoud generate 
   *    ModifiableInstanceIds
   * @param ctx Current scope
   * @returns Returns the modifies set of a procedure, including specific
   *          instance state variables.
   */
  def getProcedureModSet(proc : ProcedureDecl, instId : Option[Expr],  ctx : Scope) : Vector[ModifiableEntity] = {
    
    // add in all modified state vars
    var modifySet : Vector[ModifiableEntity] = getStateVarModifies(proc, ctx).map(id => instId match {
      case Some(expr : Identifier) => ModifiableInstanceId(OperatorApplication(SelectFromInstance(id), List(expr)))
      case Some(expr : OperatorApplication) => ModifiableInstanceId(OperatorApplication(SelectFromInstance(id), List(expr)))
      case None => ModifiableId(id)
      case _ => throw new Utils.AssertionError("instId option cannot be anything else")
    })

    var procCallStmts = getProcedureCallStmts(proc.body)
    
    while (!procCallStmts.isEmpty) {
      val callStmt = procCallStmts.head
      procCallStmts = procCallStmts.tail
      if (callStmt.instanceId != None) {
        val instOption = ctx.module.get.instances.find(inst => inst.instanceId == callStmt.instanceId.get)
        val modId = instOption.get.moduleId
        // This should not fail since we have already type checked the modules
        val instMod = ctx.get(modId).get.asInstanceOf[Scope.ModuleDefinition].mod
        val modScope = new Scope(ctx.map, Some(instMod), ctx.procedure, ctx.cmd, ctx.environment, ctx.parent)
        val instProcDecl = modScope.module.get.procedures.find(p => p.id == callStmt.id)
        val newInstId : Option[Expr] = instId match {
          case Some(expr : Identifier) => Some(OperatorApplication(SelectFromInstance(callStmt.instanceId.get), List(expr)))
          case Some(expr : OperatorApplication) => Some(OperatorApplication(SelectFromInstance(callStmt.instanceId.get), List(expr)))
          case None => Some(callStmt.instanceId.get)
          case _ => throw new Utils.AssertionError("instId option cannot be anything else")
        }
        modifySet = modifySet ++ getProcedureModSet(instProcDecl.get, newInstId, modScope)
      } else {
        val procOption = ctx.module.get.procedures.find(p => p.id == callStmt.id)
        // This call should not fail since we have already done ProcedureTypeChecking
        modifySet = modifySet ++ getProcedureModSet(procOption.get, instId, ctx)
      }
    }
    modifySet
  }
  
  /* 
   * This function is the main driver for computing the specific modifies set
   * of any procedure call statement. It will create a new procedure with
   * the same declarations but an augmented modifies set.
   *
   * @param proc The procedure declaration that is being analyzed
   * @param ctx Current scope
   * @returns Returns a new procedure declaration, with its expanded 
   * modifies set.
   */
  override def rewriteProcedure(proc : ProcedureDecl, ctx : Scope) : Option[ProcedureDecl] = {
    val newModifySet = getProcedureModSet(proc, None, ctx).toSet
    Some(ProcedureDecl(proc.id, proc.sig, proc.body, proc.requires, proc.ensures, newModifySet, proc.annotations))
  }
}

class ProcedureModifiesRewriter extends ASTRewriter("ProcedureModifiesRewriter", new ProcedureModifiesRewriterPass())
