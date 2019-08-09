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
 * ProcedureChecker
 *  If a procedure has pre/post conditions
 *    - it should not write to a variable that has not been declared modified.
 *    - only state variables should be declared modifiable
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger

class ProcedureCheckerPass extends ReadOnlyPass[Set[ModuleError]]
{
  val logger = Logger(classOf[ProcedureCheckerPass])

  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass

  def checkIdent(proc : ProcedureDecl, id : Identifier, pos : ASTPosition, context : Scope, in : T) : T = {
    logger.debug("Checking identifier: {}", id.toString())
    // At this point we should not have any ModifiableInstanceIds
    lazy val modifyIds = proc.modifies.asInstanceOf[Set[ModifiableId]].map(m => m.id)
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _) | Scope.OutputVar(_, _) | Scope.Instance(_) =>
            if (!modifyIds.contains(id)) {
              val error = ModuleError("Identifier was not declared modifiable: %s".format(id.toString), pos)
              in + error
            } else { in }
          case _ => in
        }
      case None =>
        val error = ModuleError("Unknown identifier was declared modifiable: %s".format(id.toString()), pos)
        in + error
    }
  }

  override def applyOnLHS(d : TraversalDirection.T, lhs : Lhs, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      context.procedure match {
        case Some(proc) =>
          checkIdent(proc, lhs.ident, lhs.ident.position, context, in)
        case None => in
      }
    } else { in }
  }

  override def applyOnProcedureCall(d : TraversalDirection.T, call : ProcedureCallStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      context.procedure match {
        case Some(proc) =>
          call.instanceId match {
            case Some(iid) => {
              val instOption = context.module.get.instances.find(inst => inst.instanceId == iid)
              val instMod = context.get(instOption.get.moduleId).get.asInstanceOf[Scope.ModuleDefinition].mod
              val calledProc = instMod.procedures.find((p) => p.id == call.id).get
              checkIdent(proc, instOption.get.instanceId, call.position, context, in)
            }
            case _ => {
              val calledProc = context.module.get.procedures.find(p => p.id == call.id).get
              // At this point we should not have any ModifiableInstanceIds
              val modifyIds = calledProc.modifies.asInstanceOf[Set[ModifiableId]].map(m => m.id)
              modifyIds.foldLeft(in)((acc, id) => checkIdent(proc, id, call.position, context, acc))
            }
          }
        case None =>
          in
      }
    } else {
      in
    }
  }
  override def applyOnHavoc(d : TraversalDirection.T, havocStmt : HavocStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      context.procedure match {
        case Some(proc) =>
          havocStmt.havocable match {
            case HavocableId(id) =>
              checkIdent(proc, id, id.position, context, in)
            case HavocableNextId(id) =>
              throw new Utils.AssertionError("Should not have havocable next ids inside procedures.")
            case HavocableFreshLit(f) =>
              in
          }
        case None => in
      }
    } else { in }
  }

  override def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      // At this point we should not have any ModifiableInstanceId
      val modifyIds : Set[Identifier]  = proc.modifies.asInstanceOf[Set[ModifiableId]].map(m => m.id) 
      val badVariables = modifyIds.filter {
        (v) => {
          context.get(v) match {
            case Some(namedExpr) =>
              namedExpr match {
                case Scope.StateVar(_, _)  |
                     Scope.OutputVar(_, _) |
                     Scope.SharedVar(_, _) => false
                case Scope.Instance(_) => {
                  val hasInstProcCall = proc.body.asInstanceOf[BlockStmt].stmts.find(stmt => stmt match {
                    case ProcedureCallStmt(id, callLhss, args, instanceId, moduleId) => (instanceId == v)
                    case _ => false
                  })
                  !hasInstProcCall.isEmpty
                }
                case _ => true
              }
            case None => {
              true
            }
          }
        }
      }
      val errors = badVariables.map {
        (v) => ModuleError("Identifier cannot be declared modifiable: %s".format(v.toString), v.position)
      }.toSet
      errors ++ in
    } else { in }
  }
}

class ProcedureChecker extends ASTAnalyzer("ProcedureChecker", new ProcedureCheckerPass())  {
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, Set.empty[ModuleError], context)
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}
