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

class ProcedureCheckerPass extends ReadOnlyPass[Set[ModuleError]]
{
  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass

  def checkIdent(proc : ProcedureDecl, id : Identifier, context : Scope, in : T) : T = {
    context.get(id).get match {
      case Scope.StateVar(_, _) | Scope.OutputVar(_, _) =>
        if (!proc.modifies.contains(id)) {
          val error = ModuleError("Identifier was not declared modifiable: %s".format(id.toString), id.position)
          in + error
        } else { in }
      case _ => in
    }
  }

  override def applyOnLHS(d : TraversalDirection.T, lhs : Lhs, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      context.procedure match {
        case Some(proc) =>
          checkIdent(proc, lhs.ident, context, in)
        case None => in
      }
    } else { in }
  }

  override def applyOnHavoc(d : TraversalDirection.T, havocStmt : HavocStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      context.procedure match {
        case Some(proc) =>
          checkIdent(proc, havocStmt.id, context, in)
        case None => in
      }
    } else { in }
  }

  override def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      val badVariables = proc.modifies.filter {
        (v) => {
          context.get(v) match {
            case Some(namedExpr) =>
              namedExpr match {
                case Scope.StateVar(_, _) | Scope.OutputVar(_, _) => false
                case _                    => true
              }
            case None => true
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
