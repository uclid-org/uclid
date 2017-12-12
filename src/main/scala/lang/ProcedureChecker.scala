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
 *
 * ProcedureChecker
 *  If a procedure has pre/post conditions
 *    - it should not write to a variable that has not been declared modified.
 *
 */
package uclid
package lang

class ProcedureCheckerPass extends ReadOnlyPass[Set[ModuleError]]
{
  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass

  def checkLhs(proc : ProcedureDecl, lhs : Lhs, context : Scope, in : T) : T = {
    context.get(lhs.ident).get match {
      case Scope.StateVar(_, _) =>
        if (!proc.modifies.contains(lhs.ident)) {
          val error = ModuleError("Assignment to variable not declared modifiable: %s.".format(lhs.ident.toString), lhs.position)
          in + error
        } else { in }
      case _ => in
    }
  }
  override def applyOnLHS(d : TraversalDirection.T, lhs : Lhs, in : T, context : Scope) : T = {
    context.procedure match {
      case Some(proc) =>
        if (proc.hasPrePost) {
          checkLhs(proc, lhs, context, in)
        } else {
          in
        }
      case None =>
        in
    }
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