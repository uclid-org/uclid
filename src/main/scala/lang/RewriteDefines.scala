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
 * Author : Pramod Subramanyan
 *
 * Rewrite (inline) usage of 'define' statements.
 */

package uclid
package lang

class RewriteDefinesPass extends RewritePass {
  def rewrite(defDecl : DefineDecl, args : List[Expr], ctx : Scope) : Option[Expr] = {
    val rewriteMap : Map[Expr, Expr] = (defDecl.sig.args zip args).map(p => p._1._1 -> p._2).toMap
    val exprRewriter = new ExprRewriter("DefineRewriter", rewriteMap)
    exprRewriter.visitExpr(defDecl.expr, ctx)
  }

  override def rewriteFuncApp(fapp : FuncApplication, ctx : Scope) : Option[Expr] = {
    fapp.e match {
      case id : Identifier =>
        ctx.map.get(id) match {
          case Some(Scope.Define(id, sig, defDecl)) => rewrite(defDecl, fapp.args, ctx)
          case _ => Some(fapp)
        }
      case _ => Some(fapp)
    }
  }
}

class RewriteDefines extends ASTRewriter("RewriteDefines", new RewriteDefinesPass())