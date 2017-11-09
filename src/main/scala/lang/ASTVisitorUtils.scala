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
 * A couple of AST-handling utilities.
 *   (i) ASTPrinterPass  : Prints out the module
 *  (ii) ExprRewriterPas : Replaces all instances of an expression with another. 
 */
package uclid
package lang

/** Very simple pass too print module. */
class ASTPrinterPass extends ReadOnlyPass[Unit] {
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : Unit, context : ScopeMap) : Unit = {
    if (d == TraversalDirection.Down) {
      println(module)
    }
  }
}
/** Simple analysis that instantiates ASTPrinterPass to print module. */
class ASTPrinter(name: String) extends ASTAnalyzer(name, new ASTPrinterPass()) {
  override def pass = super.pass.asInstanceOf[ASTPrinterPass]
  in = Some(Unit)
}

class ExprRewriterPass(rewrites : Map[Expr, Expr]) extends RewritePass
{
  override def rewriteExpr(e: Expr, context: ScopeMap) : Option[Expr] = {
    rewrites.get(e) match {
      case Some(eprime) => Some(eprime)
      case None => Some(e)
    }
  }
  override def rewriteIdentifier(i: Identifier, context: ScopeMap) : Option[Identifier] = {
    rewrites.get(i) match {
      case None => Some(i)
      case Some(eprime) => eprime match {
        case idprime : Identifier => Some(idprime)
        case _ => Some(i)
      }
    }
  }
}

class ExprRewriter(name: String, rewrites : Map[Expr, Expr]) 
  extends ASTRewriter(name, new ExprRewriterPass(rewrites))
{
  def rewriteStatements(stmts : List[Statement]) : List[Statement] = {
    val emptyContext = ScopeMap.empty
    return stmts.flatMap(visitStatement(_, emptyContext))
  }
}
