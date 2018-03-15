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
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : Unit, context : Scope) : Unit = {
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
  override def rewriteExpr(e: Expr, context: Scope) : Option[Expr] = {
    rewrites.get(e) match {
      case Some(eprime) => Some(eprime)
      case None => Some(e)
    }
  }
  override def rewriteIdentifier(i: Identifier, context: Scope) : Option[Identifier] = {
    rewrites.get(i) match {
      case None => Some(i)
      case Some(eprime) =>
        eprime match {
          case id : Identifier => Some(id)
          case _ => Some(i)
        }
    }
  }
}

object ExprRewriter
{
  def rewriteExpr(e : Expr, rewrites : Map[Expr, Expr], context : Scope) : Expr = {
    val rewriter = new ASTRewriter("", new ExprRewriterPass(rewrites))
    rewriter.visitExpr(e, context).get
  }
  def rewriteLHS(lhs : Lhs, rewrites: Map[Expr, Expr], context : Scope) : Lhs = {
    val rewriter = new ASTRewriter("", new ExprRewriterPass(rewrites))
    rewriter.visitLhs(lhs, context).get
  }
}

class ExprRewriter(name: String, rewrites : Map[Expr, Expr])
  extends ASTRewriter(name, new ExprRewriterPass(rewrites))
{
  def rewriteStatements(stmts : List[Statement]) : List[Statement] = {
    val emptyContext = Scope.empty
    return stmts.flatMap(visitStatement(_, emptyContext))
  }
}
