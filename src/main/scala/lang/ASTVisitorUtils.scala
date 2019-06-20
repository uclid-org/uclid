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

import com.typesafe.scalalogging.Logger

/** Very simple pass too print module. */
class ASTPrinterPass extends ReadOnlyPass[Unit] {
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : Unit, context : Scope) : Unit = {
    if (d == TraversalDirection.Down) {
      UclidMain.println(" ==> " + analysis.passName + " <== ")
      UclidMain.println(module.toString())
    }
  }
}
object ASTPrinter {
  var count = 0
  def getName() : String  = {
    count += 1
    "ASTPrinter:" + count.toString()
  }
}

/** Simple analysis that instantiates ASTPrinterPass to print module. */
class ASTPrinter() extends ASTAnalyzer(ASTPrinter.getName(), new ASTPrinterPass()) {
  override def pass = super.pass.asInstanceOf[ASTPrinterPass]
  in = Some(Unit)
}

class ExprRewriterPass(rewrites : Map[Expr, Expr]) extends RewritePass
{
  val log = Logger(classOf[ExprRewriterPass])

  override def rewriteExpr(e: Expr, context: Scope) : Option[Expr] = {
    if (e.isInstanceOf[Identifier]) {
      val id = e.asInstanceOf[Identifier]
      val g = context.map.get(id)
      if (g.isDefined && g.get.isInstanceOf[Scope.SelectorField]) {
        return Some(e)
      }
    }
    return rewrites.get(e) match {
      case Some(eprime) => Some(eprime)
      case None => Some(e)
    }
  }
  override def rewriteIdentifier(i: Identifier, context: Scope) : Option[Identifier] = {
    log.debug("scope: {}", context.map.toString())
    context.map.get(i) match {
      case Some(Scope.SelectorField(_)) =>
        log.debug("product: {}", i.toString())
        Some(i)
      case _ =>
        rewrites.get(i) match {
          case None =>
            log.debug("unchanged: {}", i.toString())
            Some(Identifier(i.name))
          case Some(eprime) =>
            eprime match {
              case id : Identifier =>
                log.debug("rewrite: {} -> {}", i.toString(), id.toString())
                Some(id)
              case _ =>
                log.debug("rewrite: {} -> {}", i.toString(), i.toString())
                Some(Identifier(i.name))
            }
        }
    }
  }
}

object ExprRewriter
{
  def rewriteExpr(e : Expr, rewrites : Map[Expr, Expr], context : Scope) : Expr = {
    val rewriter = new ASTRewriter("", new ExprRewriterPass(rewrites))
    var e1 = e
    var e2 = rewriter.visitExpr(e1, context).get
    do {
      e1 = e2
      e2 = rewriter.visitExpr(e1, context).get
    } while (e2 != e1)
    e2
  }
  def rewriteExprOnce(e : Expr, rewrites : Map[Expr, Expr], context : Scope) : Expr = {
    val rewriter = new ASTRewriter(_passName = "", new ExprRewriterPass(rewrites))
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
  def rewriteExprFixpoint( e : Expr, context : Scope) : Expr = {
    var e1 = e
    var e2 = visitExpr(e1, context).get
    do {
      e1 = e2
      e2 = visitExpr(e1, context).get
    } while (e2 != e1)
    e2
  }

  def rewriteExpr(e : Expr, context : Scope) : Expr = {
    visitExpr(e, context).get
  }

  def rewriteStatements(stmts : List[Statement], context : Scope) : List[Statement] = {
    return stmts.flatMap(visitStatement(_, context))
  }

  def rewriteStatement(stmt : Statement, context : Scope) : Option[Statement] = {
    visitStatement(stmt, context)
  }
}

class OldExprRewriterPass(rewrites : Map[Identifier, (Identifier, Identifier)]) extends RewritePass
{
  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    opapp.op match {
      case OldOperator() =>
        opapp.operands(0) match {
          case arg: Identifier => {
            rewrites.get(arg) match {
              case Some(v) => Some(v._2)
              case None => Some(Operator.old(arg))
            }
          }
          case arg: OperatorApplication => {
            arg.op match {
              case SelectFromInstance(field) => Some(Operator.oldInstance(arg))
              case _ => {
                Utils.raiseParsingError("Unexpected argument in the 'old' operator", opapp.pos, context.filename)
                Some(Operator.oldInstance(arg))
              }
            }
          }
          case _ => {
            Utils.raiseParsingError("Unexpected argument in the 'old' operator", opapp.pos, context.filename)
            Some(opapp)
          }
        }
      case HistoryOperator() =>
        val arg = opapp.operands(0).asInstanceOf[Identifier]
        val past = opapp.operands(1)
        rewrites.get(arg) match {
          case Some(v) => Some(Operator.history(v._1, past))
          case None => Some(Operator.history(arg, past))
        }
      case _ => Some(opapp)
    }
  }
}

object OldExprRewriter {
  var i = 0
  def getName() : String = {
    i += 1
    "OldExprRewriter:" + i.toString()
  }
}

class OldExprRewriter(rewrites : Map[Identifier, (Identifier, Identifier)])
  extends ASTRewriter(OldExprRewriter.getName(), new OldExprRewriterPass(rewrites))
{
  def rewriteExpr(e : Expr, context : Scope) : Expr = {
    visitExpr(e, context).get
  }
  def rewriteStatements(stmts : List[Statement], context : Scope) : List[Statement] = {
    return stmts.flatMap(visitStatement(_, context))
  }
  def rewriteStatement(stmt : Statement, context : Scope) : Option[Statement] = {
    visitStatement(stmt, context)
  }
}

