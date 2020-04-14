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
 * Main file for the UCLID model counter.
 *
 */
package uclid.extensions.modelcounts

import uclid.UclidMain
import uclid.{lang => l}
import uclid.Utils


/** CountingOp is a new operator we introduce for the UMC extension. */
case class CountingOp(xs: List[(l.Identifier, l.Type)], ys: List[(l.Identifier, l.Type)], e : l.Expr) extends l.Expr {
  override def toString() = {
    val s1 = Utils.join(xs.map(v => v._1.toString() + " : " + v._2.toString()), ", ")
    val s2 = if (ys.size > 0) {
      val s2 = Utils.join(ys.map(v => v._1.toString() + " : " + v._2.toString()), ", ")
      "#[(" + s1 + ") for (" + s2 + ")] :: "
    } else {
      "#[(" + s1 + ")] :: "
    }
    s2 + "(" + e.toString() + ")"
  }
  override val hashId = 1402
  override val md5hashCode = computeMD5Hash(xs, ys)
}

/** This is the base class for all the "statements" in the proof. */
sealed abstract class Statement extends l.ASTNode {
  override def toString = Utils.join(toLines, "\n") + "\n"
  def toLines : List[String]
  def countingOps : Seq[CountingOp]
  def expressions: Seq[l.Expr]
  def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement]
}

case class DisjointStmt(e1 : CountingOp, e2 : CountingOp, e3 : CountingOp) extends Statement {
  override val hashId = 130001
  override val md5hashCode = computeMD5Hash(e1, e2, e3)
  override def toLines = List("assert disjoint: " + e1.toString() + " == " + e2.toString() + " + " +  e3.toString())
  override def countingOps = Seq(e1, e2, e3)
  override def expressions = Seq(e1, e2, e3)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e1.e), rewriter(e2.e), rewriter(e3.e)) match {
      case (Some(e1p), Some(e2p), Some(e3p)) =>
        val op1 = CountingOp(e1.xs, e1.ys, e1p)
        val op2 = CountingOp(e2.xs, e2.ys, e2p)
        val op3 = CountingOp(e3.xs, e3.ys, e3p)
        Some(DisjointStmt(op1, op2, op3))
      case _ => None
    }
  }
}

case class RangeStmt(op : CountingOp, cnt : l.Expr) extends Statement {
  lazy val lb : l.Expr = {
    op.e match {
      case l.OperatorApplication(l.ConjunctionOp(), 
            List(l.OperatorApplication(l.LEOp(), List(lb, l.Identifier(v))),
                 l.OperatorApplication(l.LTOp(), List(l.Identifier(u), ub)))) =>
                   lb
      case _ =>
        throw new Utils.AssertionError("Unexpected operand to range expression.")
    }
  }
  lazy val ub : l.Expr = {
    op.e match {
      case l.OperatorApplication(l.ConjunctionOp(), 
            List(l.OperatorApplication(l.LEOp(), List(lb, l.Identifier(v))),
                 l.OperatorApplication(l.LTOp(), List(l.Identifier(u), ub)))) =>
                   ub
      case _ =>
        throw new Utils.AssertionError("Unexpected operand to range expression.")
    }
  }
  lazy val v : l.Identifier = {
    op.e match {
      case l.OperatorApplication(l.ConjunctionOp(), 
            List(l.OperatorApplication(l.LEOp(), List(lb, l.Identifier(v))),
                 l.OperatorApplication(l.LTOp(), List(l.Identifier(u), ub)))) =>
                  assert(u == v)
                  l.Identifier(v)
      case _ =>
        throw new Utils.AssertionError("Unexpected operand to range expression.")
    }
  }
  override val hashId = 130002
  override val md5hashCode = computeMD5Hash(op, cnt)
  override def toLines = List("assert range: " + op.toString() + " == " + cnt.toString())
  override def countingOps = Seq(op)
  override def expressions = Seq(op, cnt)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(op.e), rewriter(cnt)) match {
      case (Some(ep), Some(cntp)) =>
        val op1 = CountingOp(op.xs, op.ys, ep)
        Some(RangeStmt(op1, cntp))
      case _ => None
    }
  }
}
case class ConstLbStmt(e : CountingOp, v : l.IntLit) extends Statement {
  override val hashId = 130003
  override val md5hashCode = computeMD5Hash(e, v)
  override def toLines = List("assert constLB: " + e.toString() + " >= " + v.toString())
  override def countingOps = Seq(e)
  override def expressions = Seq(e, v)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e.e), rewriter(v)) match {
      case (Some(e1p), Some(e2p)) =>
        val e1 = CountingOp(e.xs, e.ys, e1p)
        Some(ConstLbStmt(e1, e2p.asInstanceOf[l.IntLit]))
      case _ => None
    }
  }
}

case class CountingProof(id : l.Identifier, decls : List[l.Decl], stmts : List[Statement]) extends l.ASTNode {
  override def toString = {
    "module " + id.toString() + " {\n" +
    Utils.join(decls.map("  " + _.toString()), "\n") +
    "\n\n  proof {\n" +
    Utils.join(stmts.map(st => "    " + st.toString()), "\n") +
    "\n  }\n}"
  }
  def rewriteStatments(rewriter : l.ASTRewriter) : CountingProof = {
    val ctx = decls.foldLeft(l.Scope.empty)((acc, d) => acc + d)
    def rewriterFn(expr : l.Expr) : Option[l.Expr] = {
      rewriter.visitExpr(expr, ctx)
    }
    val stmtsP = stmts.map(st => st.rewrite(rewriterFn)).flatten
    CountingProof(id, decls, stmtsP)
  }
  override val hashId = 131001
  override val md5hashCode = computeMD5Hash(id, decls, stmts)
}

/** Helpers to construct UCLID5 expressions. */
object UMCExpressions {
  // Helper functions to more easily construct expressions.
  def forall(vs : List[(l.Identifier, l.Type)], e : l.Expr) = {
    val op = l.ForallOp(vs, List.empty)
    l.OperatorApplication(op, List(e))
  }
  
  def and(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.ConjunctionOp(), List(e1, e2))
  }

  def or(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.DisjunctionOp(), List(e1, e2))
  }

  def iff(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IffOp(), List(e1, e2))
  }
  
  def not(e : l.Expr) = {
    l.OperatorApplication(l.NegationOp(), List(e))
  }
  
  def eq(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.EqualityOp(), List(e1, e2))
  }
  
  def plus(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.AddOp(), List(e1, e2))
  }
  
  def minus(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.SubOp(), List(e1, e2))
  }
  
  def le(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IntLEOp(), List(e1, e2))
  }

  def lt(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IntLTOp(), List(e1, e2))
  }

  def rng(e1 : l.Expr, e2 : l.Expr, e3 : l.Expr) = {
    and(le(e1, e2), lt(e2, e3))
  }
  
  def ite(c : l.Expr, e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.ITEOp(), List(c, e1, e2))
  }
  
  def max(e1 : l.Expr, e2 : l.Expr) = {
    ite(lt(e1, e2), e2, e1)
  }
}
