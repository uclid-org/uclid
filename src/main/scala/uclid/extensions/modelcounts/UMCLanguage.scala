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
abstract class Statement extends l.ASTNode {
  override def toString = Utils.join(toLines, "\n") + "\n"
  def toLines : List[String]
  def expressions : Seq[CountingOp]
}

case class DisjointStmt(e1 : CountingOp, e2 : CountingOp, e3 : CountingOp) extends Statement {
  override val hashId = 130001
  override val md5hashCode = computeMD5Hash(e1, e2, e3)
  override def toLines = List("assert disjoint: " + e1.toString() + " == " + e2.toString() + " + " +  e3.toString())
  override def expressions = Seq(e1, e2, e3)
}

case class CountingProof(id : l.Identifier, decls : List[l.Decl], stmts : List[Statement]) extends l.ASTNode {
  override def toString = {
    "module " + id.toString() + " {\n" +
    Utils.join(decls.map("  " + _.toString()), "\n") +
    "\n\n  proof {\n" +
    Utils.join(stmts.map(st => "    " + st.toString()), "\n") +
    "\n  }\n}"
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
}
