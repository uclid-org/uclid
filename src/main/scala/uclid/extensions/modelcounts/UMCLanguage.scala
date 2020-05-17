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
import uclid.Memo
import uclid.lang.{Identifier, Type}


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
  val countingOps : Seq[CountingOp]
  val expressions: Seq[l.Expr]
  def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement]
}

case class AssertStmt(e : l.Expr) extends Statement {
  override val hashId = 130000
  override val md5hashCode = computeMD5Hash(e)
  override def toLines = List("assert " + e.toString())
  override val countingOps = {
    def isCountingOp(e : l.Expr) = {
      e match {
        case CountingOp(_, _, _) => true
        case _ => false
      }
    }
    UMCExpressions.findSubExpressions(e, isCountingOp).map(_.asInstanceOf[CountingOp]).toSeq
  }
  override val expressions = Seq(e)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    rewriter(e) match {
      case Some(eP) => Some(AssertStmt(eP))
      case None => None
    }
  }
}

case class OrStmt(e1 : CountingOp, e2 : CountingOp, e3 : CountingOp) extends Statement {
  assert (e1.xs == e2.xs && e2.xs == e3.xs)
  assert (e1.ys == e2.ys && e2.ys == e3.ys)

  override val hashId = 130001
  override val md5hashCode = computeMD5Hash(e1, e2, e3)
  override def toLines = List("assert or: " + e1.toString() + " == " + e2.toString() + " + " +  e3.toString())
  override val countingOps = Seq(e1, e2, e3)
  override val expressions = Seq(e1, e2, e3)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e1.e), rewriter(e2.e), rewriter(e3.e)) match {
      case (Some(e1p), Some(e2p), Some(e3p)) =>
        val op1 = CountingOp(e1.xs, e1.ys, e1p)
        val op2 = CountingOp(e2.xs, e2.ys, e2p)
        val op3 = CountingOp(e3.xs, e3.ys, e3p)
        Some(OrStmt(op1, op2, op3))
      case _ => None
    }
  }
}

case class RangeStmt(op : CountingOp, cnt : l.Expr, assump: l.Expr) extends Statement {
  lazy val lb : l.Expr = {
    op.e match {
      case l.OperatorApplication(l.ConjunctionOp(), 
            List(l.OperatorApplication(l.LEOp(), List(lb, l.Identifier(v))),
                 l.OperatorApplication(l.LTOp(), List(l.Identifier(u), ub)))) => lb
      case _ =>
        throw new Utils.AssertionError("Unexpected operand to range expression.")
    }
  }
  lazy val ub : l.Expr = {
    op.e match {
      case l.OperatorApplication(l.ConjunctionOp(), 
            List(l.OperatorApplication(l.LEOp(), List(lb, l.Identifier(v))),
                 l.OperatorApplication(l.LTOp(), List(l.Identifier(u), ub)))) => ub
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
  override def toLines = List("assert range: " + assump.toString + " ==> " + op.toString() + " == " + cnt.toString())
  override val countingOps = Seq(op)
  override val expressions = Seq(op, cnt)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(op.e), rewriter(cnt), rewriter(assump)) match {
      case (Some(ep), Some(cntp), Some(aP)) =>
        val op1 = CountingOp(op.xs, op.ys, ep)
        Some(RangeStmt(op1, cntp, aP))
      case _ => None
    }
  }
}
case class ConstLbStmt(e : CountingOp, v : l.IntLit, assump: l.Expr) extends Statement {
  override val hashId = 130003
  override val md5hashCode = computeMD5Hash(e, v, assump)
  override def toLines = {
    if (assump == l.BoolLit(true)) {
      List("assert constLB: " + e.toString() + " >= " + v.toString())
    } else {
      List("assert constLB: " + assump.toString() + " ==> " + e.toString() + " >= " + v.toString()) 
    }
  }
  override val countingOps = Seq(e)
  override val expressions = Seq(e, v, assump)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e.e), rewriter(v), rewriter(assump)) match {
      case (Some(e1p), Some(e2p), Some(aP)) =>
        val e1 = CountingOp(e.xs, e.ys, e1p)
        Some(ConstLbStmt(e1, e2p.asInstanceOf[l.IntLit], aP))
      case _ => None
    }
  }
}

case class ConstUbStmt(e : CountingOp, v : l.IntLit, assump : l.Expr) extends Statement {
  override val hashId = 130004
  override val md5hashCode = computeMD5Hash(e, v, assump)
  override def toLines = {
    if (assump == l.BoolLit(true)) {
      List("assert constUB: " + e.toString() + " < " + v.toString())
    } else {
      List("assert constUB: " + assump.toString() + " ==> " + e.toString() + " < " + v.toString()) 
    }
  }
  override val countingOps = Seq(e)
  override val expressions = Seq(e, v, assump)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e.e), rewriter(v), rewriter(assump)) match {
      case (Some(e1p), Some(e2p), Some(aP)) =>
        val e1 = CountingOp(e.xs, e.ys, e1p)
        Some(ConstUbStmt(e1, e2p.asInstanceOf[l.IntLit], aP))
      case _ => None
    }
  }
}

case class ConstEqStmt(e : CountingOp, v : l.IntLit, assump : l.Expr) extends Statement {
  override val hashId = 130005
  override val md5hashCode = computeMD5Hash(e, v, assump)
  override def toLines = {
    if (assump == l.BoolLit(true)) {
      List("assert constEq: " + e.toString() + " >= " + v.toString())
    } else {
      List("assert constEq: " + assump.toString() + " ==> " + e.toString() + " == " + v.toString()) 
    }
  }
  override val countingOps = Seq(e)
  override val expressions = Seq(e, v, assump)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e.e), rewriter(v), rewriter(assump)) match {
      case (Some(e1p), Some(e2p), Some(aP)) =>
        val e1 = CountingOp(e.xs, e.ys, e1p)
        Some(ConstEqStmt(e1, e2p.asInstanceOf[l.IntLit], assump))
      case _ => None
    }
  }
}

case class IndLbStmt(fp : CountingOp, f : CountingOp, g : CountingOp, skolems : List[l.Expr]) extends Statement {
  assert (fp.ys.size >= 1 && f.ys.size >= 1 && g.ys.size >= 1)
  assert (fp.ys(0)._2.isInt)
  assert (fp.ys == f.ys)
  val n = fp.ys(0)._1
  assert (new ExprRewriter(Map(n -> UMCExpressions.plus(n, l.IntLit(1)))).rewrite(f.e) == fp.e)
  
  override val hashId = 130006
  override val md5hashCode = computeMD5Hash(fp, f, g, skolems)
  override def toLines = {
    List("assert indLB: " + fp.toString + " >= " +
         f.toString() + " * " + g.toString() + " skolems (" + 
         Utils.join(skolems.map(_.toString()), ", ") + ");")
  }
  override val countingOps = Seq(fp, f, g)
  override val expressions = Seq(fp, f, g) ++ skolems
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    val e_fp = rewriter(fp.e)
    val e_f = rewriter(f.e)
    val e_g = rewriter(g.e)
    val skolemsP = skolems.flatMap(rewriter(_))
    (e_fp, e_f, e_g) match {
      case (Some(e1), Some(e2), Some(e3)) =>
        val fpNew = CountingOp(fp.xs, fp.ys, e1)
        val fNew = CountingOp(f.xs, f.ys, e2)
        val gNew = CountingOp(g.xs, g.ys, e3)
        Some(IndLbStmt(fpNew, fNew, gNew, skolemsP))
      case _ => None
    }
  }
}

case class UbStmt(e1 : CountingOp, e2: CountingOp) extends Statement {
  assert (e1.xs == e2.xs && e1.ys == e2.ys)

  override val hashId = 130007
  override val md5hashCode = computeMD5Hash(e1, e2)
  override def toLines =
      List("assert UB: " + e1.toString() + " <= " + e2.toString())
  override val countingOps = Seq(e1, e2)
  override val expressions = Seq(e1, e2)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e1.e), rewriter(e2.e)) match {
      case (Some(e1p), Some(e2p)) =>
        val e1New = CountingOp(e1.xs, e1.ys, e1p)
        val e2New = CountingOp(e2.xs, e2.ys, e2p)
        Some(UbStmt(e1New, e2New))
      case _ => None
    }
  }
}

case class AndUbStmt(e1 : CountingOp, e2 : CountingOp, e3 : CountingOp) extends Statement {
  assert (e1.xs.toSet == (e2.xs.toSet union e3.xs.toSet))

  override val hashId = 130008
  override val md5hashCode = computeMD5Hash(e1, e2, e3)
  override def toLines = List("assert andUB: " + e1.toString() + " <= " + e2.toString() + " * " +  e3.toString())
  override val countingOps = Seq(e1, e2, e3)
  override val expressions = Seq(e1, e2, e3)
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    (rewriter(e1.e), rewriter(e2.e), rewriter(e3.e)) match {
      case (Some(e1p), Some(e2p), Some(e3p)) =>
        val op1 = CountingOp(e1.xs, e1.ys, e1p)
        val op2 = CountingOp(e2.xs, e2.ys, e2p)
        val op3 = CountingOp(e3.xs, e3.ys, e3p)
        Some(AndUbStmt(op1, op2, op3))
      case _ => None
    }
  }
}

case class DisjointStmt(e1 : CountingOp, e2 : CountingOp, e3 : CountingOp) extends Statement {
  assert (e1.xs.toSet == (e2.xs.toSet union e3.xs.toSet))

  override val hashId = 130009
  override val md5hashCode = computeMD5Hash(e1, e2, e3)
  override def toLines = List("assert disjoint: " + e1.toString() + " == " + e2.toString() + " * " +  e3.toString())
  override val countingOps = Seq(e1, e2, e3)
  override val expressions = Seq(e1, e2, e3)
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

case class InjectivityStmt(f : CountingOp, g: CountingOp, skolems : List[l.Expr] ) extends Statement {
  override val hashId = 130010
  override val md5hashCode = computeMD5Hash(f, g, skolems)
  override def toLines =
    List("assert injectivity: " + f.toString() + " <= " + g.toString() + " skolems (" +
      Utils.join(skolems.map(_.toString()), ", ") + ");")
  override val countingOps = Seq(f, g)
  override val expressions = Seq(f, g) ++ skolems
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    val skolemsP = skolems.flatMap(rewriter(_))
    (rewriter(f.e), rewriter(g.e)) match {
      case (Some(e1p), Some(e2p)) =>
        val e1New = CountingOp(f.xs, f.ys, e1p)
        val e2New = CountingOp(g.xs, g.ys, e2p)
        Some(InjectivityStmt(e1New, e2New, skolemsP))
      case _ => None
    }
  }
}

case class IndUbStmt(fp : CountingOp, f : CountingOp, g : CountingOp, skolems : List[l.Expr]) extends Statement {
  assert (fp.ys.size == 1 && f.ys.size == 1 && g.ys.size == 1)
  assert (fp.ys(0)._2.isInt)
  assert (fp.ys == f.ys && f.ys == g.ys)
  val n = fp.ys(0)._1
  assert (new ExprRewriter(Map(n -> UMCExpressions.plus(n, l.IntLit(1)))).rewrite(f.e) == fp.e)

  override val hashId = 130011
  override val md5hashCode = computeMD5Hash(fp, f, g, skolems)
  override def toLines = {
    List("assert indUB: " + fp.toString + " <= " +
      f.toString() + " * " + g.toString() + " skolems (" +
      Utils.join(skolems.map(_.toString()), ", ") + ");")
  }
  override val countingOps = Seq(fp, f, g)
  override val expressions = Seq(fp, f, g) ++ skolems
  override def rewrite(rewriter : l.Expr => Option[l.Expr]) : Option[Statement] = {
    val e_fp  = rewriter(fp.e)
    val e_f   = rewriter(f.e)
    val e_g   = rewriter(g.e)
    val skolemsP = skolems.flatMap(rewriter(_))
    (e_fp, e_f, e_g) match {
      case (Some(e1), Some(e2), Some(e3)) =>
        val fpNew = CountingOp(fp.xs, fp.ys, e1)
        val fNew  = CountingOp(f.xs, f.ys, e2)
        val gNew  = CountingOp(g.xs, g.ys, e3)
        Some(IndUbStmt(fpNew, fNew, gNew, skolemsP))
      case _ => None
    }
  }
}

case class CountingProof(id : l.Identifier, decls : List[l.Decl], lemmas: List[l.ProcedureDecl],
                         stmts : List[Statement]) extends l.ASTNode {
  override def toString = {
    "module " + id.toString() + " {\n" +
    Utils.join(decls.map("  " + _.toString()), "\n") + "\n\n" +
    Utils.join(lemmas.map("  " + _.toString()), "\n") +
    "\n\n  proof {\n" +
    Utils.join(stmts.map(st => "    " + st.toString()), "\n") +
    "\n  }\n}"
  }
  def rewriteStatments(rewriter : l.ASTRewriter) : CountingProof = {
    val ctx = decls.foldLeft(l.Scope.empty)((acc, d) => acc + d)
    def rewriterFn(expr : l.Expr) : Option[l.Expr] = {
      rewriter.visitExpr(expr, ctx)
    }

    val stmtsP = stmts.flatMap(st => st.rewrite(rewriterFn))
    CountingProof(id, decls, lemmas, stmtsP)
  }
  override val hashId = 131001
  override val md5hashCode = computeMD5Hash(id, decls, stmts)
}

/** Helpers to construct UCLID5 expressions. */
object UMCExpressions {
  // Helper functions to more easily construct expressions.
  def forall(vs : List[(l.Identifier, l.Type)], e : l.Expr) = {
    if (vs.nonEmpty) {
      val op = l.ForallOp(vs, List.empty)
      l.OperatorApplication(op, List(e))
    } else {
      e
    }
  }
  
  def exists(vs : List[(l.Identifier, l.Type)], e : l.Expr) = {
    assert (vs.nonEmpty)
    val op = l.ExistsOp(vs, List.empty)
    l.OperatorApplication(op, List(e))
  }
  
  def and(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.ConjunctionOp(), List(e1, e2))
  }

  def andL(es : Seq[l.Expr]) = {
    assert (es.nonEmpty)
    es.foldLeft(l.BoolLit(true).asInstanceOf[l.Expr])((acc, e) => and(acc, e)) 
  }

  def or(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.DisjunctionOp(), List(e1, e2))
  }
  
  def orL(es : Seq[l.Expr]) = {
    assert (es.nonEmpty)
    es.foldLeft(l.BoolLit(false).asInstanceOf[l.Expr])((acc, e) => or(acc, e)) 
  }

  def iff(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IffOp(), List(e1, e2))
  }
  
  def implies(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.ImplicationOp(), List(e1, e2))
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
  
  def mul(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.MulOp(), List(e1, e2))
  }
  
  def le(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IntLEOp(), List(e1, e2))
  }

  def lt(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IntLTOp(), List(e1, e2))
  }
  
  def ge(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IntGEOp(), List(e1, e2))
  }

  def gt(e1 : l.Expr, e2 : l.Expr) = {
    l.OperatorApplication(l.IntGTOp(), List(e1, e2))
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
  
  def distinct(es : l.Expr*) = {
    if (es.size <= 1) {
      l.BoolLit(true)
    } else {
      l.OperatorApplication(l.DistinctOp(), es.toList)
    }
  }
  
  def apply(id : l.Identifier, args : List[l.Expr]) = {
    l.FuncApplication(id, args)
  }

  def _findSubExpressions(e : l.Expr, fn : l.Expr => Boolean) : Set[l.Expr] = 
    findSubExpressions((e, fn))

  val findSubExpressions = new Memo[(l.Expr, l.Expr => Boolean), Set[l.Expr]](
    (p : (l.Expr, l.Expr => Boolean)) => {
      val expr = p._1
      val fn = p._2
      val subExprs : Set[l.Expr] = expr match {
        case _ : l.Literal => Set.empty
        case _ : l.Identifier => Set.empty
        case _ : l.ExternalIdentifier => Set.empty
        case l.ConstArray(e, t) => _findSubExpressions(e, fn)
        case l.Tuple(es) => es.foldLeft(Set.empty[l.Expr])((acc, e) => _findSubExpressions(e, fn) ++ acc)
        case l.OperatorApplication(op, args) =>
          val opExprs = op match {
            case l.ArraySelect(inds) =>
              inds.foldLeft(Set.empty[l.Expr])((acc, e) => _findSubExpressions(e, fn) ++ acc)
            case l.ArrayUpdate(inds, value) =>
              inds.foldLeft(_findSubExpressions(value, fn))((acc, e) => _findSubExpressions(e, fn) ++ acc)
            case _ =>
              Set.empty[l.Expr]
          }
          args.foldLeft(opExprs)((acc, e) => _findSubExpressions(e, fn) ++ acc)
        case l.Lambda(ids, e) => _findSubExpressions(e, fn)
        case l.FuncApplication(e1, e2) => e2.foldLeft(_findSubExpressions(e1, fn))((acc, e) => acc ++ _findSubExpressions(e, fn))
        case CountingOp(xs, ys, e) => _findSubExpressions(e, fn)
      }
      if (fn(expr)) { subExprs + expr}
      else { subExprs }
    }
  )
  
  def findSupport(es : Seq[l.Expr]) : Set[l.Identifier] = {
    es.foldLeft(Set.empty[l.Identifier])((acc, e) => acc ++ findSupport(e))
  }
  val findSupport : Memo[l.Expr, Set[l.Identifier]] = new Memo[l.Expr, Set[l.Identifier]](
    e => {
      e match {
        case _ : l.Literal | _ : l.Identifier =>
          Set.empty
        case l.ConstArray(e, t) =>
          findSupport(e)
        case l.Tuple(es) =>
          findSupport(es)
        case l.OperatorApplication(op, args) =>
          val subSupport = findSupport(args)
          op match {
            case qOp : l.QuantifiedBooleanOperator =>
              subSupport -- qOp.variables.map(_._1).toSet
            case l.ArraySelect(inds) =>
              findSupport(inds)
            case l.ArrayUpdate(inds, value) =>
              findSupport(inds) ++ findSupport(value) ++ subSupport
            case _ =>
              subSupport
          }
        case l.Lambda(ids, exp) =>
          val subSupport = findSupport(exp)
          subSupport -- ids.map(_._1).toSet
        case CountingOp(xs, ys, e) =>
          // FIXME: this is a major hack.
          // Introducing this because we *want* the variables in a CountingOp
          // to be "captured" by outer quantifiers.
          // Need to revist and fix this.
          Set.empty
        case _ : l.ExternalIdentifier =>
          throw new Utils.AssertionError("Eliminate external identifiers before calling findSupport.")
        case l.FuncApplication(e1, e2s) =>
          throw new Utils.AssertionError("Eliminate function applications before calling findSupport.")
      }
    }
  )
}

class ExprRewriter(val rwMap : Map[l.Expr, l.Expr]) {
  val supports = rwMap.map(p => p._1 -> UMCExpressions.findSupport(p._1)).toMap

  val rewrite : Memo[l.Expr, l.Expr] = new Memo[l.Expr, l.Expr](
    exp => {
      val expP : l.Expr = exp match {
        case _ : l.Literal | _ : l.Identifier | _ : l.ExternalIdentifier =>
          exp
        case l.ConstArray(e, t) =>
          val eP : l.Expr = rewrite(e)
          l.ConstArray(eP, t)
        case l.Tuple(es) =>
          val esP = es.map(e => rewrite(e))
          l.Tuple(esP)
        case l.OperatorApplication(op, args) =>
          op match {
            case qOp : l.QuantifiedBooleanOperator =>
              val mapP = rwMap.filter(p => !qOp.variables.exists(v => supports(p._1).contains(v._1)))
              if (mapP != rwMap) {
                // have to eliminate the bound variables.
                val rewriter = new ExprRewriter(mapP)
                val argsP = args.map(arg => rewriter.rewrite(arg))
                l.OperatorApplication(op, argsP)
              } else {
                // do the usual
                val argsP = args.map(arg => rewrite(arg))
                l.OperatorApplication(op, argsP)
              }
            case l.ArraySelect(inds) =>
              val indsP = inds.map(ind => rewrite(ind))
              val argsP = args.map(arg => rewrite(arg))
              l.OperatorApplication(l.ArraySelect(indsP), argsP)
            case l.ArrayUpdate(inds, e) =>
              val indsP = inds.map(ind => rewrite(ind))
              val eP = rewrite(e)
              val argsP = args.map(arg => rewrite(arg))
              l.OperatorApplication(l.ArrayUpdate(indsP, eP), argsP)
            case _ =>
              // do the usual.
              val argsP = args.map(arg => rewrite(arg))
              l.OperatorApplication(op, argsP)
          }
        case l.Lambda(ids, exp) =>
          val mapP = rwMap.filter(p => !ids.exists(v => supports(p._1).contains(v._1)))
          val expP = if (mapP != rwMap) {
            // have to eliminate the bound variables.
            val rewriter = new ExprRewriter(mapP)
            rewriter.rewrite(exp)
          } else {
            // do the usual.
            rewrite(exp)
          }
          l.Lambda(ids, exp)
        case l.FuncApplication(e1, e2s) =>
          val e1p = rewrite(e1)
          val e2sp = e2s.map(e2 => rewrite(e2))
          l.FuncApplication(e1p, e2sp)
        case CountingOp(xs, ys, e) =>
          val eP = rewrite(e)
          CountingOp(xs, ys, eP)
      }
      rwMap.get(expP) match {
        case Some(repl) => repl
        case None => expP
      }
    })
}