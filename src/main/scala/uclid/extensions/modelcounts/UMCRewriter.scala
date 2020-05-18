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
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
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
 * Rewriter for the UCLID5 model counter.
 *
 */
package uclid.extensions.modelcounts

import uclid.{lang => l}
import uclid.Memo
import uclid.extensions.modelcounts.{UMCExpressions => E}
import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}
import uclid.lang.BlockStmt


class UMCRewriter(cntProof : CountingProof) {
  /* We will be using this set in a number of places. */
  type CountingOpSet = Set[CountingOp]
  /* A map from counting ops to the UFs that represent them. */
  type UFMap = Map[CountingOp, l.FunctionDecl]
  

  /** Finding all the counting operators in a list of assert statements. */
  def identifyCountOps(proofBlk: List[Statement]) : CountingOpSet = {
    proofBlk.foldLeft(Set.empty[CountingOp]) {
      (acc, st) => acc ++ st.countingOps.toSet
    }
  }

  /** Identifiers that are already declared in the module. */
  val existingIds = cntProof.decls.flatMap(d => d.declNames).toSet
  /** Identifiers that are declared + newly generated names. */
  val usedIds : MutableSet[l.Identifier] = MutableSet.empty[l.Identifier] ++ existingIds
  /** Counters that track (roughly) the number of generated identifiers with each prefix. */
  val counters = MutableMap.empty[String, Int]
  /** Generate a new id. */
  def generateId(prefix: String) : l.Identifier = {
    var cnt = counters.get(prefix) match {
      case Some(n) => n + 1
      case None    => 1
    }
    def getName(n : Int) = l.Identifier(prefix + "_" + n.toString())
    var name = getName(cnt)
    while (usedIds.contains(name)) {
      cnt += 1
      name = getName(cnt) 
    }
    usedIds += name
    counters.put(prefix, cnt)
    name
  }
  /** Generate UF decls for the identified counting operators.
   *
   */
  def generateCountingOpToUFMap(ops : CountingOpSet) : (UFMap) = {
    ops.map {
      op => {
        val ufId = generateId("count")
        val sig = l.FunctionSig(op.ys, l.IntegerType())
        val uf = l.FunctionDecl(ufId, sig)
        op -> uf
      }
    }.toMap
  }
  
  /**
   * Create the list of UF + Axiom declarations.
   */
  def generateUFDecls(ufMap : UFMap) : List[l.Decl] = {
    def geqZero(e : l.Expr) : l.Expr = {
      l.OperatorApplication(l.IntGEOp(), List(e, l.IntLit(0)))
    }
    def quantify(ufDecl : l.FunctionDecl, e : l.Expr) : l.Expr = {
      if (ufDecl.sig.args.nonEmpty) {
        l.OperatorApplication(l.ForallOp(ufDecl.sig.args, List.empty), List(e))
      } else {
        e
      }
    }
    ufMap.flatMap {
      p => {
        val ufDecl = p._2
        val innerExpr = geqZero(l.FuncApplication(ufDecl.id, ufDecl.sig.args.map(_._1)))
        val axExpr = quantify(ufDecl, innerExpr)
        val axiomDecl = l.AxiomDecl(Some(generateId("assump")), axExpr, List.empty)
        List(ufDecl, axiomDecl)
      }
    }.toList
  }

  def _apply(uf : l.FunctionDecl) = {
    l.FuncApplication(uf.id, uf.sig.args.map(_._1))
  }
  
  def rewriteAssert(ufMap : UFMap, st : AssertStmt) : List[l.Statement] = {
    val rewriter = new ExprRewriter(ufMap.map(p => (p._1 -> _apply(p._2))).toMap)
    val eP = rewriter.rewrite(st.e)
    val assertStmt = l.AssertStmt(eP, None, List.empty)
    List(assertStmt)
  }

  def rewriteOr(ufMap : UFMap, st : OrStmt) : List[l.Statement] = {
    val o1 = st.e1
    val o2 = st.e2
    val o3 = st.e3
    val args = o1.xs ++ o1.ys
    val f1 = o1.e
    val f2 = o2.e
    val f3 = o3.e
    val assertExpr = E.and(E.forall(args, E.iff(f1, E.or(f2, f3))),
                          E.forall(args, E.not(E.and(f2, f3))))
    val assertStmt = l.AssertStmt(assertExpr, Some(l.Identifier("Or")), List.empty)
    val ufn1 = _apply(ufMap(o1))
    val ufn2 = _apply(ufMap(o2))
    val ufn3 = _apply(ufMap(o3))
    val assumeExpr = E.forall(st.e1.ys, E.eq(ufn1, E.plus(ufn2, ufn3)))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    List(assertStmt, assumeStmt)
  }

  def rewriteRange(ufMap : UFMap, st : RangeStmt) : List[l.Statement] = {
    val ufn = _apply(ufMap(st.op))
    val assumeExpr = E.forall(st.op.ys, E.eq(ufn, E.max(l.IntLit(0), E.minus(st.ub, st.lb))))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    val assertExpr = E.forall(st.op.ys, E.implies(st.assump, E.eq(ufn, st.cnt)))
    val assertStmt = l.AssertStmt(assertExpr, Some(l.Identifier("Range")), List.empty)
    List(assumeStmt, assertStmt)
  }

  def getCnstBoundStmt(ufMap : UFMap, assump : l.Expr, e : CountingOp, cnt : Int, decorators : List[l.ExprDecorator]) = {
    val cntArgs = e.xs
    val qVars = e.ys
    val ante = assump
    val argVars = cntArgs.map(a => a._1)
    val argsListP = (1 to cnt).map(i => cntArgs.map(a => generateId(a._1.name)))
    val rwMaps = argsListP.map(argsP => (argVars.map(_.asInstanceOf[l.Expr]) zip argsP).toMap)
    val exprs = rwMaps.map(rwMap => l.ExprRewriter.rewriteExprOnce(e.e, rwMap, l.Scope.empty))
    val newVars : List[(l.Identifier, l.Type)] =
      argsListP.map(argsP => (cntArgs zip argsP).map(p => (p._2, p._1._2)).toList).toList.flatten ++
      e.ys
    val blkDecls = newVars.map(p => l.BlockVarsDecl(List(p._1), p._2))
    val trueLit = l.BoolLit(true).asInstanceOf[l.Expr]
    val conjunction = exprs.foldLeft(trueLit)((acc, e) => E.and(acc, e))
    val falseLit = l.BoolLit(false).asInstanceOf[l.Expr]
    val distincts = E.distinct(rwMaps.map(m => l.Tuple(m.map(p => p._2).toList)).toList : _*)
    val query = E.forall(qVars, E.implies(ante, E.and(conjunction, distincts)))
    val assertStmt = l.AssertStmt(query, Some(l.Identifier("ConstantBound")), decorators)
    BlockStmt(blkDecls, List(assertStmt))
  }
  def rewriteConstLb(ufMap : UFMap, st : ConstLbStmt) : List[l.Statement] = {
    val blkStmt = getCnstBoundStmt(ufMap, st.assump, st.e, st.v.value.toInt, List(l.CoverDecorator, l.SATOnlyDecorator))
    val ufn = _apply(ufMap(st.e))
    val assumeExpr = E.forall(st.e.ys, E.implies(st.assump, E.ge(ufn, st.v)))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    List(blkStmt, assumeStmt)
  }

  def rewriteConstUb(ufMap : UFMap, st : ConstUbStmt) : List[l.Statement] = {
    val blkStmt = getCnstBoundStmt(ufMap, st.assump, st.e, st.v.value.toInt, List(l.CoverDecorator))
    val ufn = _apply(ufMap(st.e))
    val assumeExpr = E.forall(st.e.ys, E.implies(st.assump, E.lt(ufn, st.v)))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    List(blkStmt, assumeStmt)
  }

  def rewriteUb(ufMap : UFMap, st : UbStmt) : List[l.Statement] = {
    val s1 = st.e1
    val s2 = st.e2
    val args = s1.xs ++ s1.ys
    val f = s1.e
    val g = s2.e
    val assertExpr = E.forall(args, E.implies(f, g))
    val assertStmt = l.AssertStmt(assertExpr, Some(l.Identifier("UB")), List.empty)
    val ufn1 = _apply(ufMap(s1))
    val ufn2 = _apply(ufMap(s2))
    val assumeExpr = E.forall(st.e1.ys, E.le(ufn1, ufn2))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    List(assertStmt, assumeStmt)
  }

  def rewriteAndUb(ufMap : UFMap, st : AndUbStmt) : List[l.Statement] = {
    val s1 = st.e1
    val s2 = st.e2
    val s3 = st.e3
    val args1 = s1.xs ++ s1.ys
    val args2 = s2.xs ++ s2.ys
    val args3 = s3.xs ++ s3.ys
    val f1 = s1.e
    val f2 = s2.e
    val f3 = s3.e
    val assertExpr = E.iff(E.forall(args1, f1), E.and(E.forall(args2, f2), E.forall(args3, f3)))
    val assertStmt = l.AssertStmt(assertExpr, Some(l.Identifier("AndUB")), List.empty)
    val ufn1 = _apply(ufMap(s1))
    val ufn2 = _apply(ufMap(s2))
    val ufn3 = _apply(ufMap(s3))
    val assumeExpr = E.forall(st.e1.ys, E.le(ufn1, E.mul(ufn2, ufn3)))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    List(assertStmt, assumeStmt)
  }

  def rewriteInjectivity(ufMap : UFMap, inj : InjectivityStmt) : List[l.Statement] = {
    // forall x. f(x) ==> g(skolem(x))
    val f = inj.f
    val g = inj.g
    val f_x = f.e
    val g_y = g.e
    val skSubs = (g.xs.map(_._1.asInstanceOf[l.Expr]) zip inj.skolems).toMap
    val conseq = new ExprRewriter(skSubs).rewrite(g_y)
    val impl = E.implies(f_x, conseq)
    val qVars = f.xs ++ f.ys
    val qOp = E.forall(qVars, impl)
    val liftAssertStmt = l.AssertStmt(qOp, Some(l.Identifier("Injectivity_SkolemApplication")), List.empty)

    // Next we want to show injectivity of the skolem:
    // f(x1) && f(x2) && (x1 != x2) ==> skolem(x1) != skolem(x2)
    val x1s = f.xs.map(p => generateId(p._1.toString()))
    val x2s = f.xs.map(p => generateId(p._1.toString()))
    val rwx1 = new ExprRewriter((f.xs zip x1s).map(p => (p._1._1.asInstanceOf[l.Expr] -> p._2.asInstanceOf[l.Expr])).toMap)
    val rwx2 = new ExprRewriter((f.xs zip x2s).map(p => (p._1._1.asInstanceOf[l.Expr] -> p._2.asInstanceOf[l.Expr])).toMap)

    val f_x1n = rwx1.rewrite(f.e)
    val f_x2n = rwx2.rewrite(f.e)
    val xdiff = E.orL((x1s zip x2s).map(p => E.distinct(p._1, p._2)))
    val sk1s = inj.skolems.map(sk => rwx1.rewrite(sk))
    val sk2s = inj.skolems.map(sk => rwx2.rewrite(sk))
    val ante2 = E.andL(List(f_x1n, f_x2n, xdiff))
    val skdiff = E.orL((sk1s zip sk2s).map(p => E.distinct(p._1, p._2)))
    val impl2 = E.implies(ante2, skdiff)
    val vars = (f.xs zip x1s).map(p => (p._2, p._1._2)) ++
      (f.xs zip x2s).map(p => (p._2, p._1._2)) ++ f.ys
    val injAssertStmt = l.AssertStmt(E.forall(vars, impl2), Some(l.Identifier("Injectivity_SkolemInjectivity")), List.empty)

    // Now the assumption.
    val ufn = _apply(ufMap(f))
    val ugn = _apply(ufMap(g))
    val leqExpr = E.le(ufn, ugn)
    val assumpStmt1 = l.AssumeStmt(E.forall(f.ys, leqExpr), None)

    List(liftAssertStmt, injAssertStmt, assumpStmt1)
  }


  def rewriteDisjoint(ufMap : UFMap, st : DisjointStmt) : List[l.Statement] = {
    val e2s = st.e2.xs.toSet
    val e3s = st.e3.xs.toSet
    val intersection = if ((e2s intersect e3s).isEmpty) l.BoolLit(true)
                       else l.BoolLit(false)
    val s1 = st.e1
    val s2 = st.e2
    val s3 = st.e3
    val args1 = s1.xs ++ s1.ys
    val args2 = s2.xs ++ s2.ys
    val args3 = s3.xs ++ s3.ys
    val f1 = s1.e
    val f2 = s2.e
    val f3 = s3.e
    val assertExpr = E.and(E.iff(E.forall(args1, f1), E.and(E.forall(args2, f2), E.forall(args3, f3))), intersection)
    val assertStmt = l.AssertStmt(assertExpr, Some(l.Identifier("Disjoint")), List.empty)
    val ufn1 = _apply(ufMap(s1))
    val ufn2 = _apply(ufMap(s2))
    val ufn3 = _apply(ufMap(s3))
    val assumeExpr = E.forall(st.e1.ys, E.eq(ufn1, E.mul(ufn2, ufn3)))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    List(assertStmt, assumeStmt)
  }

  def rewriteIndLb(ufMap : UFMap, indlb : IndLbStmt) : List[l.Statement] = {
    // First we want f(x, n) && g(y, n) ==> f(skolem(x, y), n + 1)
    val f = indlb.f
    val g = indlb.g
    val f_xn = f.e
    val g_yn = g.e
    val ante = E.and(f_xn, g_yn)
    val nplus1 = E.plus(indlb.n, l.IntLit(1))
    val skSubs = (f.xs.map(_._1.asInstanceOf[l.Expr]) zip indlb.skolems).toMap +
                 (indlb.n.asInstanceOf[l.Expr] -> nplus1)
    val conseq = new ExprRewriter(skSubs).rewrite(f_xn)
    val impl = E.implies(ante, conseq)
    val qVars = f.xs ++ g.xs ++ f.ys ++ g.ys
    val qOp = E.forall(qVars, impl)
    val liftAssertStmt = l.AssertStmt(qOp, Some(l.Identifier("IndLB_SkolemApplication")), List.empty)

    // Now we want to show injectivity of the skolem:
    // f(x1, n) && g(y1, n) && f(x2, n) && g(y2, n) && (x1 != x2 || y1 != y2)
    //   ==> skolem(x1, y1, n) != skolem(x2, y2, n)
    val x1s = f.xs.map(p => generateId(p._1.toString()))
    val x2s = f.xs.map(p => generateId(p._1.toString()))
    val y1s = g.xs.map(p => generateId(p._1.toString()))
    val y2s = g.xs.map(p => generateId(p._1.toString()))
    val rwx1 = new ExprRewriter((f.xs zip x1s).map(p => (p._1._1.asInstanceOf[l.Expr] -> p._2.asInstanceOf[l.Expr])).toMap)
    val rwy1 = new ExprRewriter((g.xs zip y1s).map(p => (p._1._1.asInstanceOf[l.Expr] -> p._2.asInstanceOf[l.Expr])).toMap)
    val rwx2 = new ExprRewriter((f.xs zip x2s).map(p => (p._1._1.asInstanceOf[l.Expr] -> p._2.asInstanceOf[l.Expr])).toMap)
    val rwy2 = new ExprRewriter((g.xs zip y2s).map(p => (p._1._1.asInstanceOf[l.Expr] -> p._2.asInstanceOf[l.Expr])).toMap)
    val rwxy1 = new ExprRewriter(rwx1.rwMap ++ rwy1.rwMap)
    val rwxy2 = new ExprRewriter(rwx2.rwMap ++ rwy2.rwMap)
    val f_x1n = rwx1.rewrite(f.e)
    val g_y1n = rwy1.rewrite(g.e)
    val f_x2n = rwx2.rewrite(f.e)
    val g_y2n = rwy2.rewrite(g.e)
    val xdiff = E.orL((x1s zip x2s).map(p => E.distinct(p._1, p._2)))
    val ydiff = E.orL((y1s zip y2s).map(p => E.distinct(p._1, p._2)))
    val sk1s = indlb.skolems.map(sk => rwxy1.rewrite(sk))
    val sk2s = indlb.skolems.map(sk => rwxy2.rewrite(sk))
    val ante2 = E.andL(List(f_x1n, f_x2n, g_y1n, g_y2n, E.or(xdiff, ydiff)))
    val skdiff = E.orL((sk1s zip sk2s).map(p => E.distinct(p._1, p._2)))
    val impl2 = E.implies(ante2, skdiff)
    val vars = (f.xs zip x1s).map(p => (p._2, p._1._2)) ++
               (f.xs zip x2s).map(p => (p._2, p._1._2)) ++
               (g.xs zip y1s).map(p => (p._2, p._1._2)) ++
               (g.xs zip y2s).map(p => (p._2, p._1._2)) ++ f.ys ++ g.ys
    val injAssertStmt = l.AssertStmt(E.forall(vars, impl2), Some(l.Identifier("IndLB_SkolemInjectivity")), List.empty)

    // Finally, we have to produce the assumption.
    val ufn = _apply(ufMap(f))
    val ugn = _apply(ufMap(g))
    val ufnplus1 = E.apply(ufMap(f).id, List(nplus1) ++ ufMap(f).sig.args.drop(1).map(_._1))
    val geqExpr = E.ge(ufnplus1, E.mul(ufn, ugn))
    val assumpStmt1 = l.AssumeStmt(E.forall(f.ys ++ g.ys, geqExpr), None)
    val ufpn = _apply(ufMap(indlb.fp))
    val eqExpr = E.eq(ufnplus1, ufpn)
    val assumpStmt2 = l.AssumeStmt(E.forall(f.ys, eqExpr), None)
    List(liftAssertStmt, injAssertStmt, assumpStmt1, assumpStmt2)
  }


  def rewriteAssert(ufmap : UFMap, st : Statement) : List[l.Statement] = {
    val newStmts : List[l.Statement] = st match {
      case a : AssertStmt =>
        rewriteAssert(ufmap, a)
      case d : OrStmt =>
        rewriteOr(ufmap, d)
      case r : RangeStmt =>
        rewriteRange(ufmap, r)
      case constLb : ConstLbStmt =>
        rewriteConstLb(ufmap, constLb)
      case constUb : ConstUbStmt =>
        rewriteConstUb(ufmap, constUb)
      case eq : ConstEqStmt =>
        rewriteConstLb(ufmap, ConstLbStmt(eq.e, eq.v, eq.assump)) ++
        rewriteConstUb(ufmap, ConstUbStmt(eq.e, l.IntLit(eq.v.value + 1), eq.assump))
      case indLb : IndLbStmt =>
        rewriteIndLb(ufmap, indLb)
      case ub : UbStmt =>
        rewriteUb(ufmap, ub)
      case andUb : AndUbStmt =>
        rewriteAndUb(ufmap, andUb)
      case disj : DisjointStmt =>
        rewriteDisjoint(ufmap, disj)
      case inj : InjectivityStmt =>
        rewriteInjectivity(ufmap, inj)
      case _ =>
        throw new AssertionError("Unknown proof statement: " + st.toString())
    }
    l.ASTNode.introducePos(true, true, newStmts, st.position)
  }

  lazy val controlBlock : List[l.GenericProofCommand] = List(
    l.GenericProofCommand(
        l.Identifier("verify"), 
        List.empty, List((l.Identifier("countingProof"), "countingProof")), 
        Some(l.Identifier("v")), None),
    l.GenericProofCommand(
        l.Identifier("check"), 
        List.empty, List.empty, 
        None, None),
    l.GenericProofCommand(
        l.Identifier("print_results"), 
        List.empty, List.empty, 
        None, None),
  )

  lazy val verifyLemmas : List[l.GenericProofCommand] =
    cntProof.lemmas.map(lem => l.GenericProofCommand(
      l.Identifier("verify"),
      List.empty, List((lem.id, lem.id.toString+ " in Lemma block.")),
      None, None))

  def process() : l.Module = {
    val countingOps = identifyCountOps(cntProof.stmts)
    val ufMap = generateCountingOpToUFMap(countingOps)
    val ufDecls = generateUFDecls(ufMap)
    val newProofStmts = cntProof.stmts.flatMap(st => rewriteAssert(ufMap, st))
    val newProofProc = l.ProcedureDecl(
        l.Identifier("countingProof"),
        l.ProcedureSig(List.empty, List.empty),
        l.BlockStmt(List.empty, newProofStmts), 
        List.empty, List.empty, Set.empty, l.ProcedureAnnotations(Set.empty))
    val prevDecls = cntProof.decls.filter(p => !p.isInstanceOf[l.ProcedureDecl])
    val prevProcDecls = cntProof.lemmas
    val moduleP = l.Module(cntProof.id, 
                           prevDecls ++ prevProcDecls ++ ufDecls ++ List(newProofProc),
                            verifyLemmas ++ controlBlock, List.empty)
    println(ufMap.toString())
    println(ufDecls.toString())
    moduleP
  }
}