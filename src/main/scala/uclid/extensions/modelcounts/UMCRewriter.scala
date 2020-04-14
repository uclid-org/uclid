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
  val existingIds = cntProof.decls.map(d => d.declNames).flatten.toSet
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
      if (ufDecl.sig.args.size > 0) {
        l.OperatorApplication(l.ForallOp(ufDecl.sig.args, List.empty), List(e))
      } else {
        e
      }
    }
    ufMap.map {
       p => {
         val ufDecl = p._2
         val innerExpr = geqZero(l.FuncApplication(ufDecl.id, ufDecl.sig.args.map(_._1)))
         val axExpr = quantify(ufDecl, innerExpr)
         val axiomDecl = l.AxiomDecl(Some(generateId("assump")), axExpr, List.empty)
         List(ufDecl, axiomDecl)
       }
    }.flatten.toList
  }

  def extractCountingArgs(e : CountingOp) = {
    e.xs ++ e.ys
  }

  def _apply(uf : l.FunctionDecl) = {
    l.FuncApplication(uf.id, uf.sig.args.map(_._1))
  }
  def rewriteDisjoint(ufMap : UFMap, st : DisjointStmt) : List[l.Statement] = {
    val o1 = st.e1
    val o2 = st.e2
    val o3 = st.e3
    val args = extractCountingArgs(o1)
    val f1 = o1.e
    val f2 = o2.e
    val f3 = o3.e
    val assertExpr = E.and(E.forall(args, E.iff(f1, E.or(f2, f3))),
                          E.forall(args, E.not(E.and(f2, f3))))
    val assertStmt = l.AssertStmt(assertExpr, None, List.empty)
    val ufn1 = _apply(ufMap(o1))
    val ufn2 = _apply(ufMap(o2))
    val ufn3 = _apply(ufMap(o3))
    val assumeExpr = E.forall(args, E.eq(ufn1, E.plus(ufn2, ufn3)))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    List(assertStmt, assumeStmt)
  }
  
  def rewriteRange(ufMap : UFMap, st : RangeStmt) : List[l.Statement] = {
    val args = extractCountingArgs(st.op)
    val ufn = _apply(ufMap(st.op))
    val assumeExpr = E.forall(args, E.eq(ufn, E.max(l.IntLit(0), E.minus(st.ub, st.lb))))
    val assumeStmt = l.AssumeStmt(assumeExpr, None)
    val assertExpr = E.forall(args, E.eq(ufn, st.cnt))
    val assertStmt = l.AssertStmt(assertExpr, None, List.empty)
    List(assumeStmt, assertStmt)
  }
  
  def rewriteAssert(ufmap : UFMap, st : Statement) : List[l.Statement] = {
    st match {
      case d : DisjointStmt =>
        rewriteDisjoint(ufmap, d)
      case r : RangeStmt =>
        rewriteRange(ufmap, r)
      case _ =>
        throw new AssertionError("Unknown proof statement: " + st.toString())
    }
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


  def process() : l.Module = {
    val countingOps = identifyCountOps(cntProof.stmts)
    val ufMap = generateCountingOpToUFMap(countingOps)
    val ufDecls = generateUFDecls(ufMap)
    val newProofStmts = cntProof.stmts.map(st => rewriteAssert(ufMap, st)).flatten
    val newProofProc = l.ProcedureDecl(
        l.Identifier("countingProof"),
        l.ProcedureSig(List.empty, List.empty),
        l.BlockStmt(List.empty, newProofStmts), 
        List.empty, List.empty, Set.empty, l.ProcedureAnnotations(Set.empty))
    val prevDecls = cntProof.decls.filter(p => !p.isInstanceOf[l.ProcedureDecl])
    val moduleP = l.Module(cntProof.id, 
                           prevDecls ++ ufDecls ++ List(newProofProc), 
                           controlBlock, List.empty)
    println(ufMap.toString())
    println(ufDecls.toString())
    moduleP
  }
}