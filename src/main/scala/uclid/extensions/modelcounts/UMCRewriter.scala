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

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}
 
class UMCRewriter(module : l.Module) {
  val proofProcedure = module.procedures(0)
  
  /* We will be using this set in a number of places. */
  type CountingOpSet = Set[l.OperatorApplication]
  /* A map from counting ops to the UFs that represent them. */
  type UFMap = Map[l.OperatorApplication, l.FunctionDecl]
  

  /** Identify counting ops in a sequence of expressions.
   *  
   *  Note the recursion is to identifyCountOps which is a Memo.
   */
  def _identifyCountOps(es : Seq[l.Expr]) : CountingOpSet = {
    es.foldLeft(Set.empty[l.OperatorApplication]) {
      (acc, e) => acc ++ identifyCountOps(e)
    }
  }
  /** Identify counting ops in an expression.
   *  
   *  Note recursion is to identifyCountsOp which is a memo.
   */
  def _identifyCountOps(e : l.Expr) : CountingOpSet = {
    e match {
      case _ : l.Identifier | _ : l.ExternalIdentifier | _ : l.Literal =>
        Set.empty
      case l.ConstArray(e, typ) =>
        identifyCountOps(e)
      case l.Tuple(es) =>
        _identifyCountOps(es)
      case opapp : l.OperatorApplication =>
        val init : CountingOpSet = opapp.op match {
          case l.CountingOp(_, _) => Set(opapp)
          case _ => Set.empty
        }
        init ++ _identifyCountOps(opapp.operands)
      case l.FuncApplication(e, args) =>
        identifyCountOps(e) ++ _identifyCountOps(args)
      case l.Lambda(ids, e) =>
        identifyCountOps(e)
    }
  }

  /**
   * Memoizing wrapper for finding all counting operators.
   */
  val identifyCountOps = new Memo[l.Expr, CountingOpSet](_identifyCountOps _)

  /** Finding all the counting operators in a list of assert statements. */
  def identifyCountOps(proofBlk: List[l.AssertStmt]) : CountingOpSet = {
    proofBlk.foldLeft(Set.empty[l.OperatorApplication]) {
      (acc, st) => acc ++ identifyCountOps(st.e)
    }
  }

  /** Identifiers that are already declared in the module. */
  val existingIds = module.decls.map(d => d.declNames).flatten.toSet
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
      opapp => {
        assert (opapp.op.isInstanceOf[l.CountingOp])
        val op = opapp.op.asInstanceOf[l.CountingOp]
        val ufId = generateId("count")
        val sig = l.FunctionSig(op.ys, l.IntegerType())
        val uf = l.FunctionDecl(ufId, sig)
        opapp -> uf
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
  
  def process() : l.Module = {
    val proofProcBody = module.procedures(0).body.asInstanceOf[l.BlockStmt].stmts.map(_.asInstanceOf[l.AssertStmt])
    val countingOps = identifyCountOps(proofProcBody)
    val ufMap = generateCountingOpToUFMap(countingOps)
    val ufDecls = generateUFDecls(ufMap)
    val moduleP = l.Module(module.id, module.decls ++ ufDecls, module.cmds, module.notes)
    println(ufMap.toString())
    println(ufDecls.toString())
    moduleP
  }
}