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

  /** Identify counting ops in a sequence of expressions.
   *  
   *  Note the recursion is to identifyCountOps which is a Memo.
   */
  def _identifyCountOps(es : Seq[l.Expr]) : Set[l.OperatorApplication] = {
    es.foldLeft(Set.empty[l.OperatorApplication]) {
      (acc, e) => acc ++ identifyCountOps(e)
    }
  }
  /** Identify counting ops in an expression.
   *  
   *  Note recursion is to identifyCountsOp which is a memo.
   */
  def _identifyCountOps(e : l.Expr) : Set[l.OperatorApplication] = {
    e match {
      case _ : l.Identifier | _ : l.ExternalIdentifier | _ : l.Literal =>
        Set.empty
      case l.ConstArray(e, typ) =>
        identifyCountOps(e)
      case l.Tuple(es) =>
        _identifyCountOps(es)
      case opapp : l.OperatorApplication =>
        val init : Set[l.OperatorApplication] = opapp.op match {
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
  val identifyCountOps = new Memo[l.Expr, Set[l.OperatorApplication]](_identifyCountOps _)

  /** Finding all the counting operators in a list of assert statements. */
  def identifyCountOps(proofBlk: List[l.AssertStmt]) : Set[l.OperatorApplication] = {
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
  def generateUFDecls(ops : Set[l.OperatorApplication]) : (Map[l.OperatorApplication, l.FunctionDecl]) = {
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
  
  def process() : l.Module = {
    val proofProcBody = module.procedures(0).body.asInstanceOf[l.BlockStmt].stmts.map(_.asInstanceOf[l.AssertStmt])
    val countingOps = identifyCountOps(proofProcBody)
    val ufDecls = generateUFDecls(countingOps)
    println(ufDecls.toString())
    module
  }
}