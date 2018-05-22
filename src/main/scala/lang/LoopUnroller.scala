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
 * Author: Pramod Subramanyan

 * Unrolls all for loops.
 *
 */

package uclid
package lang

class FindInnermostLoopsPass extends ReadOnlyPass[Set[ForStmt]] {
  override def applyOnFor(d : TraversalDirection.T, st : ForStmt, in : Set[ForStmt], context : Scope) : Set[ForStmt] = {
    if(!st.body.exists(_.isLoop)) {
      in + st
    } else {
      in
    }
  }
}

class ForLoopRewriterPass(forStmtsToRewrite: Set[ForStmt]) extends RewritePass {
  override def rewriteFor(st: ForStmt, ctx : Scope) : List[Statement] = {
     if (forStmtsToRewrite.contains(st)) {
       val low = st.range._1.asInstanceOf[NumericLit]
       val high = st.range._2.asInstanceOf[NumericLit]
       def rewriteForValue(value : NumericLit) : List[Statement] = {
         val rewriteMap = Map.empty[Expr, Expr] + (st.id -> value)
         val rewriter = new ExprRewriter("ForRewriter(i)", rewriteMap)
         rewriter.rewriteStatements(st.body, ctx)
       }
       (low to high).foldLeft(List.empty[Statement])((acc, i) => acc ++ rewriteForValue(i))
     } else {
       List(st)
     }
  }
}

class ForLoopUnroller extends ASTAnalysis {
  var findInnermostLoopsPass = new FindInnermostLoopsPass()
  var findInnermostLoopsAnalysis = new ASTAnalyzer("ForLoopUnroller.FindInnermostLoops", findInnermostLoopsPass)
  var _astChanged = false
  val MAX_ITERATIONS = 16384

  override def passName = "ForLoopUnroller"
  override def reset() = {
    findInnermostLoopsAnalysis.reset()
  }
  override def visit(module : Module, context : Scope) : Option[Module] = {
    var modP : Option[Module] = Some(module)
    var iteration = 0
    var done = false
    do {
      findInnermostLoopsAnalysis.reset()
      modP match {
        case None =>
          done = true
        case Some(mod) =>
          val innermostLoopSet = findInnermostLoopsAnalysis.visitModule(mod, Set.empty[ForStmt], context)
          done = innermostLoopSet.size == 0
          if (!done) {
            val forLoopRewriter = new ASTRewriter("ForLoopUnroller.LoopRewriter", new ForLoopRewriterPass(innermostLoopSet))
            modP = forLoopRewriter.visit(mod, context)
          }
      }
      iteration = iteration + 1
    } while(!done && iteration < MAX_ITERATIONS)
    Utils.assert(iteration < MAX_ITERATIONS, "Too many rewriting iterations.")
    return modP
  }
}
