/*
 * UCLID5 Verification and Synthesis Engine
 * 
 * Copyright (c) 2017. The Regents of the University of California (Regents). 
 * All Rights Reserved. 
 * 
 * Permission to use, copy, modify, and distribute this software
 * and its documentation for educational, research, and not-for-profit purposes,
 * without fee and without a signed licensing agreement, is hereby granted,
 * provided that the above copyright notice, this paragraph and the following two
 * paragraphs appear in all copies, modifications, and distributions. 
 * 
 * Contact The Office of Technology Licensing, UC Berkeley, 2150 Shattuck Avenue,
 * Suite 510, Berkeley, CA 94720-1620, (510) 643-7201, otl@berkeley.edu,
 * http://ipira.berkeley.edu/industry-info for commercial licensing opportunities.
 * 
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
 * INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING OUT OF
 * THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS
 * PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 * 
 * Author: Pramod Subramanyan

 * Unrolls all for loops.
 *
 */

package uclid
package lang

class FindInnermostLoopsPass extends ReadOnlyPass[Set[ForStmt]] {
  override def applyOnFor(d : TraversalDirection.T, st : ForStmt, in : Set[ForStmt], context : ScopeMap) : Set[ForStmt] = {
    if(!st.body.exists(_.isLoop)) {
      in + st
    } else {
      in
    }
  }
}

class ForLoopRewriterPass(forStmtsToRewrite: Set[ForStmt]) extends RewritePass {
  override def rewriteFor(st: ForStmt, ctx : ScopeMap) : List[Statement] = {
     if (forStmtsToRewrite.contains(st)) {
       val low = st.range._1
       val high = st.range._2
       def rewriteForValue(value : NumericLit) : List[Statement] = {
         val rewriteMap = Map.empty[Expr, Expr] + (st.id -> value)
         val rewriter = new ExprRewriter("ForRewriter(i)", rewriteMap)
         rewriter.rewriteStatements(st.body)
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
  def visit(module : Module) : Option[Module] = {
    var modP : Option[Module] = Some(module)
    var iteration = 0
    var done = false
    do {
      findInnermostLoopsAnalysis.reset()
      modP match {
        case None => 
          done = true
        case Some(mod) =>
          val innermostLoopSet = findInnermostLoopsAnalysis.visitModule(mod, Set.empty[ForStmt])
          // println("Innermost loops: " + innermostLoopSet.toString)
          done = innermostLoopSet.size == 0
          if (!done) {
            val forLoopRewriter = new ASTRewriter("ForLoopUnroller.LoopRewriter", new ForLoopRewriterPass(innermostLoopSet))
            modP = forLoopRewriter.visit(mod)
            // if(!modP.isEmpty) {
            //  println("** AFTER UNROLLING **")
            //  println(modP.get)
            // }
          }
      }
      iteration = iteration + 1
    } while(!done && iteration < MAX_ITERATIONS)
    Utils.assert(iteration < MAX_ITERATIONS, "Too many rewriting iterations.")
    return modP
  }
}