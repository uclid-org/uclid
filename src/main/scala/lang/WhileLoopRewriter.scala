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

 * Rewrites while loops.
 *
 */

package uclid
package lang

class WhileLoopRewriterPass extends RewritePass {
  override def rewriteWhile(whileSt : WhileStmt, context: Scope) : List[Statement] = {
    val cond = whileSt.cond
    val body = whileSt.body
    val invs = whileSt.invariants
    val initialAsserts = invs.map{
      inv => {
        ASTNode.introducePos(true, true, AssertStmt(inv, Some(Identifier("loop invariant (entry)"))), inv.position)
      }
    }
    val varsToHavoc = StatementScheduler.writeSets(whileSt.body, context).toList
    val havocStmts = varsToHavoc.map(v => HavocStmt(HavocableId(v)))
    val assumeStmts = invs.map(inv => AssumeStmt(inv, None))
    val assertStmts = invs.map{
      inv => {
        ASTNode.introducePos(true, true, AssertStmt(inv, Some(Identifier("loop invariant (iteration)"))), inv.position)
      }
    }
    val finishAssump = AssumeStmt(Operator.not(cond), None)
    val ifBody = havocStmts ++ assumeStmts ++ body ++ assertStmts
    val ifElseStmt = IfElseStmt(cond, ifBody, List.empty)
    initialAsserts ++ List(ifElseStmt, finishAssump)
  }
}

class WhileLoopRewriter extends ASTRewriter(
    "WhileLoopRewriter", new WhileLoopRewriterPass())
{
}