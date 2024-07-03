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
 * Author : Alejandro Sanchez Ocegueda
 * 
 * Inserts an 'assert false' statement at the end of each (nonempty) basic block.
 * This is a sanity check for unreachable code.
 * Note: Smoke testing should not be used with LTL properties yet.
 * 
 */

package uclid
package lang

class SmokeInsertPass() extends RewritePass {
  
  var smokeCount = 1
  override def rewriteBlock(st : BlockStmt, ctx : Scope) : Option[Statement] = {

    if (st.stmts.length == 1) {
      val line = st.stmts(0).pos.line
      var assertFalse = AssertStmt(BoolLit(false), Some(Identifier(s"line %d".format(line))))
      assertFalse.setPos(st.stmts(0).pos)
      val newstmts = st.stmts :+ assertFalse 
      smokeCount += 1
      Some(BlockStmt(st.vars, newstmts, st.isProcedural))
    } else if (st.stmts.length > 1) {
      val topLine = st.stmts(0).pos.line
      val bottomLine = st.stmts(st.stmts.length-1).pos.line
      var assertFalse = AssertStmt(BoolLit(false), Some(Identifier(s"lines %d-%d".format(topLine, bottomLine))))
      assertFalse.setPos(st.stmts(st.stmts.length-1).pos)
      val newstmts = st.stmts :+ assertFalse 
      smokeCount += 1
      Some(BlockStmt(st.vars, newstmts, st.isProcedural))
    } else {
      Some(st)
    }

  } 
    
}


class SmokeInserter() extends ASTRewriter(
  "SmokerInserter", new SmokeInsertPass()
)
