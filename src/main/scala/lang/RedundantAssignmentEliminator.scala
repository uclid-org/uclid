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
 * Authors: Pramod Subramanyan
 *
 * Flatten unnecessary BlockStmts.
 *
 */
package uclid
package lang

import com.typesafe.scalalogging.Logger

class RedundantAssignmentEliminatorPass extends RewritePass {
  val log = Logger(classOf[RedundantAssignmentEliminatorPass])
  override def rewriteBlock(blkStmt : BlockStmt, context : Scope) : Option[Statement] = {
    val initWrites : (Map[IdGenerator.Id, Set[Identifier]], Map[Identifier, IdGenerator.Id]) = (Map.empty, Map.empty)
    val (deadWrites, liveWrites) = blkStmt.stmts.foldLeft(initWrites) {
      (writesIn, stmt) => {
        val readSet = StatementScheduler.readSet(stmt, context)
        val liveWritesP1 = writesIn._2 -- readSet
        val writeSet = StatementScheduler.writeSet(stmt, context)
        val deadVariables = (writeSet.map {
          v => liveWritesP1.get(v) match {
            case Some(id) => Some((v, id))
            case None => None
          }
        }).flatten
        val deadWritesP2 = deadVariables.foldLeft(writesIn._1) {
          (acc, p) => {
            acc.get(p._2) match {
              case Some(set) => acc + (p._2 -> (set + p._1))
              case None => acc + (p._2 -> (Set(p._1)))
            }
          }
        }
        val liveWritesP2 = liveWritesP1 ++ (writeSet.map(w => (w, stmt.astNodeId)))
        (deadWritesP2, liveWritesP2)
      }
    }
    val stmtsP = blkStmt.stmts.filter {
      st => {
        val id = st.astNodeId
        deadWrites.get(id) match {
          case Some(vars) =>
            val writes = StatementScheduler.writeSetIds(st, context)
            val b = writes.exists(v => !vars.contains(v))
            if (!b) { log.debug("[DELETING] {}", st.toString()) }
            b
          case None =>
            true
        }
        
      }
    }
    val blkP = BlockStmt(blkStmt.vars, stmtsP)
    if (stmtsP.size < blkStmt.stmts.size) {
      log.debug("Original :\n{}", blkStmt.toString())
      log.debug("Revised  :\n{}", blkP.toString())
    }
    Some(blkP)
  }
}

class RedundantAssignmentEliminator extends ASTRewriter("RedundantAssignmentEliminator", new RedundantAssignmentEliminatorPass())
{
  override val repeatUntilNoChange = true
}
