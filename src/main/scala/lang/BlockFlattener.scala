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

class BlockFlattenerPass extends RewritePass {
  lazy val logger = Logger(classOf[BlockFlattenerPass])

  override def rewriteBlock(blkStmt : BlockStmt, context : Scope) : Option[Statement] = {
    logger.debug("Input:\n" + blkStmt.toString())
    val stmtsP = blkStmt.stmts.flatMap {
      (st) => {
        st match {
          case BlockStmt(vs, stmts) => 
            if(vs.size == 0) {
              stmts
            } else {
              List(st)
            }
          case _ => List(st)
        }
      }
    }
    val result = if (blkStmt.vars.size == 0) {
      stmtsP.size match {
        case 0 => SkipStmt()
        case 1 => stmtsP(0)
        case _ => BlockStmt(blkStmt.vars, stmtsP)
      }
    } else {
      BlockStmt(blkStmt.vars, stmtsP)
    }
    logger.debug("Result:\n" + result.toString())
    Some(result)
  }
}

object BlockFlattener {
  var index = 0
  def getName() : String = {
    index += 1
    "BlockFlattener:" + index.toString()
  }
}

class BlockFlattener() extends ASTRewriter(BlockFlattener.getName(), new BlockFlattenerPass())
{
  override val repeatUntilNoChange = true
}

object Optimizer {
  var index = 0
  def getName() : String = {
    index += 1
    "Optimizer:" + index.toString()
  }
}

class DummyPass extends RewritePass
class Optimizer extends ASTRewriter(Optimizer.getName(), new DummyPass())
{
  val blockRewriter = new BlockFlattener()
  val redundantAssignmentEliminator = new RedundantAssignmentEliminator()
  override def visitModule(module: Module, context: Scope) : Option[Module] = {
    blockRewriter.visitModule(module, context).flatMap {
      m => redundantAssignmentEliminator.visitModule(m, context)
    }
  }
}