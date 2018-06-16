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
  var nameProvider = new ContextualNameProvider("")
  
  override def reset() {
    nameProvider = new ContextualNameProvider("")
  }

  def renameBlock(blk : BlockStmt, context : Scope, nameProvider : ContextualNameProvider) : (List[Statement], List[(Identifier, Type)]) = {
    val blkVars = blk.vars.flatMap(vs => vs.ids.map(v => (v, vs.typ)))
    val renaming = blkVars.foldLeft(Map.empty[Identifier, (Identifier, Type)]) {
      (map, vDec) => {
        if (context.map.get(vDec._1).isEmpty && !nameProvider.names.contains(vDec._1)) {
          nameProvider.names.add(vDec._1)
          map + (vDec._1 -> (vDec._1, vDec._2))
        } else {
          val newId = nameProvider(context, vDec._1, "")
          map + (vDec._1 -> (newId, vDec._2))
        }
      }
    }
    val rewriteMap = renaming.filter(p => p._1 != p._2._1).map(p => p._1.asInstanceOf[Expr] -> p._2._1)
    val varDecls = renaming.map(p => p._2).toList
    val rewriter = new ExprRewriter("BlockFlattener:Rewrite", rewriteMap)
    val stmtsP = rewriter.rewriteStatements(blk.stmts, context + blk.vars)
    (stmtsP, varDecls)
  }
  override def rewriteBlock(blkStmt : BlockStmt, context : Scope) : Option[Statement] = {
    logger.debug("==> [%s] Input:\n%s".format(analysis.passName, blkStmt.toString()))
    val stmtM1 = blkStmt.stmts.map {
      (st) => {
        st match {
          case blk : BlockStmt => renameBlock(blk, context, nameProvider)
          case _ => (List(st), List.empty)
        }
      }
    }
    val stmts = stmtM1.map(p => p._1).flatMap(st => st)
    val vars = stmtM1.map(p => p._2).flatMap(vs => vs.map(p => BlockVarsDecl(List(p._1), p._2)))
    val result = BlockStmt(blkStmt.vars ++ vars, stmts)
    logger.debug("<== Result:\n" + result.toString())
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
      m => {
        redundantAssignmentEliminator.visitModule(m, context)
      }
    }
  }
}