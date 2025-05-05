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
import java.util.jar.Attributes.Name


class BlockVariableRenamerPass extends RewritePass {
  def renameVarList (vars : List[(Identifier, Type)], context : Scope) : List[(Identifier, Identifier, Type)] = {
    vars.map {
      p => {
        if (context.map.contains(p._1)) {
          (p._1, NameProvider.get("block_rename"), p._2)
        } else {
          (p._1, p._1, p._2)
        }
      }
    }
  }
  def getRewriteMap(varTuples : List[(Identifier, Identifier, Type)]) : Map[Expr, Expr] = {
    varTuples.filter(p => (p._1 != p._2)).map(p => p._1 -> p._2).toMap
  }
  override def rewriteBlock(blkStmt : BlockStmt, context : Scope) : Option[Statement] = {
    val blkVars = blkStmt.vars.map(p => p.ids.map(id => (id, p.typ))).flatMap(v => v)
    val varTuples = renameVarList(blkVars, context)
    val rewriteMap = getRewriteMap(varTuples)
    val rewriter = new ExprRewriter("BlockVariableRenamerPass:Block", rewriteMap)
    val statementsP = rewriter.rewriteStatements(blkStmt.stmts, context + blkStmt.vars)
    val varsP = varTuples.map(p => BlockVarsDecl(List(p._2), p._3))
    Some(BlockStmt(varsP, statementsP, blkStmt.isProcedural))
  }
  override def rewriteProcedure(proc : ProcedureDecl, context : Scope) : Option[ProcedureDecl] = {
    val argTuples = renameVarList(proc.sig.inParams, context)
    val returnTuples = renameVarList(proc.sig.outParams, context)
    val contextP = context + proc
    val varTuples = argTuples ++ returnTuples
    val rewriteMap = getRewriteMap(varTuples)
    val rewriter = new ExprRewriter("BlockVariableRenamerPass:Procedure", rewriteMap)
    // construction of new procedure.
    val inParamsP = argTuples.map(p => (p._2, p._3))
    val outParamsP = returnTuples.map(p => (p._2, p._3))
    val sigP = ProcedureSig(inParamsP, outParamsP)
    val requiresP = proc.requires.map(req => rewriter.rewriteExpr(req, context))
    val ensuresP = proc.ensures.map(ens => rewriter.rewriteExpr(ens, context))
    val bodyP = rewriter.rewriteStatement(proc.body, contextP).get
    val procP = ProcedureDecl(proc.id, sigP, bodyP, requiresP, ensuresP, proc.modifies, proc.annotations)
    Some(procP)
  }
  override def rewriteFunction(func : FunctionDecl, context : Scope) : Option[FunctionDecl] = {
    val varTuples = renameVarList(func.sig.args, context)
    val contextP = context + func.sig
    val rewriteMap = getRewriteMap(varTuples)
    val rewriter = new ExprRewriter("BlockVariableRenamerPass:Function", rewriteMap)
    val argsP = func.sig.args.map(arg => (rewriter.rewriteExpr(arg._1, contextP).asInstanceOf[Identifier], arg._2))
    val sigP = FunctionSig(argsP, func.sig.retType)
    val funcP = FunctionDecl(func.id, sigP)
    Some(funcP)
  }

  override def rewriteDefine(defDecl : DefineDecl, context : Scope) : Option[DefineDecl] = {
    val varTuples = renameVarList(defDecl.sig.args, context)
    val contextP = context + defDecl.sig
    val rewriteMap = getRewriteMap(varTuples)
    val rewriter = new ExprRewriter("BlockVariableRenamerPass:Define", rewriteMap)
    val argsP = defDecl.sig.args.map(arg => (rewriter.rewriteExpr(arg._1, contextP).asInstanceOf[Identifier], arg._2))
    val sigP = FunctionSig(argsP, defDecl.sig.retType)
    val bodyP = rewriter.rewriteExpr(defDecl.expr, contextP)
    val defP = DefineDecl(defDecl.id, sigP, bodyP) 
    Some(defP)
  }
}

object BlockVariableRenamer {
  var count = 0
  def getName() : String = {
    count += 1
    "BlockVariableRenamer:" + count.toString()
  }
}

class BlockVariableRenamer extends ASTRewriter(
    BlockVariableRenamer.getName(), new BlockVariableRenamerPass())

class BlockFlattenerPass extends RewritePass {
  lazy val logger = Logger(classOf[BlockFlattenerPass])
  
  def renameBlock(blk : BlockStmt, context : Scope, mapIn : Map[Identifier, Type]) : (List[Statement], Map[Identifier, Type]) = {
    val blkVars = blk.vars.flatMap(vs => vs.ids.map(v => (v, vs.typ)))
    val renaming = blkVars.foldLeft(Map.empty[Identifier, (Identifier, Type)]) {
      (map, vDec) => {
        if (context.map.get(vDec._1).isEmpty && !mapIn.contains(vDec._1)) {
          map + (vDec._1 -> (vDec._1, vDec._2))
        } else {
          val newId = NameProvider.get("blk")
          map + (vDec._1 -> (newId, vDec._2))
        }
      }
    }
    val rewriteMap = renaming.filter(p => p._1 != p._2._1).map(p => p._1.asInstanceOf[Expr] -> p._2._1)
    val varDecls = mapIn ++ renaming.map(p => p._2._1 -> p._2._2).toMap
    val rewriter = new ExprRewriter("BlockFlattener:Rewrite", rewriteMap)
    val stmtsP = rewriter.rewriteStatements(blk.stmts, context + blk.vars)
    (stmtsP, varDecls)
  }

  def addConcurrentVars (blkStmt : BlockStmt, context: Scope) : BlockStmt = {
    val filteredStmts = blkStmt.stmts.filter(_.isInstanceOf[BlockStmt])

    if(filteredStmts.size != blkStmt.stmts.size)
      logger.debug("BlockFlattener: block contains blk statements and other statements")

    val nonSequentialBlockCount = filteredStmts.count(_.asInstanceOf[BlockStmt].isProcedural == false)
    logger.debug("Number of blocks: " + filteredStmts.size.toString())
    
    if(!blkStmt.isProcedural && filteredStmts.size >1)
    {
      val reads = filteredStmts.foldLeft(Set.empty[Identifier]) {
        (acc, blk) => {
          val readSet = StatementScheduler.readSets(blk.asInstanceOf[BlockStmt].stmts, context)
          acc ++ readSet
        }
      }.filter(id => context.map.contains(id) && context.map(id).isInstanceOf[Scope.StateVar] && !id.name.startsWith("__ucld"))

      val writes = filteredStmts.foldLeft(Set.empty[Identifier]) {
        (acc, blk) => {
          val writeSet = StatementScheduler.writeSets(blk.asInstanceOf[BlockStmt].stmts, context)
          acc ++ writeSet
        }
      }.filter(id => context.map.contains(id) && context.map(id).isInstanceOf[Scope.StateVar])

      // create new vars. We only need new variables for the reads that are also written to 
      // because there should only be
      // one write to a variable in a concurrent block. Blocks with more than one write will have been
      // caught earlier
      val varPairs: Map[Expr, Expr] =
        reads.intersect(writes).map(
        id => (id.asInstanceOf[Expr] -> NameProvider.get("block_" + id.toString()).asInstanceOf[Expr])).toMap
      logger.debug("New vars: " + varPairs.toString())

      val rewriter = new ReadSetExprRewriter("BlockFlattener:Rewrite", varPairs)
      val stmtsP = rewriter.rewriteStatements(blkStmt.stmts, context + blkStmt.vars)

      // create variable declarations for the new read variables.
      val vars = varPairs.map(p => BlockVarsDecl(List(p._2.asInstanceOf[Identifier]), context.map(p._1.asInstanceOf[Identifier]).asInstanceOf[Scope.StateVar].typ))
      // create assign statements for the new variables
      val readVarAssigns = varPairs.map(p => AssignStmt(List(LhsId(p._2.asInstanceOf[Identifier])), List(p._1.asInstanceOf[Expr]))).toList

      // new block statement
      val blkStmtP = BlockStmt(blkStmt.vars ++ vars, readVarAssigns ++ stmtsP, blkStmt.isProcedural)
      logger.debug("New block statement:\n" + blkStmtP.toString())
      blkStmtP
    }
    else{
      blkStmt
    }
  }

  override def rewriteBlock(blkStmt : BlockStmt, context : Scope) : Option[Statement] = {
    logger.debug("==> [%s] Input:\n%s".format(analysis.passName, blkStmt.toString()))
    val init = (List.empty[Statement], Map.empty[Identifier, Type])

    val blkStmtP = addConcurrentVars(blkStmt, context)
    val (stmtsP, mapOut) = blkStmtP.stmts.foldLeft(init) {
      (acc, st) => {
        val (stP, mapOut) = st match {
          case blk : BlockStmt => renameBlock(blk, context, acc._2)
          case _ => (List(st), acc._2)
        }
        (acc._1 ++ stP, mapOut)
      }
    }

    val vars = mapOut.map(p => BlockVarsDecl(List(p._1), p._2))
    val result = BlockStmt(blkStmtP.vars ++ vars, stmtsP, blkStmt.isProcedural)
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