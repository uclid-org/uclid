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

 * Statement scheduler.
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger

object StatementScheduler {
  lazy val logger = Logger(classOf[StatementScheduler])

  def writeSet(st : Statement, context : Scope) : Set[Identifier] = {
    st match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, _, _) => Set.empty
      case AssumeStmt(e, _) => Set.empty
      case HavocStmt(h) => 
        h match {
          case HavocableId(id) => Set(id)
          case HavocableNextId(id) => Set(id)
          case HavocableFreshLit(_) =>
            throw new Utils.AssertionError("Fresh literals must have been eliminated by now.")
          case HavocableInstanceId(_) => Set.empty
        }
      case AssignStmt(lhss, _) =>
        lhss.map(lhs => lhs match {
          case LhsId(_) | LhsNextId(_) => Some(lhs.ident)
          case _ => None 
        }).flatten.toSet
      case BlockStmt(vars, stmts) =>
        val declaredVars = vars.flatMap(vs => vs.ids.map(v => v)).toSet
        writeSets(stmts, context + vars) -- declaredVars
      case IfElseStmt(_, ifblock, elseblock) =>
        val ifWrites = writeSet(ifblock, context)
        val elseWrites = writeSet(elseblock, context)
        ifWrites.intersect(elseWrites)
      case ForStmt(_, _, _, body) =>
        writeSet(body, context)
      case WhileStmt(_, body, _) =>
        writeSet(body, context)
      case CaseStmt(bodies) =>
        val writeSets = bodies.map(b => writeSet(b._2, context).toSet)
        val allVars = writeSets.foldLeft(Set.empty[Identifier])((acc, set) => acc.union(set))
        writeSets.foldLeft(allVars)((acc, set) => acc.intersect(set))
      case ProcedureCallStmt(id, callLhss, _, instanceId, _) =>
        val module = context.module.get
        val modifies = instanceId match {
          case Some(_) => {
            List.empty
          }
          case None => {
            val procedure = module.procedures.find(p => p.id == id).get
            // val modifies = procedure.modifies
            procedure.modifies.filter(m => m.isInstanceOf[lang.ModifiableId]).asInstanceOf[Set[lang.ModifiableId]].map(m => m.id)
          }
        } 
        val modifiedIdents = callLhss.map(lhs => lhs match {
          case LhsId(_) | LhsNextId(_) => Some(lhs.ident)
          case _ => None 
        }).flatten.toSet
        modifiedIdents ++ modifies.toSet
      case ModuleCallStmt(id) =>
        val namedExprOpt = context.map.get(id)
        Utils.assert(namedExprOpt.isDefined, "Must not haven an unknown instance here: " + id.toString())
        val namedExpr = namedExprOpt.get
        Utils.assert(namedExpr.isInstanceOf[Scope.Instance], "Must be a module instance: " + id.toString())
        val instD = namedExpr.asInstanceOf[Scope.Instance].instD
        instD.outputMap.map(p => p._3.asInstanceOf[Identifier]).toSet
    }
  }
  def writeSets(stmts: List[Statement], context : Scope) : (Set[Identifier]) = {
    stmts.foldLeft(Set.empty[Identifier])((acc, st) => acc ++ writeSet(st, context))
  }

  def writeSetIds(st : Statement, context : Scope) : Set[Identifier] = {
    st match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, _, _) => Set.empty
      case AssumeStmt(e, _) => Set.empty
      case HavocStmt(h) => 
        h match {
          case HavocableId(id) => Set(id)
          case HavocableNextId(id) => Set(id)
          case HavocableFreshLit(_) =>
            throw new Utils.AssertionError("Fresh literals must have been eliminated by now.")
          case HavocableInstanceId(_) => Set.empty
        }
      case AssignStmt(lhss, _) => lhss.map(lhs => lhs.ident).toSet
      case BlockStmt(vars, stmts) =>
        val declaredVars : Set[Identifier] = vars.flatMap(vs => vs.ids.map(v => v)).toSet
        writeSetIds(stmts, context + vars) -- declaredVars
      case IfElseStmt(_, ifblock, elseblock) =>
        writeSetIds(ifblock, context) ++ writeSetIds(elseblock, context)
      case ForStmt(_, _, _, body) =>
        writeSetIds(body, context)
      case WhileStmt(_, body, _) =>
        writeSetIds(body, context)
      case CaseStmt(bodies) =>
        bodies.flatMap(b => writeSetIds(b._2, context)).toSet
      case ProcedureCallStmt(id, callLhss, _, instanceId, _) => 
        val module = context.module.get
        val modifies = instanceId match {
          case Some(_) => {
            // Do nothing; we haven't handled instance proc calls at this point
            List.empty
          }
          case _ => {
            val procedure = module.procedures.find(p => p.id == id).get
            procedure.modifies.filter(m => m.isInstanceOf[lang.ModifiableId]).asInstanceOf[Set[lang.ModifiableId]].map(m => m.id)

          }
        }
        callLhss.map(_.ident).toSet ++ modifies.toSet

      case ModuleCallStmt(id) =>
        val namedExprOpt = context.map.get(id)
        Utils.assert(namedExprOpt.isDefined, "Must not haven an unknown instance here: " + id.toString())
        val namedExpr = namedExprOpt.get
        Utils.assert(namedExpr.isInstanceOf[Scope.Instance], "Must be a module instance: " + id.toString())
        val instD = namedExpr.asInstanceOf[Scope.Instance].instD
        instD.outputMap.map(p => p._3.asInstanceOf[Identifier]).toSet
    }
  }
  def writeSetIds(stmts: List[Statement], context : Scope) : (Set[Identifier]) = {
    stmts.foldLeft(Set.empty[Identifier])((acc, st) => acc ++ writeSetIds(st, context))
  }

  def readSet(e : Expr) : Set[Identifier] = {
    e match {
      case id : Identifier => Set(id)
      case ExternalIdentifier(_, _) => Set.empty
      case _ : Literal => Set.empty
      case Tuple(values) => readSets(values)
      case OperatorApplication(GetNextValueOp(), List(id : Identifier)) => Set(id)
      case OperatorApplication(ArraySelect(inds), exps) => readSets(inds) ++ readSets(exps)
      case OperatorApplication(ArrayUpdate(inds, exp), exps) => readSets(inds) ++ readSet(exp) ++ readSets(exps)
      case OperatorApplication(_, es) => readSets(es)
      case ConstArray(e, _) => readSet(e)
      case FuncApplication(e, args) => readSet(e) ++ readSets(args)
      case Lambda(_, expr) => readSet(expr)
    }
  }
  def readSets(es : List[Expr]) : Set[Identifier] = {
    es.foldLeft(Set.empty[Identifier])((acc, e) => acc ++ readSet(e))
  }
  def readSet(st : Statement, context : Scope) : Set[Identifier] = {
    st match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, _, _) => readSet(e)
      case AssumeStmt(e, _) => readSet(e)
      case HavocStmt(_) => Set.empty
      case AssignStmt(lhss, rhss) =>
      {
        val arrayIndices =
        lhss flatMap {
          case arrayselect : LhsArraySelect => Some(arrayselect.indices)
          case _ => None
        }
        readSets(rhss)++readSets(arrayIndices.flatten)
      }
      case BlockStmt(vars, stmts) =>
        val declaredVars : Set[Identifier] = vars.flatMap(vs => vs.ids.map(v => v)).toSet
        readSets(stmts, context + vars) -- declaredVars
      case IfElseStmt(cond, ifblock, elseblock) =>
        readSet(cond) ++ readSet(ifblock, context) ++ readSet(elseblock, context)
      case ForStmt(_, _, range, body) =>
        readSet(range._1) ++ readSet(range._2) ++ readSet(body, context)
      case WhileStmt(cond, body, _) =>
        readSet(cond) ++ readSet(body, context)
      case CaseStmt(bodies) =>
        bodies.flatMap(b => readSet(b._1) ++ readSet(b._2, context)).toSet
      case ProcedureCallStmt(_, _, args, _, _) =>
        readSets(args)
      case ModuleCallStmt(id) =>
        val namedExprOpt = context.map.get(id)
        Utils.assert(namedExprOpt.isDefined, "Must not haven an unknown instance here: " + id.toString())
        val namedExpr = namedExprOpt.get
        Utils.assert(namedExpr.isInstanceOf[Scope.Instance], "Must be a module instance: " + id.toString())
        val instD = namedExpr.asInstanceOf[Scope.Instance].instD
        val moduleInputs = instD.inputMap.map(p => p._3)
        val moduleSharedVars = instD.sharedVarMap.map(p => p._3)
        logger.trace("moduleInputs: {}", moduleInputs.toString())
        logger.trace("moduleSharedVars: {}", moduleSharedVars.toString())
        readSets(moduleInputs) ++ readSets(moduleSharedVars)
    }
  }
  def readSets(stmts : List[Statement], context : Scope) : (Set[Identifier]) = {
    stmts.foldLeft(Set.empty[Identifier])((acc, st) => acc ++ readSet(st, context))
  }

  def primeReadSet(e : Expr) : Set[Identifier] = {
    e match {
      case Identifier(_) => Set.empty
      case ExternalIdentifier(_, _) => Set.empty
      case _ : Literal => Set.empty
      case Tuple(values) => primeReadSets(values)
      case OperatorApplication(GetNextValueOp(), List(id : Identifier)) => Set(id)
      case OperatorApplication(ArraySelect(inds), exps) => primeReadSets(inds) ++ primeReadSets(exps)
      case OperatorApplication(ArrayUpdate(inds, exp), exps) => primeReadSets(inds) ++ primeReadSet(exp) ++ primeReadSets(exps)
      case OperatorApplication(_, es) => primeReadSets(es)
      case FuncApplication(e, args) => primeReadSet(e) ++ primeReadSets(args)
      case Lambda(_, expr) => primeReadSet(expr)
    }
  }
  def primeReadSets(es : List[Expr]) : Set[Identifier] = {
    es.foldLeft(Set.empty[Identifier])((acc, e) => acc ++ primeReadSet(e))
  }
  def primeReadSet(st : Statement, context : Scope) : Set[Identifier] = {
    st match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, _, _) => primeReadSet(e)
      case AssumeStmt(e, _) => primeReadSet(e)
      case HavocStmt(_) => Set.empty
      case AssignStmt(lhss, rhss) => 
      // this code is not necessary because we do not support updating arrays using an array select e.g., A[i]' = 0
      // but it is added here incase we do support this in future
      {
        val arrayIndices =
        lhss flatMap {
          case arrayselect : LhsArraySelect => Some(arrayselect.indices)
          case _ => None
        }
        primeReadSets(rhss)++primeReadSets(arrayIndices.flatten)
      }
      case BlockStmt(vars, stmts) =>
        val declaredVars : Set[Identifier] = vars.flatMap(vs => vs.ids.map(v => v)).toSet
        primeReadSets(stmts, context + vars) -- declaredVars
      case IfElseStmt(cond, ifblock, elseblock) =>
        primeReadSet(cond) ++ primeReadSet(ifblock, context) ++ primeReadSet(elseblock, context)
      case ForStmt(_, _, range, body) =>
        primeReadSet(range._1) ++ primeReadSet(range._2) ++ primeReadSet(body, context)
      case WhileStmt(cond, body, _) =>
        primeReadSet(cond) ++ primeReadSet(body, context)
      case CaseStmt(bodies) =>
        bodies.flatMap(b => primeReadSet(b._1) ++ primeReadSet(b._2, context)).toSet
      case ProcedureCallStmt(_, _, args, _, _) =>
        primeReadSets(args)
      case ModuleCallStmt(id) =>
        val namedExprOpt = context.map.get(id)
        Utils.assert(namedExprOpt.isDefined, "Must not haven an unknown instance here: " + id.toString())
        val namedExpr = namedExprOpt.get
        Utils.assert(namedExpr.isInstanceOf[Scope.Instance], "Must be a module instance: " + id.toString())
        val instD = namedExpr.asInstanceOf[Scope.Instance].instD
        val moduleInputs = instD.inputMap.map(p => p._3)
        val moduleSharedVars = instD.sharedVarMap.map(p => p._3)
        logger.trace("moduleInputs: {}", moduleInputs.toString())
        logger.trace("moduleSharedVars: {}", moduleSharedVars.toString())
        primeReadSets(moduleInputs) ++ primeReadSets(moduleSharedVars)
    }
  }
  def primeReadSets(stmts : List[Statement], context : Scope) : (Set[Identifier]) = {
    stmts.foldLeft(Set.empty[Identifier])((acc, st) => acc ++ primeReadSet(st, context))
  }


  type StmtDepGraph = Map[Identifier, Set[Identifier]]
  def getReadWriteSets(statements : List[Statement], context : Scope) : List[(Set[Identifier], Set[Identifier])] = {
    statements.map {
      st => {
        val insP = primeReadSet(st, context)
        val outs = writeSetIds(st, context)
        val ins = if (st.hasStmtBlock) {
          insP.diff(outs)
        } else {
          insP
        }
        logger.debug("Statement: {}", st.toString())
        logger.debug("Input Dependencies: {}", ins.toString())
        logger.debug("Output Dependencies: {}", outs.toString())
        (ins, outs)
      }
    }
  }
  def addEdges(graph : StmtDepGraph, deps : List[(Set[Identifier], Set[Identifier])]) : StmtDepGraph = {
    deps.foldLeft(graph) {
      (accSt, dep) => {
        val ins = dep._1
        val outs = dep._2
        outs.foldLeft(accSt) {
          (accId, out) => {
            accId.get(out) match {
              case Some(deps) => accId + (out -> (deps ++ ins))
              case None => accId + (out -> ins)
            }
          }
        }
      }
    }
  }
}

class VariableDependencyFinderPass extends ReadOnlyPass[List[ModuleError]] {
  lazy val logger = Logger(classOf[VariableDependencyFinder])

  type T = List[ModuleError]
  override def applyOnBlock(d : TraversalDirection.T, blockStmt : BlockStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up && context.environment == SequentialEnvironment) {
      checkBlock(blockStmt.stmts, in, context)
    } else {
      in
    }
  }
  def checkBlock(stmts : List[Statement], in : T, context : Scope) : T = {
    val deps = StatementScheduler.getReadWriteSets(stmts, context)
    val graph = StatementScheduler.addEdges(Map.empty, deps)
    val (writeSet, errors) = (stmts zip deps).foldLeft((Set.empty[Identifier], in)) {
      (acc, p) => {
        val (stmt, dep) = p
        val repeatVars = dep._2.intersect(acc._1)
        val errorsP = if (repeatVars.size > 0) {
          val repeatVarsList = repeatVars.toList
          val msg = "Multiple updates to identifier(s): " + Utils.join(repeatVarsList.map(_.toString()), ", ")
          ModuleError(msg, stmt.position) :: acc._2
        } else {
          acc._2
        }
        val vars = acc._1 ++ dep._2
        (vars, errorsP)
      }
    }
    isCyclic(graph, writeSet.toSeq, errors)
  }

  def isCyclic(graph : StatementScheduler.StmtDepGraph, roots : Seq[Identifier], in : T) : T = {
    def cyclicModuleError(node : Identifier, stack : List[Identifier]) : ModuleError = {
      val msg = "Cyclical dependency involving variable(s): " + Utils.join(stack.map(_.toString).toList, ", ")
      ModuleError(msg, node.position)
    }
    val errors = Utils.findCyclicDependencies(graph, roots, cyclicModuleError)
    in ++ errors
  }
}

class VariableDependencyFinder() extends ASTAnalyzer(
    "VariableDependencyFinder", new VariableDependencyFinderPass())
{
  lazy val logger = Logger(classOf[VariableDependencyFinder])

  var cyclicalDependency : Option[Boolean] = None
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, List.empty, context)
    if (out.size > 0) {
      throw new Utils.ParserErrorList(out.map(e => (e.msg, e.position)))
    }
    Some(module)
  }
}

class StatementSchedulerPass extends RewritePass {
  lazy val logger = Logger(classOf[StatementSchedulerPass])
  type StmtDepGraph = Map[IdGenerator.Id, Set[IdGenerator.Id]]
  type IdToStmtMap = Map[Identifier, IdGenerator.Id]

  def reorderStatements(blkStmt: BlockStmt, context : Scope) : BlockStmt = {
    val deps = StatementScheduler.getReadWriteSets(blkStmt.stmts, context + blkStmt.vars)
    val nodeIds = blkStmt.stmts.map(st => st.astNodeId)
    val idToStmtIdMap : IdToStmtMap = (nodeIds zip deps).flatMap(p => p._2._2.map(id => (id -> p._1))).toMap
    val stmtIdToStmtMap : Map[IdGenerator.Id, Statement] = blkStmt.stmts.map(st => (st.astNodeId -> st)).toMap
    logger.debug("Statement Id Map: {}", stmtIdToStmtMap.toString())
    val stmtDepGraph = (blkStmt.stmts zip deps).foldLeft(Map.empty[IdGenerator.Id, Set[IdGenerator.Id]]) {
      (acc, p) => {
        val st = p._1
        val ins = p._2._1
        val outs = p._2._2
        // add an edge from st.astNodeId to each of the statements that produce the ins
        logger.debug("st: {}; ins: {}; outs: {}", st.astNodeId.toString(), ins.toString(), outs.toString())
        val inIds = ins.map(id => idToStmtIdMap.get(id)).flatten
        acc + (st.astNodeId -> inIds)
      }
    }
    logger.debug("stmt dep graph: {}", stmtDepGraph.toString())
    val sortedOrder = Utils.schedule(nodeIds, stmtDepGraph)
    logger.debug("sortedOrder: {}", sortedOrder.toString())
    BlockStmt(blkStmt.vars, sortedOrder.map(id => stmtIdToStmtMap.get(id).get))
  }
  override def rewriteNext(next : NextDecl, context : Scope) : Option[NextDecl] = {
    val bodyP = reorderStatements(BlockStmt(List.empty, List(next.body)), context).stmts
    logger.debug(Utils.join(bodyP.flatMap(st => st.toLines), "\n"))
    Some(NextDecl(BlockStmt(List.empty, bodyP)))
  }
  override def rewriteBlock(blk : BlockStmt, context : Scope) : Option[Statement] = {
    if (context.environment == SequentialEnvironment) {
      val stmtsP = reorderStatements(BlockStmt(blk.vars, blk.stmts), context + blk.vars)
      Some(stmtsP)
    } else {
      Some(blk)
    }
  }
  override def rewriteHavoc(havocStmt : HavocStmt, context : Scope) : Option[Statement] = {
    if (context.environment == SequentialEnvironment) {
      havocStmt.havocable match {
        case HavocableId(id) => Some(HavocStmt(HavocableNextId(id)))
        case _ => Some(havocStmt)
      }
    } else {
      Some(havocStmt)
    }
  }
}

class StatementScheduler extends ASTRewriter("StatementScheduler", new StatementSchedulerPass())
