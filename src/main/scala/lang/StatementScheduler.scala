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
 * Authors: Rohit Sinha, Pramod Subramanyan

 * Statement scheduler.
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger

object StatementScheduler {
  def extractId(n : Expr) : Identifier = {
    n match {
      case OperatorApplication(GetNextValueOp(), List(id : Identifier)) => id
      case _ => throw new Utils.AssertionError("Unexpected value where primed identifier was expected.")
    }
  }

  def writeSet(st : Statement, context : Scope) : Set[Identifier] = {
    st match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, _) => Set.empty
      case AssumeStmt(e, _) => Set.empty
      case HavocStmt(h) => 
        h match {
          case HavocableId(id) => Set(id)
          case HavocableFreshLit(f) =>
            throw new Utils.AssertionError("Fresh literals must have been eliminated by now.")
        }
      case AssignStmt(lhss, rhss) => lhss.map(lhs => lhs.ident).toSet
      case IfElseStmt(cond, ifblock, elseblock) =>
        writeSets(ifblock, context) ++ writeSets(elseblock, context)
      case ForStmt(_, _, body) =>
        writeSets(body, context)
      case CaseStmt(bodies) =>
        bodies.flatMap(b => writeSets(b._2, context)).toSet
      case ProcedureCallStmt(id, callLhss, args) => callLhss.map(_.ident).toSet
      case ModuleCallStmt(id) =>
        val namedExprOpt = context.map.get(id)
        Utils.assert(namedExprOpt.isDefined, "Must not haven an unknown instance here: " + id.toString())
        val namedExpr = namedExprOpt.get
        Utils.assert(namedExpr.isInstanceOf[Scope.Instance], "Must be a module instance: " + id.toString())
        val instD = namedExpr.asInstanceOf[Scope.Instance].instD
        val moduleType : ModuleType = instD.modType.get.asInstanceOf[ModuleType]
        instD.outputMap.map(p => extractId(p._3)).toSet
    }
  }

  def writeSets(stmts: List[Statement], context : Scope) : (Set[Identifier]) = {
    stmts.foldLeft(Set.empty[Identifier])((acc, st) => acc ++ writeSet(st, context))
  }

  def readSet(st : Statement, context : Scope) : Set[Identifier] = {
    st match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, _) => Set.empty
      case AssumeStmt(e, _) => Set.empty
      case HavocStmt(h) => Set.empty
      case AssignStmt(lhss, rhss) => readSets(rhss)
      case IfElseStmt(cond, ifblock, elseblock) =>
        readSet(cond) ++ readSets(ifblock, context) ++ readSets(elseblock, context)
      case ForStmt(_, _, body) =>
        readSets(body, context)
      case CaseStmt(bodies) =>
        bodies.flatMap(b => readSets(b._2, context)).toSet
      case ProcedureCallStmt(_, lhss, args) =>
        readSets(args)
      case ModuleCallStmt(id) =>
        val namedExprOpt = context.map.get(id)
        Utils.assert(namedExprOpt.isDefined, "Must not haven an unknown instance here: " + id.toString())
        val namedExpr = namedExprOpt.get
        Utils.assert(namedExpr.isInstanceOf[Scope.Instance], "Must be a module instance: " + id.toString())
        val instD = namedExpr.asInstanceOf[Scope.Instance].instD
        val moduleType : ModuleType = instD.modType.get.asInstanceOf[ModuleType]
        readSets(instD.inputMap.map(p => p._3)) ++ readSets(instD.sharedVarMap.map(p => p._3))
    }
  }

  def readSets(stmts : List[Statement], context : Scope) : (Set[Identifier]) = {
    stmts.foldLeft(Set.empty[Identifier])((acc, st) => acc ++ readSet(st, context))
  }

  def readSets(es : List[Expr]) : Set[Identifier] = {
    es.foldLeft(Set.empty[Identifier])((acc, e) => acc ++ readSet(e))
  }

  def readSet(e : Expr) : Set[Identifier] = {
    e match {
      case Identifier(_) => Set.empty
      case ExternalIdentifier(_, _) => Set.empty
      case lit : Literal => Set.empty
      case Tuple(values) => readSets(values)
      case OperatorApplication(GetNextValueOp(), List(id : Identifier)) => Set(id)
      case OperatorApplication(_, es) => readSets(es)
      case ArraySelectOperation(e, index) => readSet(e) ++ readSets(index)
      case ArrayStoreOperation(e, index, value) => readSet(e) ++ readSets(index) ++ readSet(value)
      case FuncApplication(e, args) => readSet(e) ++ readSets(args)
      case Lambda(ids, expr) => readSet(expr)
    }
  }
}

class VariableDependencyFinderPass extends ReadOnlyPass[(Map[Identifier, Set[Identifier]], List[Identifier])] {
  lazy val logger = Logger(classOf[VariableDependencyFinder])

  type T = (Map[Identifier, Set[Identifier]], List[Identifier])
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      val ctxP = context + module
      val graph1 = addEdges(in._1, module.init.get.body, ctxP)
      val graph2 = addEdges(graph1, module.next.get.body, ctxP)
      (graph2, module.vars.map(v => v._1) ++ module.outputs.map(v => v._1))
    } else {
      in
    }
  }
  def addEdges(graph : Map[Identifier, Set[Identifier]], statements : List[Statement], context : Scope) : Map[Identifier, Set[Identifier]] = {
    statements.foldLeft(graph) {
      (accSt, st) => {
        val ins = StatementScheduler.readSet(st, context)
        val outs = StatementScheduler.writeSet(st, context)
        logger.debug("Statement: {}", st.toString())
        logger.debug("Input Dependencies: {}", ins.toString())
        logger.debug("Output Dependencies: {}", ins.toString())
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

class VariableDependencyFinder() extends ASTAnalyzer(
    "VariableDependencyFinder", new VariableDependencyFinderPass())
{
  lazy val logger = Logger(classOf[VariableDependencyFinder])

  var cyclicalDependency : Option[Boolean] = None
  override def reset() {
    in = Some(Map.empty[Identifier, Set[Identifier]], List.empty[Identifier])
  }

  override def finish() {
    val depGraph = out.get._1
    val variables = out.get._2
    logger.debug("Dependency graph: {}", depGraph.toString())
    def cyclicModuleError(node : Identifier, stack : List[Identifier]) : ModuleError = {
      val msg = "Cyclical dependency among variables: " + Utils.join(stack.map(_.toString).toList, ", ")
      ModuleError(msg, node.position)
    }
    val errors = Utils.findCyclicDependencies(depGraph, variables, cyclicModuleError)
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
  }
}
