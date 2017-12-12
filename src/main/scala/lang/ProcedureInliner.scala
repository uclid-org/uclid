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

 * Inlines all procedure calls.
 *
 * FIXME: Need to check for the absence of recursion.
 */

package uclid
package lang

import scala.collection.mutable.{Set => MutableSet}
import scala.collection.immutable.{Set => Set}

class FindProcedureDependencyPass extends ReadOnlyPass[Map[Identifier, Set[Identifier]]] {
  type T = Map[Identifier, Set[Identifier]]
  override def applyOnProcedureCall(d : TraversalDirection.T, proc : ProcedureCallStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      context.procedure match {
        case Some(proc) =>
          in.get(proc.id) match {
            case Some(procedures) => in + (proc.id -> (procedures + proc.id))
            case None => in + (proc.id -> Set(proc.id))
          }
        case None => in
      }
    } else {
      in
    }
  }
}

class FindProcedureDependency extends ASTAnalyzer("FindProcedureDependency", new FindProcedureDependencyPass())
{
  var moduleInstantiationOrder : Option[List[Identifier]] = None
  var cyclicalDependency : Option[Boolean] = None
  override def reset() {
    in = Some(Map.empty[Identifier, Set[Identifier]])
  }

  override def visit(module : Module, context : Scope) : Option[Module] = {
    val procDepGraph = visitModule(module, Map.empty[Identifier, Set[Identifier]], context)
    // val procInliningOrder = Some(Utils.topoSort(mainModuleName, depGraph))
    Some(module)
  }
  /*
  override def finish() {
    val depGraph = out.get
    def cyclicModuleError(node : Identifier, stack : Set[Identifier]) : ModuleError = {
      val msg = "Cyclical dependency among modules: " + Utils.join(stack.map(_.toString).toList, ", ") + "."
      ModuleError(msg, node.position)
    }
    val errors = Utils.findCyclicDependencies(depGraph, mainModuleName, cyclicModuleError)
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
  }
  * 
  */
}

class FindLeafProcedurePass extends ReadOnlyPass[Set[Identifier]] {
  type T = Set[Identifier]
  override def applyOnProcedureCall(d : TraversalDirection.T, st : ProcedureCallStmt, in : T, ctx : Scope) : T = {
    ctx.procedure match {
      case Some(proc) => in - proc.id
      case None => in
    }
  }
}

class InlineProcedurePass(proc : ProcedureDecl) extends RewritePass {
  type UniqueNameProvider = (Identifier, String) => Identifier
  override def rewriteProcedure(p : ProcedureDecl, ctx : Scope) : Option[ProcedureDecl] = {
    if (p.id == proc.id) return None

    val nameProvider = new ContextualNameProvider(ctx + p, "proc$" + p.id + "$" + proc.id)
    val (stmts, newVars) = inlineProcedureCalls((id, p) => nameProvider(id, p), p.body)
    val newDecls = newVars.map((t) => LocalVarDecl(t._1, t._2))
    return Some(ProcedureDecl(p.id, p.sig, p.decls ++ newDecls, stmts, proc.requires, proc.ensures, proc.modifies))
  }

  override def rewriteModule(m : Module, ctx : Scope) : Option[Module] = {
    val initNameProvider = new ContextualNameProvider(ctx, "init$" + proc.id)
    val nextNameProvider = new ContextualNameProvider(ctx, "next$" + proc.id)

    val decls = m.decls.foldLeft((List.empty[Decl], List.empty[StateVarDecl]))((acc, decl) => {
      decl match {
        case InitDecl(body) =>
          val (stmts, vars) = inlineProcedureCalls((id, p) => initNameProvider(id, p), body)
          (acc._1 ++ List(InitDecl(stmts)), acc._2 ++ vars.map((t) => StateVarDecl(t._1, t._2)))
        case NextDecl(body) =>
          val (stmts, vars) = inlineProcedureCalls((id, p) => nextNameProvider(id, p), body)
          (acc._1 ++ List(NextDecl(stmts)), acc._2 ++ vars.map((t) => StateVarDecl(t._1, t._2)))
        case stmt =>
          (acc._1 ++ List(stmt), acc._2)
      }
    })
    val moduleDecls = decls._2 ++ decls._1
    return Some(Module(m.id, moduleDecls, m.cmds))
  }

  /** Inline a procedure call.
   *
   *  The return value consists of a tuple of:
   *  	- rewritten statements
   *    - new variables that will need to be declared in the enclosing scope.
   */
  def inlineProcedureCalls(uniqNamer : UniqueNameProvider, stmts : List[Statement]) : (List[Statement], List[(Identifier, Type)]) = {
    val init = (List.empty[Statement], List.empty[(Identifier, Type)])
    // we walk through the list of statements accumulating inlined procedures and new declarations.
    return stmts.foldLeft(init)((acc, stmt) => {
      stmt match {
        case ProcedureCallStmt(id, lhss, args) =>
          if (id != proc.id) {
            (acc._1 ++ List(stmt), acc._2)
          } else {
            // Sanity check.
            Utils.assert(args.size == proc.sig.inParams.size, "Incorrect number of arguments to procedure: " + proc.id + ".\nStatement: " + stmt.toString)
            Utils.assert(lhss.size == proc.sig.outParams.size, "Incorrect number of return values from procedure: " + proc.id)
            // what are the arguments?
            val argVars : List[Identifier] = proc.sig.inParams.map(_._1)
            // return values original names.
            var retVars : List[Identifier] = proc.sig.outParams.map(_._1)
            // new variables for the return values.
            var retNewVars : List[(Identifier, Type)] = proc.sig.outParams.map((r) => (uniqNamer(r._1, "ret"), r._2))
            // new variables for the local variables.
            val localNewVars : List[(Identifier, Type)] = proc.decls.map((v) => (uniqNamer(v.id, "loc"), v.typ))
            // map procedure formal arguments to actual
            val mEmpty = Map.empty[Expr, Expr]
            val mArgs = (argVars zip args).foldLeft(mEmpty)((map, t) => map + (t._1 -> t._2))
            val mRet  = (retVars zip retNewVars).foldLeft(mEmpty)((map, t) => map + (t._1 -> t._2._1))
            val mLocal = (proc.decls zip localNewVars).foldLeft(mEmpty)((map, t) => map + (t._1.id -> t._2._1))
            val resultAssignStatment = AssignStmt(lhss, retNewVars.map(_._1))
            val rewriteMap = mArgs ++ mRet ++ mLocal
            val rewriter = new ExprRewriter("ProcedureInlineRewriter", rewriteMap)
            (acc._1 ++ rewriter.rewriteStatements(proc.body) ++ List(resultAssignStatment), acc._2 ++ retNewVars ++ localNewVars)
          }
        case ForStmt(id, range, body) =>
          val bodyP = inlineProcedureCalls(uniqNamer, body)
          val forP = ForStmt(id, range, bodyP._1)
          (acc._1 ++ List(forP), acc._2 ++ bodyP._2)
        case IfElseStmt(cond, ifblock, elseblock) =>
          val ifBlockP = inlineProcedureCalls(uniqNamer, ifblock)
          val elseBlockP = inlineProcedureCalls(uniqNamer, elseblock)
          val ifElseP = IfElseStmt(cond, ifBlockP._1, elseBlockP._1)
          (acc._1 ++ List(ifElseP), acc._2 ++ ifBlockP._2 ++ elseBlockP._2)

        case CaseStmt(cases) =>
          val caseBodiesP = cases.map((c) => inlineProcedureCalls(uniqNamer, c._2))
          val caseConds = cases.map(_._1)
          val caseBodyStmts = caseBodiesP.map(_._1)
          val caseBodyVars = caseBodiesP.map(_._2)
          val caseStmtP = CaseStmt(caseConds zip caseBodyStmts)
          val newVars = caseBodyVars.foldLeft(List.empty[(Identifier, Type)])((acc, vars) => acc ++ vars)
          (acc._1 ++ List(caseStmtP), acc._2 ++ newVars)
        case _ => (acc._1 ++ List(stmt), acc._2)
      }
    })
  }
}

class ProcedureInliner extends ASTAnalysis {
  var findLeafProcedurePass = new FindLeafProcedurePass()
  var findLeafProcedureAnalysis = new ASTAnalyzer("ProcedureInliner.FindLeafProcedure", findLeafProcedurePass)

  override def passName = "ProcedureInliner"
  override def visit(module : Module, context : Scope) : Option[Module] = {
    var modP : Option[Module] = Some(module)
    var iteration = 0
    var done = false
    val MAX_ITERATIONS = 1000
    do {
      modP = modP match {
        case None =>
          done = true
          None
        case Some(mod) =>
          val leafProcSet = findLeafProcedureAnalysis.visitModule(mod, mod.procedures.map(_.id).toSet, context)
          val leafProc = leafProcSet.headOption
          leafProc match {
            case Some(procId) =>
              done = false
              val proc = mod.procedures.find((p) => p.id == procId).get
              // rewrite this procedure.
              val rewriter = new ASTRewriter("FunctionInliner.Inline:" + procId.toString, new InlineProcedurePass(proc))
              // println("Inlining procedure: " + proc.id.toString)
              val mP = rewriter.visit(mod, context)
              // println("** Changed Module **")
              // println(mP.get.toString)
              mP
            case None =>
              done = true
              Some(mod)
          }
      }
      iteration = iteration + 1
    } while(!done && iteration < MAX_ITERATIONS)
    // check if we managed to inline all procedures.
    modP match {
      case Some(mod) =>
        val procs = mod.procedures
        if (procs.size > 0) {
          val errors = procs.map((p) => ("Unable to inline procedure " + p.id + ". Do you have recursion?", p.position))
          throw new Utils.ParserErrorList(errors)
        }
      case None =>
    }
    Utils.assert(iteration < MAX_ITERATIONS, "Too many rewriting iterations.")
    return modP
  }
}

