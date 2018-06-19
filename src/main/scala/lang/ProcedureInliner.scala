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
 *
 * Inlines all procedure calls.
 *
 */

package uclid
package lang

import scala.collection.immutable.{Set => Set}
import com.typesafe.scalalogging.Logger

class FindProcedureDependencyPass extends ReadOnlyPass[Map[Identifier, Set[Identifier]]] {
  type T = Map[Identifier, Set[Identifier]]
  override def applyOnProcedureCall(d : TraversalDirection.T, proc : ProcedureCallStmt, in : T, context : Scope) : T = {
    def addEdge(caller : Identifier, callee : Identifier) : T = {
      in.get(caller) match {
        case Some(procedures) => in + (caller -> (procedures + callee))
        case None => in + (caller -> Set(callee))
      }
    }
    if (d == TraversalDirection.Down) {
      context.procedure match {
        case Some(currentProc) => addEdge(currentProc.id, proc.id)
        case None => addEdge(Identifier("_top"), proc.id)
      }
    } else { in }
  }
}

class FindProcedureDependency extends ASTAnalyzer("FindProcedureDependency", new FindProcedureDependencyPass())
{
  var procInliningOrder : List[Identifier] = List.empty

  override def visit(module : Module, context : Scope) : Option[Module] = {
    def recursionError(proc : Identifier, stack : List[Identifier]) : ModuleError = {
      val msg = "Recursion involving procedures: " + Utils.join(stack.map(_.toString).toList, ", ")
      ModuleError(msg, proc.position)
    }

    val procDepGraph = visitModule(module, Map.empty[Identifier, Set[Identifier]], context)
    val errors = Utils.findCyclicDependencies(procDepGraph, List(Identifier("_top")), recursionError)
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
    procInliningOrder = Utils.topoSort(List(Identifier("_top")), procDepGraph)
    Some(module)
  }
}

object ProcedureInliner {
  sealed abstract class RewriteOptions
  case object RewriteNext extends RewriteOptions
  case object RewriteInit extends RewriteOptions
}

class InlineProcedurePass(rewriteOptions : ProcedureInliner.RewriteOptions, procToInline : ProcedureDecl, primeVarMap : Map[Identifier, Identifier]) extends RewritePass {
  val log = Logger(classOf[InlineProcedurePass])

  type UniqueNameProvider = (Identifier, String) => Identifier
  override def rewriteProcedure(p : ProcedureDecl, ctx : Scope) : Option[ProcedureDecl] = {
    if (p.id == procToInline.id) Some(p)
    else {
      val ctxP = ctx + p
      val (stmts, newVars) = inlineProcedureCalls((id, p) => NameProvider.get(id.toString() + "_" + p), List(p.body), ctx)
      val newDecls = newVars.map((t) => LocalVarDecl(t._1, t._2))
      Some(ProcedureDecl(p.id, p.sig, p.decls ++ newDecls, BlockStmt(List.empty, stmts), p.requires, p.ensures, p.modifies))
    }
  }

  override def rewriteModule(m : Module, contextIn : Scope) : Option[Module] = {
    val context = contextIn + m
    val decls = m.decls.foldLeft((List.empty[Decl], List.empty[StateVarsDecl]))((acc, decl) => {
      decl match {
        case InitDecl(body) =>
          if (rewriteOptions == ProcedureInliner.RewriteInit) {
            val (stmts, vars) = inlineProcedureCalls((id, p) => NameProvider.get(id.toString() + "_" + p), List(body), context)
            (acc._1 ++ List(InitDecl(BlockStmt(List.empty, stmts))), acc._2 ++ vars.map((t) => StateVarsDecl(List(t._1), t._2)))
          } else {
            (acc._1 ++ List(decl), acc._2)
          }
        case NextDecl(body) =>
          if (rewriteOptions == ProcedureInliner.RewriteNext) {
            val (stmts, vars) = inlineProcedureCalls((id, p) => NameProvider.get(id.toString() + "_" + p), List(body), context)
            (acc._1 ++ List(NextDecl(BlockStmt(List.empty, stmts))), acc._2 ++ vars.map((t) => StateVarsDecl(List(t._1), t._2)))
          } else {
            (acc._1 ++ List(decl), acc._2)
          }
        case decl =>
          (acc._1 ++ List(decl), acc._2)
      }
    })
    val moduleDecls = decls._2 ++ decls._1
    return Some(Module(m.id, moduleDecls, m.cmds, m.notes))
  }

  /** Inline a procedure call.
   *
   *  The return value consists of a tuple of:
   *  	- rewritten statements
   *    - new variables that will need to be declared in the enclosing scope.
   */
  // FIXME: turn stmts into BlockStmt
  def inlineProcedureCalls(uniqNamer : UniqueNameProvider, stmts : List[Statement], context : Scope) : (List[Statement], List[(Identifier, Type)]) = {
    Utils.assert(context.map.size > 0, "Context is empty.")
    val init = (List.empty[Statement], List.empty[(Identifier, Type)])
    // we walk through the list of statements accumulating inlined procedures and new declarations.
    return stmts.foldLeft(init)((acc, stmt) => {
      stmt match {
        case ProcedureCallStmt(id, lhss, args) =>
          if (id != procToInline.id) {
            (acc._1 ++ List(stmt), acc._2)
          } else {
            // Sanity check.
            Utils.assert(args.size == procToInline.sig.inParams.size,
                "Incorrect number of arguments to procedure: " + procToInline.id.toString() + ".\nStatement: " + stmt.toString)
            Utils.assert(lhss.size == procToInline.sig.outParams.size,
                "Incorrect number of return values from procedure: " + procToInline.id.toString())
            // what are the arguments?
            val argVars : List[Identifier] = procToInline.sig.inParams.map(_._1)
            // return values original names.
            var retVars : List[Identifier] = procToInline.sig.outParams.map(_._1)
            // new variables for the return values.
            var retNewVars : List[(Identifier, Type)] = procToInline.sig.outParams.map((r) => (uniqNamer(r._1, "return"), r._2))
            // new variables for the local variables.
            val localNewVars : List[(Identifier, Type)] = procToInline.decls.map((v) => (uniqNamer(v.id, "local"), v.typ))
            // new variables for the modifies.
            val modifiesMap : List[(Identifier, Identifier, Type)] = if (procToInline.shouldInline) {
              List.empty
            } else {
              (procToInline.modifies.map {
                m => {
                  val typMOption = context.typeOf(m)
                  Utils.assert(typMOption.isDefined, "Unknown identifier %s in context %s.".format(m.toString, context.map.toString))
                  (primeVarMap.get(m).get, uniqNamer(m, "modifies"), context.typeOf(m).get) 
                }
              }).toList
            }
            val modifiesNewVars = modifiesMap.map(p => (p._2, p._3))

            // map procedure formal arguments to actual
            val mEmpty = Map.empty[Expr, Expr]
            val mArgs = (argVars zip args).foldLeft(mEmpty)((map, t) => map + (t._1 -> t._2))
            val mRet  = (retVars zip retNewVars).foldLeft(mEmpty)((map, t) => map + (t._1 -> t._2._1))
            val mLocal = (procToInline.decls zip localNewVars).foldLeft(mEmpty)((map, t) => map + (t._1.id -> t._2._1))
            val mModifies : Map[Expr, Identifier] = procToInline.modifies.map(m => (m -> primeVarMap.get(m).get)).toMap
            val mOldModifies : Map[Expr, Identifier] = modifiesMap.map(p => (Operator.old(p._1) -> p._2)).toMap
            val resultHavocStmts = retNewVars.map(retVar => HavocStmt(HavocableId(retVar._1)))
            val resultAssignStatment = if (lhss.size > 0) List(AssignStmt(lhss, retNewVars.map(_._1))) else List.empty
            val rewriteMap = mArgs ++ mRet ++ mLocal ++ mModifies
            log.debug("rewriteMap: {}", rewriteMap.toString())
            val preconditionAsserts = procToInline.requires.map {
              req => {
                val assertExpr = ExprRewriter.rewriteExpr(req, rewriteMap, context)
                val stmt = AssertStmt(assertExpr, Some(Identifier("precondition")))
                ASTNode.introducePos(true, true, stmt, req.position)
              }
            }
            val modifyAssigns = modifiesMap.map(p => AssignStmt(List(LhsId(p._2)), List(p._1)))
            val rewriter = new ExprRewriter("ProcedureInlineRewriter", rewriteMap)
            val procedureBody = if (procToInline.shouldInline) {
              rewriter.rewriteStatements(List(procToInline.body), context) ++ resultAssignStatment
            } else {
              val modifyHavocs = mModifies.map(m => HavocStmt(HavocableId(m._2)))
              val postconditionAssumes = procToInline.ensures.map {
                pos => {
                  log.debug("mOldModifies: {}", mOldModifies.toString())
                  //val assumeExpr1 = ExprRewriter.rewriteExpr(pos, mOldModifies, context)
                  val assumeExpr = ExprRewriter.rewriteExpr(pos, rewriteMap ++ mOldModifies, context)
                  val assumeStmt = AssumeStmt(assumeExpr, None)
                  log.debug("expr: {}; rewritten: {}", pos.toString(), assumeExpr.toString()) 
                  ASTNode.introducePos(true, true, assumeStmt, assumeExpr.position)
                }
              }
              modifyHavocs ++ postconditionAssumes
            }
            (acc._1 ++ resultHavocStmts ++ preconditionAsserts ++ modifyAssigns ++ procedureBody, 
             acc._2 ++ retNewVars ++ localNewVars ++ modifiesNewVars)
          }
        case BlockStmt(vs, stmts) =>
          val (stmtsP, vars) = inlineProcedureCalls(uniqNamer, stmts, context)
          val blockP = BlockStmt(vs, stmtsP)
          (acc._1 ++ List(blockP), acc._2 ++ vars)
        case ForStmt(id, typ, range, body) =>
          val bodyP = inlineProcedureCalls(uniqNamer, List(body), context)
          val forP = ForStmt(id, typ, range, BlockStmt(List.empty, bodyP._1))
          (acc._1 ++ List(forP), acc._2 ++ bodyP._2)
        case IfElseStmt(cond, ifblock, elseblock) =>
          val ifBlockP = inlineProcedureCalls(uniqNamer, List(ifblock), context)
          val elseBlockP = inlineProcedureCalls(uniqNamer, List(elseblock), context)
          val ifElseP = IfElseStmt(cond, BlockStmt(List.empty, ifBlockP._1), BlockStmt(List.empty, elseBlockP._1))
          (acc._1 ++ List(ifElseP), acc._2 ++ ifBlockP._2 ++ elseBlockP._2)

        case CaseStmt(cases) =>
          val caseBodiesP = cases.map((c) => inlineProcedureCalls(uniqNamer, List(c._2), context))
          val caseConds = cases.map(_._1)
          val caseBodyStmts = caseBodiesP.map(body => BlockStmt(List.empty, body._1))
          val caseBodyVars = caseBodiesP.map(_._2)
          val caseStmtP = CaseStmt(caseConds zip caseBodyStmts)
          val newVars = caseBodyVars.foldLeft(List.empty[(Identifier, Type)])((acc, vars) => acc ++ vars)
          (acc._1 ++ List(caseStmtP), acc._2 ++ newVars)
        case _ => (acc._1 ++ List(stmt), acc._2)
      }
    })
  }
}

class NewProcedureInlinerPass() extends RewritePass {
  def inlineProcedureCall(callStmt : ProcedureCallStmt, proc : ProcedureDecl, context : Scope) : Statement = {
    val procSig = proc.sig
    def getModifyLhs(id : Identifier) = {
      if (context.environment.isProcedural) { LhsId(id) }
      else { LhsNextId(id) }
    }

    // formal and actual argument pairs.
    val argPairs : List[(Identifier, Expr)] = ((procSig.inParams.map(p => p._1)) zip (callStmt.args))
    // formal and actual return value pairs.
    val retPairs : List[(Identifier, (Identifier, Type))] = procSig.outParams.map(p => (p._1 -> (NameProvider.get("ret_" + p._1.toString()), p._2)))
    // list of new return variables.
    val retIds = retPairs.map(r => r._2._1)
    // map from formal to actual arguments.
    val argMap : Map[Expr, Expr] = argPairs.map(p => p._1.asInstanceOf[Expr] -> p._2).toMap
    // map from formal to the fake variables created for return values.
    val retMap : Map[Expr, Expr] = retPairs.map(p => p._1.asInstanceOf[Expr] -> p._2._1).toMap
    // map from modified state variables to new variables created for them.
    val modifyPairs : List[(Identifier, Identifier)] = proc.modifies.map(m => (m, NameProvider.get("modifies_" + m.toString()))).toList
    // map from st_var -> modify_var.
    val modifiesMap : Map[Expr, Expr] = modifyPairs.map(p => (p._1 -> p._2)).toMap
    // map from old(var) -> var.
    val oldModifiesMap : Map[Expr, Expr] = modifyPairs.map(p => Operator.old(p._2) -> p._1).toMap
    // full rewrite map.
    val rewriteMap = argMap ++ retMap ++ modifiesMap ++ oldModifiesMap
    // rewriter object.
    val rewriter = new ExprRewriter("InlineRewriter", rewriteMap)

    // variable declarations for return values.
    val retVars = retPairs.map(r => BlockVarsDecl(List(r._2._1), r._2._2))
    // variable declarations for the modify variables.
    val modifyVars : List[BlockVarsDecl] = modifyPairs.map(p => BlockVarsDecl(List(p._2), context.get(p._1).get.typ))
    // list of all variable declarations.
    val varsToDeclare = retVars ++ modifyVars

    // statements assigning state variables to modify vars.
    val modifyInitAssigns : List[AssignStmt] = if (proc.shouldInline) {
      modifyPairs.map(p => AssignStmt(List(LhsId(p._2)), List(p._1)))
    } else {
      List.empty
    }
    // statements updating the state variables at the end.
    val modifyFinalAssigns : List[AssignStmt] = modifyPairs.map(p => AssignStmt(List(getModifyLhs(p._1)), List(p._2)))
    // create precondition asserts
    val preconditionAsserts : List[Statement] = proc.requires.map {
      (req) => {
        val exprP = rewriter.rewriteExpr(req, context)
        AssertStmt(exprP, None)
      }
    }
    // create postcondition asserts
    val postconditionAsserts : List[Statement] = if (proc.shouldInline) {
      proc.ensures.map {
        (ens) => {
          val exprP = rewriter.rewriteExpr(ens, context)
          AssertStmt(exprP, None)
        }
      }
    } else {
      List.empty
    }
    // body of the procedure.
    val bodyP = if (proc.shouldInline) {
      rewriter.rewriteStatement(proc.body, Scope.empty).get
    } else {
      val postconditionAssumes : List[Statement] = proc.ensures.map {
        (ens) => {
          val exprP = rewriter.rewriteExpr(ens, context)
          AssumeStmt(exprP, None)
        }
      }
      BlockStmt(List.empty, postconditionAssumes)
    }
    val stmtsP = if (callStmt.callLhss.size > 0) {
      val returnAssign = AssignStmt(callStmt.callLhss, retIds)
      modifyInitAssigns ++ preconditionAsserts ++ List(bodyP, returnAssign) ++ postconditionAsserts ++ modifyFinalAssigns
    } else {
      modifyInitAssigns ++ preconditionAsserts ++ List(bodyP) ++ postconditionAsserts ++ modifyFinalAssigns
    }
    BlockStmt(varsToDeclare, stmtsP)
  }
  override def rewriteProcedureCall(callStmt : ProcedureCallStmt, context : Scope) : Option[Statement] = {
    val procId = callStmt.id
    val proc = context.module.get.procedures.find(p => p.id == procId).get
    if (!proc.body.hasCall) {
      Some(inlineProcedureCall(callStmt, proc, context))
    } else {
      Some(callStmt)
    }
  }
}

class NewProcedureInliner() extends ASTRewriter("ProcedureInliner", new NewProcedureInlinerPass()) {
  override val repeatUntilNoChange = true
}

class ProcedureInliner(rewriteOptions: ProcedureInliner.RewriteOptions) extends ASTAnalysis {
  lazy val primedVariableCollector = manager.pass("PrimedVariableCollector").asInstanceOf[PrimedVariableCollector]
  lazy val findProcedureDependency = manager.pass("FindProcedureDependency").asInstanceOf[FindProcedureDependency]
  override def passName = "ProcedureInliner:"+rewriteOptions.toString()


  override def visit(module : Module, context : Scope) : Option[Module] = {
    val primeVarMap = if (rewriteOptions == ProcedureInliner.RewriteNext) {
      primedVariableCollector.primeVarMap.get
    } else {
      val writeables = module.sharedVars.map(p => p._1) ++ module.vars.map(p => p._1) ++ module.outputs.map(p => p._1)
      writeables.map(v => (v -> v)).toMap
    }
    val procInliningOrder = findProcedureDependency.procInliningOrder
    def inlineProcedure(procId : Identifier, mod : Module) : Module = {
      if (procId != Identifier("_top")) {
        val proc = mod.procedures.find(p => p.id == procId).get
        val rewriter = new ASTRewriter("ProcedureInliner.Inline:" + procId.toString, new InlineProcedurePass(rewriteOptions, proc, primeVarMap))
        rewriter.visit(mod, context).get
      } else {
        module
      }
    }
    val modP = procInliningOrder.foldLeft(module)((mod, procId) => inlineProcedure(procId, mod))
    Some(modP)
  }
}
