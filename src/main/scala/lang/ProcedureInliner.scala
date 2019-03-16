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
    // full rewrite map.
    val rewriteMap = argMap ++ retMap ++ modifiesMap
    // rewriter object.
    val rewriter = new ExprRewriter("InlineRewriter", rewriteMap)
    // map from old(var) -> var.
    val oldMap : Map[Identifier, Identifier] = modifyPairs.map(p => p._2 -> p._1).toMap
    // rewriter object.
    val oldRewriter = new OldExprRewriter(oldMap)

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
        val exprP = oldRewriter.rewriteExpr(rewriter.rewriteExpr(req, context), context)
        val node = AssertStmt(exprP, Some(Identifier("precondition")))
        ASTNode.introducePos(true, true, node, req.position)
      }
    }
    // create postcondition asserts
    val postconditionAsserts : List[Statement] = if (proc.shouldInline) {
      proc.ensures.map {
        (ens) => {
          val exprP = oldRewriter.rewriteExpr(rewriter.rewriteExpr(ens, context), context)
          val node = AssertStmt(exprP, Some(Identifier("postcondition")))
        ASTNode.introducePos(true, true, node, ens.position)
        }
      }
    } else {
      List.empty
    }
    // body of the procedure.
    val bodyP = if (proc.shouldInline) {
      oldRewriter.rewriteStatement(rewriter.rewriteStatement(proc.body, Scope.empty).get, context).get
    } else {
      val postconditionAssumes : List[Statement] = proc.ensures.map {
        (ens) => {
          val exprP = oldRewriter.rewriteExpr(rewriter.rewriteExpr(ens, context), context)
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

// The following cleans up procedure pre-conditions to ensure they always
// use the "old" version of state variables.
class ProcedureRequiresRewriterPass extends RewritePass {
  override def rewriteProcedure(proc: ProcedureDecl, context : Scope) : Option[ProcedureDecl] = {
    val rewriteMap : Map[Expr, Expr] = proc.modifies.map {
      v => v -> OperatorApplication(OldOperator(), List(v))
    }.toMap
    val requiresP = proc.requires.map(e => ExprRewriter.rewriteExprOnce(e, rewriteMap, context))
    val procP = ProcedureDecl(proc.id, proc.sig, proc.body, requiresP, proc.ensures, proc.modifies, proc.annotations)
    Some(procP)
  }
}

class ProcedureRequiresRewriter extends ASTRewriter(
  "ProcedureRequiresRewriter", new ProcedureRequiresRewriterPass()
)

class DoubleOldOperatorRemovePass extends RewritePass {
  override def rewriteOperatorApp(opapp:  OperatorApplication, ctx:  Scope): Option[Expr] = {
    opapp match {
      case OperatorApplication(
            OldOperator(), List(OperatorApplication(OldOperator(), args))) =>
        Some(OperatorApplication(OldOperator(), args))
      case _ =>
        Some(opapp)
    }
  }
}

class DoubleOldOperatorRemove extends ASTRewriter(
  "DoubleOldOperatorRemove", new DoubleOldOperatorRemovePass())
{
  override val repeatUntilNoChange = true
}