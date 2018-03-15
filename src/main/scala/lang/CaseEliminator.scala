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
 * Author : Pramod Subramanyan
 *
 * The CaseEliminatorPass eliminate case statements from the AST and replaces
 * them with ifs.
 *
 * The IfEliminatorPass elimiantes if statements from the AST and replaces
 * them with conditional assignments.
 *
 */
package uclid
package lang

import scala.collection.mutable.{Set => MutableSet}
import scala.collection.immutable.Map

class CaseEliminatorPass extends RewritePass {
  def casesToIfs(cases : List[(Expr, List[Statement])]) : List[Statement] = {
    cases match {
      case Nil =>
        List.empty[Statement]
      case head :: rest =>
        List(IfElseStmt(head._1, head._2, casesToIfs(rest)))
    }
  }

  override def rewriteCase(st : CaseStmt, ctx : Scope) : List[Statement] = {
    casesToIfs(st.body)
  }
}

class CaseEliminator extends ASTRewriter(
    "CaseEliminator", new CaseEliminatorPass())

class IfEliminatorPass extends RewritePass {
  val newVarDeclarations = MutableSet.empty[(Identifier, Type)]
  var nameProvider : Option[ContextualNameProvider] = None

  def setModule(module : Module, context : Scope) {
    nameProvider = Some(new ContextualNameProvider(context, "ifelim"))
  }

  def rewriteStatements(cond : Expr, stmts : List[Statement], context : Scope) : (Map[Expr, Identifier], List[Statement]) = {
    val init = (Map.empty[Expr, Identifier], List.empty[Statement])
    stmts.foldLeft(init) {
      (acc, st) => {
        st match {
          case SkipStmt() =>
            (acc._1, acc._2 ++ List(st))
          case AssumeStmt(e, id) =>
            val eP = ExprRewriter.rewriteExpr(e, acc._1, context)
            val stP = AssumeStmt(Operator.imply(cond, eP), id)
            (acc._1, acc._2 ++ List(stP))
          case AssertStmt(e, id) =>
            val eP = ExprRewriter.rewriteExpr(e, acc._1, context)
            val stP = AssertStmt(Operator.and(cond, eP), id)
            (acc._1, acc._2 ++ List(stP))
          case HavocStmt(id) =>
            val idP = nameProvider.get(id, "havoc")
            val mapP = acc._1 + (id -> idP)
            val stP = HavocStmt(idP)
            (mapP, acc._2 ++ List(stP))
          case AssignStmt(lhss, rhss) =>
            val newLhsIds = lhss.map(lhs => (lhs.ident, nameProvider.get(lhs.ident, "assign")))
            val rhssP = rhss.map(rhs => ExprRewriter.rewriteExpr(rhs, acc._1, context))
            val newLhsCopys = newLhsIds.map(p => AssignStmt(List(LhsId(p._2)), List(p._1)))
            val mapP = newLhsIds.foldLeft(acc._1)((acc, p) => acc + (p._1 -> p._2))
            val lhssP = lhss.map(lhs => ExprRewriter.rewriteLHS(lhs, mapP, context))
            val stP = newLhsCopys ++ List(AssignStmt(lhssP, rhssP))
            (mapP, acc._2 ++ stP)
          case IfElseStmt(_, _, _) =>
            throw new Utils.AssertionError("If else statements are not expected here.")
          case ForStmt(_, _, _) =>
            throw new Utils.AssertionError("For loops must have been eliminated by now.")
          case CaseStmt(_) =>
            throw new Utils.AssertionError("Case statements should have been eliminated by now.")
          case ProcedureCallStmt(_, _, _) =>
            throw new Utils.AssertionError("Procedure calls should have been inlined by now.")
          case ModuleCallStmt(_) =>
            (acc._1, acc._2 ++ List(st))
        }
      }
    }
  }
  override def rewriteIfElse(ifElseStmt : IfElseStmt, ctx : Scope) : List[Statement] = {
    val cond = ifElseStmt.cond
    val notCond = Operator.not(cond)
    val (mapThen, ifBlockP) = rewriteStatements(cond, ifElseStmt.ifblock, ctx)
    val (mapElse, elseBlockP) = rewriteStatements(notCond, ifElseStmt.elseblock, ctx)
    val mapUnifiedLeft : Map[Identifier, (Identifier, Identifier)] =
      mapThen.map(p => p._1.asInstanceOf[Identifier] -> (p._2, p._1.asInstanceOf[Identifier]))
    val mapUnified = mapElse.foldLeft(mapUnifiedLeft) {
      (acc, rightEntry) => {
        val ident = rightEntry._1.asInstanceOf[Identifier]
        acc.get(ident) match {
          case None => acc + (ident -> (ident, rightEntry._2))
          case Some(leftEntry) => acc + (ident -> (leftEntry._1, rightEntry._2))
        }
      }
    }
    mapThen.foreach(p => newVarDeclarations += (p._2 -> ctx.typeOf(p._1.asInstanceOf[Identifier]).get))
    mapElse.foreach(p => newVarDeclarations += (p._2 -> ctx.typeOf(p._1.asInstanceOf[Identifier]).get))
    val iteStmts = (mapUnified.map(
      p => AssignStmt(List(LhsId(p._1)), List(Operator.ite(cond, p._2._1, p._2._2)))
    )).toList
    ifBlockP ++ elseBlockP ++ iteStmts
  }

  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val newDeclarations = newVarDeclarations.map(p => StateVarsDecl(List(p._1), p._2))
    val newDecls = module.decls ++ newDeclarations
    Some(Module(module.id, newDecls, module.cmds, module.notes))
  }
}

class IfEliminator extends ASTRewriter("IfEliminator", new IfEliminatorPass()) {
  override val pass : IfEliminatorPass = super.pass.asInstanceOf[IfEliminatorPass]
  override def visit(module : Module, context : Scope) : Option[Module] = {
    pass.setModule(module, context)
    visitModule(module, context)
  }
}