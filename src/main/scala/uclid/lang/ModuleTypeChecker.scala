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
 * Authors: Norman Mu, Pramod Subramanyan

 * All sorts of type inference and type checking functionality is in here.
 *
 */

package uclid
package lang

class ModuleTypeCheckerPass extends ReadOnlyPass[Set[ModuleError]]
{
  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  override def applyOnStatement(d : TraversalDirection.T, st : Statement, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      in
    } else {
      st match {
        case AssertStmt(e, _) =>
          val eType = exprTypeChecker.typeOf(e, context)
          if (!eType.isBool) {
            in + ModuleError("Assertion expression must be of Boolean or Temporal type", st.position)
          } else {
            in
          }
        case AssumeStmt(e, _) =>
          val eType = exprTypeChecker.typeOf(e, context)
          if (!eType.isBool) {
            in + ModuleError("Assumption must be Boolean", st.position)
          } else {
            in
          }
        case HavocStmt(h) =>
          h match {
            case HavocableId(id) =>
              if (!context.doesNameExist(id)) {
                in + ModuleError("Unknown identifier in havoc statement", st.position)
              } else {
                in
              }
            case HavocableNextId(id) =>
              if (!context.doesNameExist(id)) {
                in + ModuleError("Unknown identifier in havoc statement", st.position)
              } else {
                in
              }
            case HavocableFreshLit(_) =>
              in
            case HavocableInstanceId(_) =>
              throw new Utils.AssertionError("Should be no havocable instance ids at this point")
          }
        case AssignStmt(lhss, rhss) =>
          var ret = in

          if (rhss.size == 0) {
            ret = in + ModuleError("Right hand size of assignment must not be empty", st.position)
          }

          for ((lh, rh) <- lhss zip rhss) {
            val lhType = exprTypeChecker.typeOf(lh, context)
            val rhType = exprTypeChecker.typeOf(rh, context)
            if(context.isNameReadOnly(lh.ident)) {
              ret = in + ModuleError("'%s' is a readonly entity and cannot be assigned to".format(lh.ident.toString), st.position)
            }
            if (!lhType.matches(rhType)) {
              lh.ident.toString
              ret = in + ModuleError("'%s' expected type '%s' but received type '%s'".format(lh.ident.toString, lhType.toString, rhType.toString), st.position)
            }
          }

          val l1 = lhss.length
          val l2 = rhss.length

          if (l1 != l2) {
            ret = ret + ModuleError("Assignment expected %d expressions but received %d".format(l1, l2), st.position)
          }

          ret

        case BlockStmt(_, _) =>
          in
        case IfElseStmt(cond, _, _) =>
          val cType = exprTypeChecker.typeOf(cond, context)
          if (!cType.isBool) {
            in + ModuleError("Condition in if statement must be of type boolean", st.position)
          } else {
            in
          }
        case ForStmt(_,_,  range, _) =>
          // FIXME: @ConstantLitForLoop
          (range._1, range._2) match {
            case (i: IntLit, j : IntLit) =>
              if (i.value > j.value) {
                in + ModuleError("Range lower bound must be less than upper bound", st.position)
              } else {
                in
              }
            case (b: BitVectorLit, c : BitVectorLit) =>
              if (b.value > c.value) {
                in + ModuleError("Range lower bound must be less than upper bound", st.position)
              } else if (b.width != c.width) {
                in + ModuleError("Range lower and upper bounds must be of same width", st.position)
              } else {
                in
              }
            case (_: NumericLit, _ : NumericLit) =>
              in + ModuleError("Range lower and upper bounds must be of same type", st.position)
            // The following three cases catch the same error, but we split them so that the error points to the right location.
            case (_: NumericLit, _) =>
              in + ModuleError("Invalid for loop range", range._2.position)
            case (_, _ : NumericLit) =>
              in + ModuleError("Invalid for loop range", range._1.position)
            case _ =>
              in + ModuleError("Invalid for loop range", range._1.position)
          }
        case WhileStmt(cond, _, invs) =>
          val cType = exprTypeChecker.typeOf(cond, context)
          val inP1 = if (cType.isBool) {
            in
          } else {
            in + ModuleError("While loop condition must be of type boolean", cond.position)
          }
          val badInvs = invs.filter(inv => !exprTypeChecker.typeOf(inv, context).isBool)
          val invErrors = badInvs.map(bInv => ModuleError("While loop invariant must be of type boolean", bInv.position))
          inP1 ++ invErrors
        case CaseStmt(body) =>
          body.foldLeft(in) {
            (acc, c) => {
              val cType = exprTypeChecker.typeOf(c._1, context)
              if (!cType.isBool) {
                acc + ModuleError("Case clause must be of type boolean", st.position)
              } else {
                acc
              }
            }
          }
        case ProcedureCallStmt(id, callLhss, args, instanceId, _) =>
          var ret = in
          Utils.assert(context.module.isDefined, "Module must be defined!")
          val procOption = instanceId match {
            case Some(iid) => {
              val instOption = context.module.get.instances.find(inst => inst.instanceId == iid)
              if (instOption.isEmpty) {
                ret = ret + ModuleError(s"Instance id: ${instanceId} in procedure call: ${id} does not exist in the context. Double check the name", st.position)
                return ret
              }
              val instMod = context.get(instOption.get.moduleId).get.asInstanceOf[Scope.ModuleDefinition].mod
              instMod.procedures.find((p) => p.id == id)
            }
            case _ => context.module.get.decls.find((p) => p.isInstanceOf[ProcedureDecl] && p.asInstanceOf[ProcedureDecl].id == id)
          }
          if (procOption.isEmpty) {
            ret = ret + ModuleError("Procedure does not exist", id.position)
            return ret
          }

          val proc = procOption.get.asInstanceOf[ProcedureDecl]
          for ((param, arg) <- proc.sig.inParams zip args) {
            var (pId, pType) = param.asInstanceOf[(Identifier, Type)]
            val aType = exprTypeChecker.typeOf(arg.asInstanceOf[Expr], context)
            if (!pType.matches(aType)) {
              ret = ret + ModuleError("Parameter %s expected argument of type %s but received type %s".format(pId.name, pType.toString, aType.toString), st.position)
            }
          }

          var l1 = proc.sig.inParams.length
          var l2 = args.length

          if (l1 != l2) {
            ret = ret + ModuleError("Procedure expected %d arguments but received %d".format(l1, l2), st.position)
          }

          for ((retval, lh) <- proc.sig.outParams zip callLhss) {
            val rType = retval.asInstanceOf[(Identifier, Type)]._2
            val lType = exprTypeChecker.typeOf(lh, context)
            if (!rType.matches(lType)) {
              ret = ret + ModuleError("Left hand variable %s expected return value of type %s but received type %s"
                .format(lh.toString, lType.toString, rType.toString), st.position)
            }
            if(context.isNameReadOnly(lh.ident)) {
              ret = ret + ModuleError("'%s' is a readonly entity and cannot be assigned to".format(lh.ident.toString), st.position)
            }
          }

          l1 = proc.sig.outParams.length
          l2 = callLhss.length

          if (l1 != l2) {
            ret = ret + ModuleError("Left hand side expected %d return values but received %d".format(l1, l2), st.position)
          }
          ret
        case ModuleCallStmt(id) =>
          val instanceNames : Set[Identifier] = context.module.get.instanceNames
          if (!instanceNames.contains(id)) {
            val error = ModuleError("Unknown module instance: " + id.toString, id.position)
            in + error
          } else {
            in
          }
        case MacroCallStmt(id) =>
          var ret = in
          context.map.get(id) match {
              case Some(Scope.Macro(mId, typ, macroDecl)) => ret
              case _ => ret + ModuleError("Macro does not exist", id.position)
          }
        case SkipStmt() => in
      }
    }
  }
  override def applyOnDefine(d : TraversalDirection.T, defDecl : DefineDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      val exprType = exprTypeChecker.typeOf(defDecl.expr, context + defDecl.sig)
      if (exprType != defDecl.sig.retType) {
        val error = ModuleError("Return type and expression type do not match", defDecl.expr.position)
        in + error
      } else {
        in
      }
    } else {
      in
    }
  }

  override def applyOnGroup(d : TraversalDirection.T, groupDecl : GroupDecl, in : T, context : Scope) : T = {
    val groupElemType = 
      groupDecl.typ match {
        case GroupType(typ) => typ
        case _ => throw new Utils.RuntimeError("GroupDecl does not have type GroupType?")
      }

    def checkGroupTypes(errors : T, expr : Expr) : T =
    {
      val exprType = exprTypeChecker.typeOf(expr, context)

      if (exprType != groupDecl.typ.typ)
      {
        val error = ModuleError("Expected member of group type %s but found member of type %s".format(groupDecl.typ.typ.toString, exprType.toString), expr.position)
        errors + error
      }
      else
      {
        errors
      }
    }

    var ret = in
    
    if (d == TraversalDirection.Down) {
      ret = groupDecl.members.foldLeft(ret)(checkGroupTypes)
    }

    ret
  }

  override def applyOnModuleTypesImport(d : TraversalDirection.T, modTypImport : ModuleTypesImportDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      val id = modTypImport.id
      context.map.get(id) match {
        case Some(Scope.ModuleDefinition(_)) =>
          in
        case _ =>
          val error = ModuleError("Unknown module in module types import declaration", modTypImport.id.position)
          in + error
      }
    } else {
      in
    }
  }
}

class ModuleTypeChecker extends ASTAnalyzer("ModuleTypeChecker", new ModuleTypeCheckerPass())  {
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, Set.empty[ModuleError], context)
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}
