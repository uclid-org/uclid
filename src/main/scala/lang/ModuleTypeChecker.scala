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
        case AssertStmt(e, id) =>
          val eType = exprTypeChecker.typeOf(e, context)
          if (!eType.isBool) {
            in + ModuleError("Assertion expression must be of Boolean or Temporal type", st.position)
          } else {
            in
          }
        case AssumeStmt(e, id) =>
          val eType = exprTypeChecker.typeOf(e, context)
          if (!eType.isBool) {
            in + ModuleError("Assumption must be Boolean", st.position)
          } else {
            in
          }
        case HavocStmt(id) =>
          if (!context.doesNameExist(id)) {
            in + ModuleError("Unknown identifier in havoc statement", st.position)
          } else {
            in
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

        case IfElseStmt(cond, _, _) =>
          val cType = exprTypeChecker.typeOf(cond, context)
          if (!cType.isBool) {
            in + ModuleError("Condition in if statement must be of type boolean", st.position)
          } else {
            in
          }
        case ForStmt(_, range, _) =>
          range._1 match {
            case i: IntLit =>
              range._2 match {
                case j: IntLit =>
                  if (i.value > j.value) {
                    in + ModuleError("Range lower bound must be less than upper bound", st.position)
                  } else {
                    in
                  }
                case _ =>
                  in + ModuleError("Range lower and upper bounds must be of same type", st.position)
              }
            case b: BitVectorLit =>
              range._2 match {
                case c: BitVectorLit =>
                  if (b.value > c.value) {
                    in + ModuleError("Range lower bound must be less than upper bound", st.position)
                  } else if (b.width != c.width) {
                    in + ModuleError("Range lower and upper bounds must be of same width", st.position)
                  } else {
                    in
                  }
                case _ =>
                  in + ModuleError("Range lower and upper bounds must be of same type", st.position)
              }
          }
        case CaseStmt(body) =>
          body.foldLeft(in) {
            (acc, c) => {
              var cType = exprTypeChecker.typeOf(c._1, context)
              if (!cType.isBool) {
                acc + ModuleError("Case clause must be of type boolean", st.position)
              } else {
                acc
              }
            }
          }
        case ProcedureCallStmt(id, callLhss, args) =>
          var ret = in
          Utils.assert(context.module.isDefined, "Module must be defined!")
          val procOption = context.module.get.decls.find((p) => p.isInstanceOf[ProcedureDecl] && p.asInstanceOf[ProcedureDecl].id == id)

          if (procOption.isEmpty) {
            ret = ret + ModuleError("Procedure does not exist", id.position)
            return ret
          }

          val proc = procOption.get.asInstanceOf[ProcedureDecl]
          for ((param, arg) <- proc.sig.inParams zip args) {
            var (pId, pType) = param.asInstanceOf[(Identifier, Type)]
            var aType = exprTypeChecker.typeOf(arg.asInstanceOf[Expr], context)
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
        case SkipStmt() => in
      }
    }
  }
  override def applyOnDefine(d : TraversalDirection.T, defDecl : DefineDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      val contextP = context + defDecl.sig
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
