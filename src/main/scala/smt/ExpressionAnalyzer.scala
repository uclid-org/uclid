/*
 * UCLID5
 * 
 * Author: Pramod Subramanyan
 *
 * ExpressionAnalyzer: Currently enables testing if an expression is a constant.
 *
 */

package uclid
package smt

import scala.collection.immutable.Map

object ExpressionAnalyzer {
  var z3ConstInterface = Z3Interface.newInterface()
  def getConstIntValue(expr : smt.Expr, scope : lang.ScopeMap) : Option[Int] = {
    Utils.assert(expr.typ.isInt, "Expected an integer-sorted expression.")
    val smtExpr1 = Converter.renameSymbols(expr, (s, t) => s + "_1")
    val smtExpr2 = Converter.renameSymbols(expr, (s, t) => s + "_2")
    val isConst = z3ConstInterface.check(smt.OperatorApplication(smt.InequalityOp, List(smtExpr1, smtExpr2))).isFalse
    if (!isConst) return None
    else {
      val intLit = Symbol("$IntegerValue", smt.IntType())
      val eqExpr = smt.OperatorApplication(smt.EqualityOp, List(smtExpr1, intLit))
      val smtResult = z3ConstInterface.check(eqExpr)
      smtResult.model match {
        case Some(m) => 
          m.evaluate(intLit) match {
            case IntLit(v) => Some(v.toInt)
            case _ => None
          }
        case None => None
      }
    }
  }
  def isExprConst(expr : smt.Expr, scope : lang.ScopeMap) : Boolean = {
    val smtExpr1 = Converter.renameSymbols(expr, (s, t) => s + "_1")
    val smtExpr2 = Converter.renameSymbols(expr, (s, t) => s + "_2")
    z3ConstInterface.check(smt.OperatorApplication(smt.InequalityOp, List(smtExpr1, smtExpr2))).isFalse
  }
}