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
 *
 * ExpressionAnalyzer: Currently enables testing if an expression is a constant.
 *
 */

package uclid
package smt

import scala.collection.immutable.Map

object ExpressionAnalyzer {
  var z3ConstInterface = Z3Interface.newInterface()
  def getConstIntValue(expr : smt.Expr, scope : lang.Scope) : Option[Int] = {
    Utils.assert(expr.typ.isInt, "Expected an integer-sorted expression.")
    val smtExpr1 = Converter.renameSymbols(expr, (s, t) => s + "_1")
    val smtExpr2 = Converter.renameSymbols(expr, (s, t) => s + "_2")
    z3ConstInterface.push()
    z3ConstInterface.assert(smt.OperatorApplication(smt.InequalityOp, List(smtExpr1, smtExpr2)))
    val smtResult = z3ConstInterface.check()
    z3ConstInterface.pop()
    val isConst = smtResult.isFalse
    if (!isConst) return None
    else {
      val intLit = Symbol("$IntegerValue", smt.IntType())
      val eqExpr = smt.OperatorApplication(smt.EqualityOp, List(smtExpr1, intLit))
      z3ConstInterface.push()
      z3ConstInterface.assert(eqExpr)
      val smtResult = z3ConstInterface.check()
      z3ConstInterface.pop()
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
}