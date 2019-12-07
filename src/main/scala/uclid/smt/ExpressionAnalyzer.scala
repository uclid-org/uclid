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
 * ExpressionAnalyzer: Currently enables testing if an expression is a constant.
 *
 */

package uclid
package smt

import scala.collection.immutable.Map

object ExpressionAnalyzer {
  var z3ConstInterface = new Z3Interface()
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
      val intLit = Symbol("$IntegerValue", smt.IntType)
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
