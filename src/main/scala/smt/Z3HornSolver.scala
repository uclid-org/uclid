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
 * Z3 Solver for Constrained Horn Clauses.
 *
 */

package uclid
package smt

import com.microsoft.z3

case class TransitionSystem(
    init : smt.Expr,
    tr   : smt.Expr,
    inv  : smt.Symbol,
    bads : Seq[smt.Expr]
)

class Z3HornSolver extends Z3Interface {
  z3.Global.setParameter("fixedpoint.engine", "pdr")
  def hornSolve(M : TransitionSystem) : List[Option[Boolean]] = {
    List.empty
  }
}

object Z3HornSolver
{
  def test() : Unit = {
    // Transition system
    //
    // Init(x, y) = x == 0 && y > 1
    // Transition(x, y, x', y') = (x' = x + 1) && (y' = y + x)
    // Bad(x, y) = x >= y
    //
    z3.Global.setParameter("fixedpoint.engine", "pdr")

    val ctx = new z3.Context()
    val intSort = ctx.mkIntSort()
    val boolSort = ctx.mkBoolSort()
    val fp = ctx.mkFixedpoint()

    val sorts2 = Array[z3.Sort](intSort, intSort)
    val invDecl = ctx.mkFuncDecl("inv", sorts2, boolSort)
    val errorDecl = ctx.mkFuncDecl("error", Array[z3.Sort](), boolSort)

    val symbolx = ctx.mkSymbol(0)
    val symboly = ctx.mkSymbol(1)
    val symbols2 = Array[z3.Symbol](symbolx, symboly)
    val x = ctx.mkBound(0, sorts2(0)).asInstanceOf[z3.ArithExpr]
    val y = ctx.mkBound(1, sorts2(1)).asInstanceOf[z3.ArithExpr]
    
    def applyDecl(f : z3.FuncDecl, x : z3.ArithExpr, y : z3.ArithExpr) : z3.BoolExpr = {
      f.apply(x, y).asInstanceOf[z3.BoolExpr]
    }
    var qId = 0
    var skId = 0
    def createForall(sorts : Array[z3.Sort], symbols : Array[z3.Symbol], e : z3.Expr) = {
      qId += 1
      skId += 1
      ctx.mkForall(sorts, symbols, e,
        0, Array[z3.Pattern](), Array[z3.Expr](), ctx.mkSymbol(qId), ctx.mkSymbol(skId))
    }
    
    fp.registerRelation(invDecl)
    fp.registerRelation(errorDecl)

    // x >= 0 && y >= 0 ==> inv(x, y)
    val xEq0 = ctx.mkEq(x, ctx.mkInt(0))
    val yGt1 = ctx.mkGt(y, ctx.mkInt(1))
    val initCond = ctx.mkAnd(xEq0, yGt1)
    val initRule = createForall(sorts2, symbols2, ctx.mkImplies(initCond, applyDecl(invDecl, x, y)))

    // inv(x, y) ==> inv(x+1, y+x)
    val xPlus1 = ctx.mkAdd(x, ctx.mkInt(1))
    val yPlusx = ctx.mkAdd(y, x)
    val guard = applyDecl(invDecl, x, y)
    val trRule = createForall(sorts2, symbols2, ctx.mkImplies(guard, applyDecl(invDecl, xPlus1, yPlusx)))

    val yProp1 = ctx.mkGe(x, y)
    val propGuard = ctx.mkAnd(applyDecl(invDecl, x, y), yProp1)
    val propRule = createForall(sorts2, symbols2, ctx.mkImplies(propGuard, errorDecl.apply().asInstanceOf[z3.BoolExpr]))
    
    fp.addRule(initRule, ctx.mkSymbol("initRule"))
    fp.addRule(trRule, ctx.mkSymbol("trRule"))
    fp.addRule(propRule, ctx.mkSymbol("propRule"))

    println(fp.toString())

    // property.
    println (fp.query(Array(errorDecl)))
  }
}
