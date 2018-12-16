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
import uclid.lang.{Scope}

import scala.collection.mutable.ArrayBuffer



case class TransitionSystem(
    init : smt.Expr,
    tr   : smt.Expr,
    inv  : smt.Symbol,
    bads : Seq[smt.Expr]
)

class Z3HornSolver(sim: SymbolicSimulator) extends Z3Interface {
  z3.Global.setParameter("fixedpoint.engine", "pdr")
  var id = 0
  def getUniqueId() = {
    id = id + 1
    id - 1
  }

  def hornSolve(M : TransitionSystem) : List[Option[Boolean]] = {
    List.empty
  }


  def solveLambdas(initLambda: smt.Lambda, nextLambda: smt.Lambda,
                   initHyperAssumes: List[smt.Expr], initAsserts: List[AssertInfo],
                   initHyperAsserts: List[AssertInfo], nextHyperAsserts: List[AssertInfo],
                   nextAssumes: List[smt.Expr], nextHyperAssumes: List[smt.Expr], nextAsserts: List[AssertInfo],
                   scope: Scope) = {

    z3.Global.setParameter("fixedpoint.engine", "pdr")
    val sorts = initLambda.ids.map(id => getZ3Sort(id.typ))
    var finalSorts = sorts
    val numCopies = sim.getMaxHyperInvariant(scope)
    for (i <- 1 to numCopies - 1) {
      finalSorts = finalSorts ++ sorts
    }

    val simRecord = new sim.SimulationTable
    var prevVarTable = new ArrayBuffer[List[List[smt.Expr]]]()
    var havocTable = new ArrayBuffer[List[(smt.Symbol, smt.Symbol)]]()


    val boolSort = ctx.mkBoolSort()
    val invDecl = ctx.mkFuncDecl("inv", finalSorts.toArray, boolSort)
    val fp = ctx.mkFixedpoint()

    var inputStep = 0
    var initConjuncts = new ArrayBuffer[smt.Expr]()

    for (i <- 1 to numCopies) {
      var frames = new sim.FrameTable
      val initSymTab = sim.newInputSymbols(sim.getInitSymbolTable(scope), inputStep, scope)
      inputStep += 1
      frames += initSymTab
      var prevVars = sim.getVarsInOrder(initSymTab.map(_.swap), scope)
      prevVarTable += prevVars
      val init_havocs = sim.getHavocs(initLambda.e)
      val havoc_subs = init_havocs.map {
        havoc =>
          val s = havoc.id.split("_")

          val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
          (havoc, sim.newHavocSymbol(name, havoc.typ))
      }
      havocTable += havoc_subs
      val init_conjunct = sim.substitute(sim.betaSubstitution(initLambda, prevVars.flatten), havoc_subs)
      //addAssumptionToTree(init_conjunct, List.empty)
      initConjuncts += init_conjunct
      simRecord += frames
    }

    val initConjunctsZ3 = initConjuncts.map(exp => exprToZ3(exp).asInstanceOf[z3.BoolExpr])
    val rewrittenInitHyperAssumes = sim.rewriteHyperAssumes(
      initLambda, 0, initHyperAssumes, simRecord, 0, scope, prevVarTable.toList)

    val asserts_init = sim.rewriteAsserts(
      initLambda, initAsserts, 0,
      prevVarTable(0).flatten.map(p => p.asInstanceOf[smt.Symbol]),
      simRecord.clone(), havocTable(0))

    val initAssertsMap: Map[AssertInfo, z3.FuncDecl] = asserts_init.map {
      assert =>
        val errorDecl = ctx.mkFuncDecl("error_init_assert_" + getUniqueId().toString, Array[z3.Sort](), boolSort)
        fp.registerRelation(errorDecl)
        val not = ctx.mkNot(exprToZ3(assert.expr).asInstanceOf[z3.BoolExpr])
        val and = ctx.mkAnd(initConjunctsZ3(0), not)
        val implies = ctx.mkImplies(and, errorDecl.apply().asInstanceOf[z3.BoolExpr])
        fp.addRule(implies, ctx.mkSymbol("init_assert_" + getUniqueId().toString))
        assert -> errorDecl
    }.toMap

    val asserts_init_hyper = sim.rewriteHyperAsserts(
      initLambda, 0, initHyperAsserts, simRecord, 0, scope, prevVarTable.toList)

    val initHyperAssertsMap: Map[AssertInfo, z3.FuncDecl] = asserts_init_hyper.map {
      assert =>
        val errorDecl = ctx.mkFuncDecl("error_init_hyp_assert_" + getUniqueId().toString(), Array[z3.Sort](), boolSort)
        fp.registerRelation(errorDecl)
        val not = ctx.mkNot(exprToZ3(assert.expr).asInstanceOf[z3.BoolExpr])
        val and = ctx.mkAnd(initConjunctsZ3 : _*)
        val implies = ctx.mkImplies(ctx.mkAnd(and, not), errorDecl.apply().asInstanceOf[z3.BoolExpr])
        fp.addRule(implies, ctx.mkSymbol("init_hyp_assert_" + getUniqueId().toString))
        assert -> errorDecl
    }.toMap

    
    // 1) Make copies of all the variables
    // 2) Make error decls for each of the asserts and hyperAsserts
    // 3) Encode everything like the example
    // 4) For each error relation query the fixed point


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
    //val initRule = createForall(sorts2, symbols2, ctx.mkImplies(initCond, applyDecl(invDecl, x, y)))
    val initRule = ctx.mkImplies(initCond, applyDecl(invDecl, x, y))

    // inv(x, y) ==> inv(x+1, y+x)
    val xPlus1 = ctx.mkAdd(x, ctx.mkInt(1))
    val yPlusx = ctx.mkAdd(y, x)
    val guard = applyDecl(invDecl, x, y)
    //val trRule = createForall(sorts2, symbols2, ctx.mkImplies(guard, applyDecl(invDecl, xPlus1, yPlusx)))
    val trRule = ctx.mkImplies(guard, applyDecl(invDecl, xPlus1, yPlusx))

    val yProp1 = ctx.mkGe(x, y)
    val propGuard = ctx.mkAnd(applyDecl(invDecl, x, y), yProp1)
    //val propRule = createForall(sorts2, symbols2, ctx.mkImplies(propGuard, errorDecl.apply().asInstanceOf[z3.BoolExpr]))
    val propRule = ctx.mkImplies(propGuard, errorDecl.apply().asInstanceOf[z3.BoolExpr])
    
    fp.addRule(initRule, ctx.mkSymbol("initRule"))
    fp.addRule(trRule, ctx.mkSymbol("trRule"))
    fp.addRule(propRule, ctx.mkSymbol("propRule"))

    UclidMain.println(fp.toString())

    // property.
    UclidMain.println (fp.query(Array(errorDecl)).toString)
  }


}
