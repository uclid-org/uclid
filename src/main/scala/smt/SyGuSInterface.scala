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
 * SyGuS solver interface.
 *
 */

package uclid
package smt

import lang.{Identifier, Scope}
import com.typesafe.scalalogging.Logger

class SyGuSInterface(args: List[String]) extends SMTLIB2Base with SynthesisContext {
  val sygusLog = Logger(classOf[SyGuSInterface])

  override def getTypeName(suffix: String) : String = {
    counterId += 1
    "type_" + suffix + "_" + counterId.toString()
  }
  override def getVariableName(v : String) : String = {
    "var_" + v
  }
  def getPrimedVariableName(v : String) : String = {
    "var_" + v + "!"
  }
  def getEqExpr(ident : Identifier, expr : smt.Expr, ctx : Scope, getNameFn : (String => String)) : String = {
    val typ = Converter.typeToSMT(ctx.typeOf(ident).get)
    val symbol = Symbol(ident.name, typ)
    val eqExpr : smt.Expr = OperatorApplication(EqualityOp, List(symbol, expr))
    val symbols = Context.findSymbols(eqExpr)
    val symbolsP = symbols.filter(s => !variables.contains(s.id))
    symbolsP.foreach {
      (s) => {
        val sIdP = getNameFn(s.id)
        variables += (s.id -> (sIdP, s.symbolTyp))
      }
    }
    val trExpr = translateExpr(eqExpr, true)
    trExpr
  }

  def getInitFun(initState : Map[Identifier, Expr], variables : List[(String, Type)], ctx : Scope) : String = {
    val initExprs = initState.map(p => getEqExpr(p._1, p._2, ctx, getVariableName)).toList
    val paramString = "(" + Utils.join(variables.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")"), " ") + ")"
    val funcBody = "(and " + Utils.join(initExprs, " ") + ")"
    val func = "(define-fun init-fn " + paramString + " " + funcBody + ")"
    func
  }

  def getNextFun(nextState : Map[Identifier, Expr], variables : List[(String, Type)], ctx : Scope) : String = {
    // FIXME: some variables are not primed. Why?
    val nextExprs = nextState.map(p => getEqExpr(p._1, p._2, ctx, getPrimedVariableName)).toList
    val varString = Utils.join(variables.map(p => "(" + p._1 + " " + generateDatatype(p._2)._1 + ")"), " ")
    val primeString = Utils.join(variables.map(p => "(" + p._1 + "! " + generateDatatype(p._2)._1 + ")"), " ")
    val paramString = "(" + varString + " " + primeString + ")"
    val funcBody = "(and " + Utils.join(nextExprs, " ") + ")"
    val func = "(define-fun trans-fn " + paramString + " " + funcBody + ")"
    func
  }

  def getVariables(ctx : Scope) : List[(String, Type)] = {
    (ctx.map.map {
      p => {
        val namedExpr = p._2
        namedExpr match {
          case Scope.StateVar(_, _) | Scope.InputVar(_, _) |Scope.OutputVar(_, _) | Scope.SharedVar(_, _) | Scope.ConstantVar(_, _) =>
            Some((getVariableName(namedExpr.id.name), Converter.typeToSMT(namedExpr.typ)))
          case _ =>
            None
        }
      }
    }).toList.flatten
  }

  override def synthesizeInvariant(initState : Map[Identifier, Expr], nextState: Map[Identifier, Expr], properties : List[lang.Expr], ctx : Scope) : Unit = {
    val variables = getVariables(ctx)
    val initFun = getInitFun(initState, variables, ctx)
    val transFun = getNextFun(nextState, variables, ctx)
    sygusLog.debug(nextState.toString())
    sygusLog.debug(initFun)
    sygusLog.debug(transFun)
  }

}