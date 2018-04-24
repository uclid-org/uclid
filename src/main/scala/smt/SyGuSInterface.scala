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

  def writeCommand(cmd: String) {
    println("-> " + cmd)
  }
  override def getTypeName(suffix: String) : String = {
    counterId += 1
    "_type_" + suffix + "_" + counterId.toString()
  }
  override def getVariableName(v : String) : String = {
    "_var_" + v
  }
  def getInitExpr(ident : Identifier, expr : smt.Expr, ctx : Scope) : String = {
    val typ = Converter.typeToSMT(ctx.typeOf(ident).get)
    val symbol = Symbol(ident.name, typ)
    val eqExpr : smt.Expr = OperatorApplication(EqualityOp, List(symbol, expr))
    val symbols = Context.findSymbols(eqExpr)
    val symbolsP = symbols.filter(s => !variables.contains(s.id))
    symbolsP.foreach {
      (s) => {
        val sIdP = getVariableName(s.id)
        variables += (s.id -> (sIdP, s.symbolTyp))
      }
    }
    val (trExpr, _) = translateExpr(eqExpr, Map.empty, false, writeCommand)
    trExpr.expr
  }

  def getInitFun(initState : Map[Identifier, Expr], ctx : Scope) : String = {
    val initExprs = initState.map(p => getInitExpr(p._1, p._2, ctx)).toList
    ""
  }
  override def synthesizeInvariant(initState : Map[Identifier, Expr], nextState: Map[Identifier, Expr], properties : List[lang.Expr], ctx : Scope) : Unit = {
    val initExprs = initState.map(p => getInitExpr(p._1, p._2, ctx)).toList
    sygusLog.debug("initExpr: {}", initExprs.toString())
  }
}