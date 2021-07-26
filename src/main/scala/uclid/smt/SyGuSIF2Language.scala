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
 * Authors: Kevin Cheang
 *
 * SyGuS-IF 2.0 AST definition (extends SMTLanguage).
 *
 */
package uclid
package smt

// For define-macro application as SyGuS grammar terminal
case class MacroApplication(e: Expr, defDecl: DefineSymbol, args: List[Expr])
  extends Expr (e.typ.asInstanceOf[MapType].outType)
{
  override val hashId = 317
  override val hashCode = computeHash(args, e)
  override val md5hashCode = computeMD5Hash(args, e)
  override def toString = "(" + e.toString + " " + args.tail.fold(args.head.toString)
    { (acc,i) => acc + "," + i.toString } + ")"
  override val isConstant = e.isConstant && args.forall(a => a.isConstant)
}

case class DefineSymbol(id: String, symbolTyp: lang.FunctionSig, expr: Expr)
extends Expr (smt.Converter.typeToSMT(symbolTyp.typ))
{
  override val hashId = mix(id.hashCode(), mix(symbolTyp.typ.hashCode(), 318))
  override val hashCode = computeHash(id)
  override val md5hashCode = computeMD5Hash(id, symbolTyp)
  override def toString = id.toString
}

case class SynthSymbol(id: String, symbolTyp: lang.FunctionSig, grammar: Option[GrammarSymbol], gargs: List[String], conds : List[lang.Expr]) extends Expr (smt.Converter.typeToSMT(symbolTyp.typ)) {
  override val hashId = mix(id.hashCode(), mix(symbolTyp.typ.hashCode(), 315))
  override val hashCode = computeHash
  override val md5hashCode = computeMD5Hash(id)
  override def toString = id.toString
}

case class GrammarSymbol(id: String, symbolTyp: Type, nts : List[NonTerminal]) extends Expr (symbolTyp) {
  override val hashId = mix(id.hashCode(), mix(symbolTyp.hashCode(), 316))
  override val hashCode = computeHash
  override val md5hashCode = computeMD5Hash(id, symbolTyp)
  override def toString = {
  	val nonTermDecls = Utils.join(nts.map(nt => "(" + nt.id + " " + nt.typ.toString + ")"), " ")
  	val grammarDecl = Utils.join(nts.map(_.toString), " ")
  	"(%s) (%s)".format(nonTermDecls, grammarDecl)
  }
}

case class NonTerminal(id: String, typ: Type, terms: List[GrammarTerm]) extends Hashable {
  override val hashId = 4100
  override val hashBaseId = 4100
  override def toString = {
    "(%s %s (%s))".format(id.toString, typ.toString, Utils.join(terms.map(_.toString), " "))
  }
  override val md5hashCode = computeMD5Hash(id, typ, terms)
}

case class GrammarTerm(e: Expr) extends Expr(e.typ) {
  override val hashId = 4101
  override val hashBaseId = 4101
  override def toString = e.toString
  override val md5hashCode = computeMD5Hash(e)
}