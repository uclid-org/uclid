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
 * Author: Pramod Subramanyan, Pranav Gaddamadugu
 *
 * Parser for solver output.
 *
 */

package uclid
package smt

import scala.collection.mutable

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.CharArrayReader.EofCh
import scala.util.parsing.combinator.token._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.PackratParsers

import scala.language.implicitConversions
import com.typesafe.scalalogging.Logger

trait SExprTokens extends Tokens {
  abstract class SExprToken extends Token

  /** Keywords */
  case class Keyword(chars: String) extends SExprToken {
    val word = chars
    override def toString = "[keyword]" + word
  }
  /** Symbols. */
  case class Symbol(chars: String) extends SExprToken {
    val name = chars
    override def toString = "[symbol]" + name
  }
  /** QuotedLiteral. */
  case class QuotedLiteral(chars: String) extends SExprToken {
    override def toString = "\"" + chars + "\""
  }
  /** The class of integer literal tokens. */
  case class IntegerLit(chars: String, base: Int) extends SExprToken {
    val value = BigInt(chars, base)
    override def toString = value.toString()
  }
  /** Bitvector types. */
  case class BitVectorLit(chars: String, base: Int, width: Int) extends SExprToken {
    val value = BigInt(chars, base)
    val numBits = width
    override def toString = "#x" + value.toString(16)
  }
  /** Boolean type. */
  case class BoolLit(chars: String) extends SExprToken {
    Utils.assert(chars == "true" || chars == "false", "Expected only true or false here.")
    val value = chars == "true"
    override def toString = value.toString()
  }
}

class SExprLexical extends Lexical with SExprTokens {
  val log = Logger(classOf[SExprLexical])
  override def token: Parser[Token] =
    ( { '#' ~ 'x' ~> hexDigit.+ ^^ { case chars => BitVectorLit(chars.mkString(""), 16, 4*chars.length) } }
    | { '#' ~ 'b' ~> bit.+ ^^ { case chars => BitVectorLit(chars.mkString(""), 2, chars.length) } }
    | { digit.+ ^^ { case ds => IntegerLit(ds.mkString(""), 10) } }
    | { '-' ~> digit.+ ^^ { case ds => IntegerLit("-" + ds.mkString(""), 10) } }
    | { symbolStartChar ~ rep(symbolChar) ^^ { case s ~ ss => processIdent((s :: ss).mkString("")) } }
    | { '\"' ~> quotedLiteralChar.+ <~ '\"' ^^ { case ls => QuotedLiteral(ls.mkString("")) } }
    | EofCh                                               ^^^ EOF
    | '\"' ~> failure("unclosed string literal")
    | delim
    | failure("illegal character")
    )

  def hexDigit : Parser[Char] = elem("hexDigit", ((ch) => ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')))
  def bit : Parser[Char] = elem("bit", ((ch) => ch == '0' || ch == '1'))
  val specialChars = "_+-*&|!~<>=/%?.$^@"
  def specialChar : Parser[Char] = elem("specialChar", ((ch) => specialChars.contains(ch)))
  def symbolStartChar: Parser[Char] = letter | specialChar
  def symbolChar: Parser[Char] = letter | specialChar | digit
  def quotedLiteralChar: Parser[Char] = letter | digit | '.'

  // see `whitespace in `Scanners`
  def whitespace: Parser[Any] = rep(
      whitespaceChar
    | ';' ~ rep( chrExcept(EofCh, '\n') )
    )

  /** The set of reserved identifiers: these will be returned as `Keyword`s. */
  val reserved = new mutable.HashSet[String]

  /** The set of delimiters (ordering does not matter). */
  val delimiters = new mutable.HashSet[String]

  protected def processIdent(name: String) = {
    val r = if (reserved contains name) Keyword(name) else Symbol(name)
    log.debug("name: {}; result: {}", name, r.toString())
    r
  }

  private lazy val _delim: Parser[Token] = {
    // construct parser for delimiters by |'ing together the parsers for the individual delimiters,
    // starting with the longest one -- otherwise a delimiter D will never be matched if there is
    // another delimiter that is a prefix of D
    def parseDelim(s: String): Parser[Token] = accept(s.toList) ^^ { _ => Keyword(s) }

    val d = new Array[String](delimiters.size)
    delimiters.copyToArray(d, 0)
    scala.util.Sorting.quickSort(d)
    (d.toList map parseDelim).foldRight(failure("no matching delimiter"): Parser[Token])((x, y) => y | x)
  }
  protected def delim: Parser[Token] = _delim

}

/** This is a re-implementation of the Scala libraries StdTokenParsers with StdToken replaced by UclidToken. */
trait SExprTokenParsers extends TokenParsers {
  type Tokens <: SExprTokens
  import lexical.{Keyword, Symbol, QuotedLiteral, IntegerLit, BitVectorLit, BoolLit}

  protected val keywordCache = mutable.HashMap[String, Parser[String]]()

  /** A parser which matches a single keyword token.
   *
   * @param chars    The character string making up the matched keyword.
   * @return a `Parser` that matches the given string
   */
  implicit def keyword(chars: String): Parser[String] =
    keywordCache.getOrElseUpdate(chars, accept(Keyword(chars)) ^^ (_.chars))

  /** A parser which matches an identifier */
  def symbol: Parser[Symbol] =
    elem("identifier", _.isInstanceOf[Symbol]) ^^ (_.asInstanceOf[Symbol])

  def quotedLiteral: Parser[QuotedLiteral] =
    elem("quoted literal", _.isInstanceOf[QuotedLiteral]) ^^ (_.asInstanceOf[QuotedLiteral])

  /** A parser which matches an integer literal */
  def integerLit: Parser[IntegerLit] =
    elem("integer", _.isInstanceOf[IntegerLit]) ^^ (_.asInstanceOf[IntegerLit])

  /** A parser which matches a bitvector literal */
  def bitvectorLit: Parser[BitVectorLit] =
    elem("bitvector", _.isInstanceOf[BitVectorLit]) ^^ (_.asInstanceOf[BitVectorLit])

  def boolLit: Parser[BoolLit] =
    elem("bool", _.isInstanceOf[BoolLit]) ^^ (_.asInstanceOf[BoolLit])
}

object SExprParser extends SExprTokenParsers with PackratParsers {
  type Tokens = SExprTokens
  val lexical = new SExprLexical

  // an implicit keyword function that gives a warning when a given word is not in the reserved/delimiters list
  override implicit def keyword(chars : String): Parser[String] = {
    if(lexical.reserved.contains(chars) || lexical.delimiters.contains(chars)) super.keyword(chars)
    else failure("You are trying to parse \""+chars+"\", but it is neither contained in the delimiters list, nor in the reserved keyword list of your lexical object")
  }

  lazy val OpAnd = "and"
  lazy val OpOr = "or"
  lazy val OpNot = "not"
  lazy val OpITE = "ite"
  lazy val OpImpl = "=>"
  lazy val OpEq = "="
  lazy val OpIntGT = ">"
  lazy val OpIntLT = "<"
  lazy val OpIntGE = ">="
  lazy val OpIntLE = "<="
  lazy val OpIntAdd = "+"
  lazy val OpIntSub = "-"
  lazy val OpIntMul = "*"
  lazy val OpBVAdd = "bvadd"
  lazy val OpBVSub = "bvsub"
  lazy val OpBVMul = "bvmul"
  lazy val OpBVNeg = "bvneg"
  lazy val OpBVAnd = "bvand"
  lazy val OpBVOr  = "bvor"
  lazy val OpBVXor = "bvxor"
  lazy val OpBVNot = "bvnot"
  lazy val OpBVUrem = "bvurem"
  lazy val OpBVSrem = "bvsrem"
  lazy val OpBVGTU = "bvugt"
  lazy val OpBVGT = "bvsgt"
  lazy val OpBVGEU = "bvuge"
  lazy val OpBVGE = "bvsge"
  lazy val OpBVLTU = "bvslt"
  lazy val OpBVLT = "bvslt"
  lazy val OpBVLEU = "bvule"
  lazy val OpBVLE = "bvsle"
  lazy val OpConcat= "concat"
  lazy val OpArraySelect = "select"
  lazy val OpArrayStore = "store"
  lazy val KwTrue = "true"
  lazy val KwFalse = "false"


  lazy val KwModel = "model"  // The "model" keyword is specific to Boolector 
  lazy val KwInt = "Int"
  lazy val KwBool = "Bool"
  lazy val KwBV = "BitVec"
  lazy val KwArray = "Array"
  lazy val KwLambda = "lambda"
 
  // Reserved words
  lazy val KwBINARY = "BINARY"
  lazy val KwDECIMAL = "DECIMAL"
  lazy val KwHEXADECIMAL = "HEXADECIMAL"
  lazy val KwNUMERAL = "NUMERAL"
  lazy val KwSTRING = "STRING"
  lazy val KwUS = "_"
  lazy val KwBang = "!"
  lazy val KwAs = "as"

  lazy val KwLet = "let"
  lazy val KwExists = "exists"
  lazy val KwForall = "forall"
  lazy val KwMatch = "match"
  lazy val KwPar = "par"
  lazy val KwDefFun = "define-fun"

  // Need to add to deal with Z3 output
  lazy val KwDecFun = "declare-fun"
  


  lexical.delimiters += ("(", ")")
  lexical.reserved += (
      // General reserved
      KwBang, KwUS, KwAs, KwBINARY, KwDECIMAL, KwExists, KwHEXADECIMAL, 
      KwForall, KwLet, KwMatch, KwNUMERAL, KwPar, KwSTRING, KwDefFun,
      KwDecFun,
    
      
      // For UCLID
      KwFalse,  KwTrue, KwModel, KwInt, KwBool, KwBV, KwArray, KwLambda,
      OpAnd, OpOr, OpNot, OpITE, OpImpl, OpEq, OpIntGE, OpIntGT, OpIntLT,
      OpIntLE, OpIntAdd, OpIntSub, OpIntMul, OpBVAdd, OpBVSub, OpBVMul, OpBVNeg, 
      OpBVAnd, OpBVOr, OpBVXor, OpBVNot, OpBVUrem, OpBVSrem, OpBVGT, OpBVGTU, 
      OpBVGE, OpBVGEU, OpBVLT, OpBVLTU, OpBVLE, OpBVLEU, OpConcat, OpArraySelect, OpArrayStore
  )

  lazy val Operator : PackratParser[smt.Operator] =
    OpAnd ^^ { _ => smt.ConjunctionOp } |
    OpOr ^^ { _ => smt.DisjunctionOp } |
    OpNot ^^ { _ => smt.NegationOp } |
    OpITE ^^ {_ => smt.ITEOp } |
    OpImpl ^^ { _ => smt.ImplicationOp } |
    OpEq ^^ { _ => smt.EqualityOp } |
    OpIntGE ^^ { _ => smt.IntGEOp } |
    OpIntGT ^^ { _ => smt.IntGTOp } |
    OpIntLT ^^ { _ => smt.IntLTOp } |
    OpIntLE ^^ { _ => smt.IntLEOp } |
    OpIntAdd ^^ { _ => smt.IntAddOp } |
    OpIntSub ^^ { _ => smt.IntSubOp } |
    OpIntMul ^^ { _ => smt.IntMulOp } |
    OpBVAdd ^^ { _ => smt.BVAddOp(0) } |
    OpBVSub ^^ { _ => smt.BVSubOp(0) } |
    OpBVMul ^^ { _ => smt.BVMulOp(0) } |
    OpBVNeg ^^ { _ => smt.BVMinusOp(0) }|
    OpBVAnd ^^ { _ => smt.BVAndOp(0) } |
    OpBVOr ^^ { _ => smt.BVOrOp(0) } |
    OpBVXor ^^ { _ => smt.BVXorOp(0) } |
    OpBVNot ^^ { _ => smt.BVNotOp(0) } |
    OpBVUrem ^^ { _ => smt.BVUremOp(0) } |
    OpBVSrem ^^ { _ => smt.BVSremOp(0) } |
    OpBVGTU ^^ { _ => smt.BVGTUOp(0)} | 
    OpBVGEU ^^ { _ => smt.BVGEUOp(0)} | 
    OpBVLEU ^^ { _ => smt.BVLEUOp(0)} | 
    OpBVLTU ^^ { _ => smt.BVLTUOp(0)} | 
    OpBVGT ^^ { _ => smt.BVGTOp(0)} | 
    OpBVGT ^^ { _ => smt.BVGEOp(0)} | 
    OpBVLE ^^ { _ => smt.BVLEOp(0)} | 
    OpBVLT ^^ { _ => smt.BVLTOp(0)} | 
    OpConcat ^^ { _ => smt.BVConcatOp(0) }

  lazy val Symbol : PackratParser[smt.Symbol] =
    symbol ^^ { sym => smt.Symbol(sym.name, smt.UndefinedType) } 

  lazy val IntegerLit : PackratParser[smt.IntLit] =
    integerLit ^^ { iLit => smt.IntLit(iLit.value) }

  lazy val BitVectorLit : PackratParser[smt.BitVectorLit] =
    bitvectorLit ^^ { bvLit => smt.BitVectorLit(bvLit.value, bvLit.numBits) }

  lazy val BoolLit : PackratParser[smt.BooleanLit] =
    KwTrue ^^ { _ => smt.BooleanLit(true) } |
    KwFalse ^^ { _ => smt.BooleanLit(false) }

  lazy val Type : PackratParser[smt.Type] =
    KwInt ^^ { _ => smt.IntType } |
    KwBool ^^ { _ => smt.BoolType } |
    "(" ~ KwBV ~> integerLit <~ ")" ^^ { case i => smt.BitVectorType(i.value.toInt) } |
    "(" ~ KwUS ~ KwBV ~> integerLit <~ ")" ^^ { case i => smt.BitVectorType(i.value.toInt) } |
    "(" ~ KwArray ~> Type ~ Type <~ ")" ^^ { case inType ~ outType => smt.ArrayType(List(inType), outType) } |
    "(" ~> symbol ~ rep1(Type) <~ ")" ^^ { case _ ~ typs => smt.TupleType(typs) } |
    symbol ^^ { sym =>  smt.UninterpretedType(sym.name) }
    
  lazy val FunArg : PackratParser[smt.Symbol] =
    "(" ~> symbol ~ Type <~ ")" ^^ { case sym ~ typ => smt.Symbol(sym.name, typ) }

  lazy val FunArgs : PackratParser[List[smt.Symbol]] =
    "(" ~> rep(FunArg) <~ ")"

  lazy val Binding : PackratParser[(smt.Symbol, smt.Expr)] = 
    "(" ~> Symbol ~ Expr <~ ")" ^^ { case sym ~ expr => (sym, expr) }

  lazy val Bindings : PackratParser[List[(smt.Symbol, smt.Expr)]] = 
    "(" ~> rep1(Binding) <~ ")"

  lazy val Identifier : PackratParser[smt.Expr] = 
    Symbol | 
    //TODO: Add support for indexed identifiers in Uclid SMT
    "(" ~ KwUS ~> Symbol ~ rep1(Symbol|IntegerLit) <~ ")" ^^ { case sym ~ idxs => 
      {
        val funcType = MapType(idxs.map(a => a.typ), sym.symbolTyp)
        smt.FunctionApplication(smt.Symbol(sym.id, funcType), idxs) 
      }
    }

  lazy val QualIdentifier : PackratParser[smt.Expr] = 
    Identifier |
    "(" ~ KwAs ~> Identifier ~ Type <~ ")" ^^ { case sym ~ typ => 
      {
        val e = sym match {
          case s : smt.Symbol => s
          case f : smt.FunctionApplication => f.e.asInstanceOf[smt.Symbol]
        }
        smt.Symbol(e.id, typ) 
      }
    }


  
  lazy val Expr : PackratParser[smt.Expr] =
    BitVectorLit | 
    BoolLit |
    IntegerLit |
    QualIdentifier |
    "(" ~> Operator ~ Expr.+ <~ ")" ^^ { case op ~ args => smt.OperatorApplication(op, args)} |
    "(" ~ KwLambda ~> FunArgs ~ Expr <~ ")" ^^ { case args ~ expr => smt.Lambda(args, expr) } |
    "(" ~ KwLet ~> Bindings ~ Expr <~ ")" ^^ { case bindings ~ expr => smt.LetExpression(bindings, expr) } |
    "(" ~ KwForall ~> FunArgs ~ Expr <~ ")" ^^ { case args ~ expr => 
      {
        //TODO: Do we want patterns?
        val op = smt.ForallOp(args, List.empty)
        smt.OperatorApplication(op, List(expr))  
      }
    } |
    "(" ~> QualIdentifier ~ Expr.+ <~ ")" ^^ { case q ~ args => 
      {
        val e = q match {
          case s : smt.Symbol => s
          case f : smt.FunctionApplication => f.e.asInstanceOf[smt.Symbol]
        }
        val funcType = MapType(args.map(a => a.typ), e.symbolTyp)
        val sym = smt.Symbol(e.id, funcType)
        smt.FunctionApplication(sym, args) 
      }
    } |
    "(" ~ OpArraySelect ~> Expr ~ rep(Expr) <~ ")" ^^ { case array ~ indices => smt.ArraySelectOperation(smt.Symbol(array.toString, smt.ArrayType(Nil, array.typ)), indices) } |
    // TODO: Remove these array ops, they don't technically belong here; 
    "(" ~ OpArrayStore ~> Expr ~ Expr ~ Expr <~ ")" ^^ { case array ~ indices ~ value => smt.ArrayStoreOperation(array, List(indices), value) }

    
    



  
  lazy val DefineFun : PackratParser[smt.DefineFun] =
    "(" ~ KwDefFun ~> symbol ~ FunArgs ~ Type ~ Expr <~ ")" ^^ {
      case id ~ args ~ rTyp ~ expr => {
        val funcType = MapType(args.map(a => a.typ), rTyp)
        smt.DefineFun(smt.Symbol(id.name, funcType), args, expr)
      }
    } 
  
  
  // Necessary addition to support Z3 output format
  lazy val DeclareFun : PackratParser[smt.DeclareFun] = 
    "(" ~ KwDecFun ~> symbol ~ FunArgs ~ Type <~ ")" ^^ {
      case id ~ args ~ rTyp => {
        val funcType = MapType(args.map(a => a.typ) , rTyp)
        smt.DeclareFun(smt.Symbol(id.name, funcType), args)
      }
    }

  lazy val AssignmentModel : PackratParser[smt.AssignmentModel] =
    "(" ~ KwModel ~> rep(DeclareFun | DefineFun | Expr) <~ ")" ^^ { case exprs => smt.AssignmentModel(exprs) } |
    "(" ~> rep(DefineFun) <~ ")" ^^ { case functions => smt.AssignmentModel(functions) }


  /*
    Now we have parsing to UclidLanguage
  */
  lazy val UclidOperator : PackratParser[(lang.Operator, String)] =
    OpAnd ^^ { _ => (lang.ConjunctionOp(), OpAnd) } |
    OpOr ^^ { _ => (lang.DisjunctionOp(), OpOr) } |
    OpNot ^^ { _ => (lang.NegationOp(), OpNot) } |
    OpITE ^^ { _ => (lang.ITEOp(), OpITE) } |
    OpImpl ^^ { _ => (lang.ImplicationOp(), OpImpl) } |
    OpEq ^^ { _ => (lang.EqualityOp(), OpEq) } |
    OpIntGE ^^ { _ => (lang.IntGEOp(), OpIntGE) } |
    OpIntGT ^^ { _ => (lang.IntGTOp(), OpIntGT) } |
    OpIntLT ^^ { _ => (lang.IntLTOp(), OpIntLT) } |
    OpIntLE ^^ { _ => (lang.IntLEOp(), OpIntLE) } |
    OpIntAdd ^^ { _ => (lang.IntAddOp(), OpIntAdd) } |
    OpIntSub ^^ { _ => (lang.IntSubOp(), OpIntSub) } |
    OpIntMul ^^ { _ => (lang.IntMulOp(), OpIntMul) } |
    OpBVAdd ^^ { _ => (lang.BVAddOp(0), OpBVAdd) } |
    OpBVSub ^^ { _ => (lang.BVSubOp(0), OpBVSub) } |
    OpBVMul ^^ { _ => (lang.BVMulOp(0), OpBVMul) } |
    OpBVNeg ^^ { _ => (lang.BVUnaryMinusOp(0), OpBVNeg) } |
    OpBVAnd ^^ { _ => (lang.BVAndOp(0), OpBVAnd) } |
    OpBVOr ^^ { _ => (lang.BVOrOp(0), OpBVOr) } |
    OpBVXor ^^ { _ => (lang.BVXorOp(0), OpBVXor) } |
    OpBVNot ^^ { _ => (lang.BVNotOp(0), OpBVNot) } |
    OpBVUrem ^^ { _ => (lang.BVUremOp(0), OpBVUrem) } |
    OpBVSrem ^^ { _ => (lang.BVSremOp(0), OpBVSrem) } |
    OpBVGTU ^^ { _ => (lang.BVGTUOp(0), OpBVGTU) } |
    OpBVGEU ^^ { _ => (lang.BVGEUOp(0), OpBVGEU) } |
    OpBVLEU ^^ { _ => (lang.BVLEUOp(0), OpBVLEU) } |
    OpBVLTU ^^ { _ => (lang.BVLTUOp(0), OpBVLTU) } |
    OpBVGT ^^ { _ => (lang.BVGTOp(0), OpBVGT) } |
    OpBVGT ^^ { _ => (lang.BVGEOp(0), OpBVGT) } |
    OpBVLE ^^ { _ => (lang.BVLEOp(0), OpBVLE) } |
    OpBVLT ^^ { _ => (lang.BVLTOp(0), OpBVLT) } |
    OpConcat ^^ { _ => (lang.ConcatOp(), OpConcat) }

  def joinWithSpace (tokens : String*) : String = "(" + tokens.mkString(" ") + ")"

  lazy val UclidSymbol : PackratParser[(lang.UIdentifier, String)] =
    symbol ^^ { sym => (lang.Identifier(sym.name), sym.name) }

  lazy val UclidIntegerLit : PackratParser[(lang.IntLit, String)] =
    integerLit ^^ { iLit => (lang.IntLit(iLit.value), iLit.chars) }

  lazy val UclidBitVectorLit : PackratParser[(lang.BitVectorLit, String)] =
    bitvectorLit ^^ { bvLit => (lang.BitVectorLit(bvLit.value, bvLit.numBits),
        bvLit.base match {
          case 2  => "#b" + bvLit.chars
          case 16 => "#b" + bvLit.chars
          case _  => throw new Utils.RuntimeError("lexical.BitVectorLit has unsupported base!")
        }
      )
    }

  lazy val UclidBoolLit : PackratParser[(lang.BoolLit, String)] =
    KwTrue ^^ { _ => (lang.BoolLit(true), KwTrue) } |
    KwFalse ^^ { _ => (lang.BoolLit(false), KwFalse) }

  lazy val UclidType : PackratParser[(lang.Type, String)] =
    KwInt ^^ { _ => (lang.IntegerType(), KwInt) } |
    KwBool ^^ { _ => (lang.BooleanType(), KwBool) } |
    "(" ~ KwBV ~> integerLit <~ ")" ^^ {
      case i => (lang.BitVectorType(i.value.toInt), joinWithSpace(KwBV, i.chars)) } |
    "(" ~ KwUS ~ KwBV ~> integerLit <~ ")" ^^ {
      case i => (lang.BitVectorType(i.value.toInt), joinWithSpace(KwUS, KwBV, i.chars))
    } |
    "(" ~ KwArray ~> UclidType ~ UclidType <~ ")" ^^ {
      case inType ~ outType => (lang.ArrayType(List(inType._1), outType._1), joinWithSpace(KwArray, inType._2, outType._2))
    } |
    "(" ~> symbol ~ rep1(UclidType) <~ ")" ^^ {
      case sym ~ typs => (lang.TupleType(typs.map(a => a._1)), joinWithSpace(sym.name, typs.map(a => a._2).mkString(" ")))
    } |
    symbol ^^ { sym =>  (lang.UninterpretedType(lang.Identifier(sym.name)), sym.name) }

  lazy val UclidFunArg : PackratParser[((lang.Identifier, lang.Type), String)] =
    "(" ~> symbol ~ UclidType <~ ")" ^^ { case sym ~ typ => ((lang.Identifier(sym.name), typ._1), joinWithSpace(sym.name, typ._2)) }

  lazy val UclidFunArgs : PackratParser[(List[(lang.Identifier, lang.Type)], String)] =
    "(" ~> rep(UclidFunArg) <~ ")" ^^ {
      case args => (args.map(a => a._1), joinWithSpace(args.map(a => a._2).mkString(" ")))
    }

  // lazy val UclidBinding : PackratParser[(lang.Identifier, lang.Type, lang.Expr)] =
  //   "(" ~> UclidSymbol ~ UclidExpr <~ ")" ^^ { case sym ~ expr => (sym._1, sym._2, expr) }

  // lazy val UclidBindings : PackratParser[List[(lang.Identifier, lang.Type, lang.Expr)]] =
  //   "(" ~> rep1(UclidBinding) <~ ")"

  lazy val UclidIdentifier : PackratParser[(lang.UIdentifier, String)] =
    UclidSymbol |
    "(" ~ KwUS ~> UclidSymbol ~ rep1(UclidSymbol|UclidIntegerLit) <~ ")" ^^ { case sym ~ idxs =>
      (lang.IndexedIdentifier(sym._1.toString, idxs.map(a => a._1.asInstanceOf[Either[lang.IntLit, lang.Identifier]])),
        joinWithSpace(KwUS, sym._2, idxs.map(a => a._2).mkString(" ")))
    }

  lazy val UclidQualIdentifier : PackratParser[(lang.QIdentifier, String)] =
    UclidIdentifier |
    "(" ~ KwAs ~> UclidIdentifier ~ UclidType <~ ")" ^^ { case sym ~ typ =>
      (lang.QualifiedIdentifier(sym._1, typ._1), joinWithSpace(KwAs, sym._2, typ._2))
    }

  lazy val UclidExpr : PackratParser[(lang.Expr, String)] =
    UclidBitVectorLit |
    UclidBoolLit |
    UclidIntegerLit |
    UclidQualIdentifier |
    "(" ~> UclidOperator ~ UclidExpr.+ <~ ")" ^^ {
      case op ~ args => (lang.OperatorApplication(op._1, args.map(a => a._1)), joinWithSpace(op._2, args.map(a => a._2).mkString(" ")))
    } |
    "(" ~ KwLambda ~> UclidFunArgs ~ UclidExpr <~ ")" ^^ {
      case args ~ expr => (lang.Lambda(args._1, expr._1), joinWithSpace(KwLambda, args._2, expr._2))
    } |
    // "(" ~ KwLet ~> UclidBindings ~ UclidExpr <~ ")" ^^ { case bindings ~ expr => lang.LetTerm(bindings, expr) } |
    "(" ~ KwForall ~> UclidFunArgs ~ UclidExpr <~ ")" ^^ {
      case args ~ expr => {
        //TODO: Do we want patterns?
        val op = lang.ForallOp(args._1, List.empty)
        (lang.OperatorApplication(op, List(expr._1)), joinWithSpace(KwForall, args._2, expr._2))
      }
    } |
    "(" ~> UclidQualIdentifier ~ UclidExpr.+ <~ ")" ^^ { case q ~ args =>
      {
        (lang.QualifiedIdentifierApplication(q._1, args.map(a => a._1)), joinWithSpace(q._2, args.map(a => a._2).mkString(" ")))
      }
    } |
    "(" ~ OpArraySelect ~> UclidExpr ~ rep(UclidExpr) <~ ")" ^^ {
      case array ~ indices => (
        lang.OperatorApplication(lang.ArraySelect(indices.map(a => a._1)), List(array._1)),
        joinWithSpace(OpArraySelect, array._2, indices.map(a => a._2).mkString(" "))
      )
    } |
    // TODO: Remove these array ops, they don't technically belong here,
    // ! Why?
    "(" ~ OpArrayStore ~> UclidExpr ~ UclidExpr ~ UclidExpr <~ ")" ^^ {
      case array ~ indices ~ value => (
        lang.OperatorApplication(lang.ArrayUpdate(List(indices._1), value._1), List(array._1)),
        joinWithSpace(OpArrayStore, array._2, indices._2, value._2)
      )
    }

  lazy val UclidDefineFun : PackratParser[(lang.DefineDecl, String)] =
    "(" ~ KwDefFun ~> symbol ~ UclidFunArgs ~ UclidType ~ UclidExpr <~ ")" ^^ {
      case id ~ args ~ rTyp ~ expr => {
        (lang.DefineDecl(lang.Identifier(id.name), lang.FunctionSig(args._1, rTyp._1), expr._1),
          joinWithSpace(KwDefFun, id.name, args._2, rTyp._2, expr._2)
        )
      }
    }
  
  // Necessary addition to support Z3 output format
  lazy val UclidDeclareFun : PackratParser[(lang.FunctionDecl, String)] =
    "(" ~ KwDecFun ~> symbol ~ UclidFunArgs ~ UclidType <~ ")" ^^ {
      case id ~ args ~ rTyp => {
        (lang.FunctionDecl(lang.Identifier(id.name), lang.FunctionSig(args._1, rTyp._1)),
          joinWithSpace(KwDecFun, id.name, args._2, rTyp._2)
        )
      }
    }

  lazy val UclidAssignmentModel : PackratParser[(lang.AssignmentModel, String)] =
    "(" ~ KwModel ~> rep(UclidDefineFun) <~ ")" ^^ {
      case exprs => {
        val hmap = exprs.map(a => (a._1.id, a._2)).toMap
        (lang.AssignmentModel(exprs.map(a => a._1), hmap), joinWithSpace(KwModel, exprs.map(a => a._2).mkString("\n")))
      }
    } |
    "(" ~> rep(UclidDefineFun) <~ ")" ^^ {
      case functions => {
        val hmap = functions.map(a => (a._1.id, a._2)).toMap
        (lang.AssignmentModel(functions.map(a => a._1), hmap), joinWithSpace(functions.map(a => a._2).mkString("\n")))
      }
    }

  def parseFunction(text: String): DefineFun = {
    val tokens = new PackratReader(new lexical.Scanner(text))
    phrase(DefineFun)(tokens) match {
      case Success(function, _) =>
        function
      case NoSuccess(msg, _) =>
        throw new Utils.SyGuSParserError("SExpr function parser error: %s.\nIn: %s".format(msg, text))
    }
  }

  def parseModel(text : String) : AssignmentModel = {
    val tokens = new PackratReader(new lexical.Scanner(text))
    phrase(AssignmentModel)(tokens) match {
      case Success(model, _) => model
      case NoSuccess(msg, next) =>
        UclidMain.printError(next.pos.toString)
        throw new Utils.RuntimeError("SExpr model parser error: %s.\nIn: %s".format(msg, text))
    }
  }

  def parseModelUclidLang(text : String) : lang.AssignmentModel = {
    val tokens = new PackratReader(new lexical.Scanner(text))
    phrase(UclidAssignmentModel)(tokens) match {
      case Success(model, _) => model._1
      case NoSuccess(msg, next) =>
        UclidMain.printError(next.pos.toString)
        throw new Utils.RuntimeError("SExpr model parser error: %s.\nIn: %s".format(msg, text))
    }
  }
}
