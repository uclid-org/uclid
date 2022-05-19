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

 * Defines lexical tokens for UCLID5
 *
 */


package uclid.lang

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.CharArrayReader.EofCh
import scala.collection.mutable
import scala.util.parsing.input.Positional

trait UclidTokens extends Tokens {
  abstract class UclidToken extends Token with Positional

  /** Keywords. */
  case class Keyword(chars: String) extends UclidToken {
    override def toString = "`" + chars + "'"
  }
  /** The class of integer literal tokens. */
  case class IntegerLit(chars: String, base: Int) extends UclidToken {
    override def toString = chars.toString + "_" + base.toString
  }

  /** Bitvector types. */
  case class BitVectorTypeLit(chars: String) extends UclidToken {
    val width = chars.toInt
    override def toString = "bv" + width.toString
  }

  /** Bitvector literals. */
  case class BitVectorLit(chars: String, base: Int, width: Int) extends UclidToken {
    val intValue = BigInt(chars, base)
    override def toString = "0x" + intValue.toString(16) + "bv" + width.toString
  }

  /** Float types. We only store the width and support standard IEEE floating point types */
  case class FloatTypeLit(chars: String, sig: Int) extends UclidToken {
    val exp = chars.toInt
    override def toString = "fp" + exp.toString + "_" + sig.toString
  }
  /** The class of float literal tokens. */
  /** we store the whole and fractional separately, and output straight to SMT format, as we don't need to manipulate the decimal values **/
  case class FloatLit(chars: String, frac: String,  exp: Int, sig: Int) extends UclidToken {
    val integral = BigInt(chars, 10)
    override def toString = chars.toString + "." + frac.toString + "fp" + exp.toString + "_" + sig.toString
  }

  /** The class of string literal tokens. */
  case class StringLit(chars: String) extends UclidToken {
    override def toString = "\""+chars+"\""
  }

  /** The class of identifier tokens. */
  case class Identifier(chars: String) extends UclidToken {
    override def toString = "identifier "+chars
  }
}

/** Uclid's lexical tokens.
 *  Most of this code is based on the Scala library's StdLexical.
 *  We can't subclass StdLexical because it uses StdToken while we have more interesting tokens (UclidTokens).
 */

 //TODO_leiqi: add line in here to parse float lit and float type lit!
//finish!
//when we make tokens, we does not care about the type of 3.5
//like 3.5double 3.5float 3.5half
//those can be seem as floatlist + floatType
//we can do this in Parser, which can make the code much readable
class UclidLexical extends Lexical with UclidTokens with Positional {
  
  override def token: Parser[Token] =
    ( positioned { 'b' ~ 'v' ~> digit.+                                ^^ { case chars => BitVectorTypeLit(chars.mkString("")) } }
    | positioned { 'f' ~ 'p' ~ digit ~ rep(digit) ~ '_' ~ digit ~ rep(digit) ^^ {case ('f' ~ 'p' ~ f1 ~ r1 ~ '_' ~ f2 ~ r2) => FloatTypeLit(f1 :: r1 mkString "",(f2 :: r2 mkString "").toInt)}}
    | positioned { (letter | '_') ~ rep( letter | '_' | digit )        ^^ { case first ~ rest => processIdent(first :: rest mkString "") } }
    | positioned { digit ~ rep(digit) ~ 'b' ~ 'v' ~ digit ~ rep(digit) ^^ { case (f1 ~ r1 ~ 'b' ~ 'v' ~ f2 ~ r2) => BitVectorLit(f1 :: r1 mkString "", 10, (f2 :: r2 mkString "").toInt) } }
    | positioned { '0' ~ 'x' ~ hexDigit ~ rep( hexDigit ) ~ 'b' ~ 'v' ~ digit ~ rep(digit) ^^ { case ('0' ~ 'x' ~ f1 ~ r1 ~ 'b' ~ 'v' ~ f2 ~ r2) => BitVectorLit(f1 :: r1 mkString "", 16, (f2 :: r2 mkString "").toInt) } }
    | positioned { '0' ~ 'b' ~ bit ~ rep( bit ) ~ 'b' ~ 'v' ~ digit ~ rep(digit) ^^ { case ('0' ~ 'b' ~ b ~ rb ~ 'b' ~ 'v' ~ d ~ rd) => BitVectorLit(b :: rb mkString "", 2, (d :: rd mkString "").toInt) } }
    | positioned { '0' ~ 'x' ~> rep1( hexDigit )                       ^^ { case hits => IntegerLit(hits.mkString, 16) } }
    | positioned { '0' ~ 'b' ~> rep1( bit )                            ^^ { case bits => IntegerLit(bits.mkString, 2) } }
    | positioned { digit ~ rep(digit) ~ '.' ~ digit ~ rep(digit) ^^ { case (f1 ~ r1 ~ '.' ~ f2 ~ r2) => FloatLit(f1 :: r1 mkString, f2 :: r2 mkString,11,52) } }
    | positioned { digit ~ rep( digit )                                ^^ { case first ~ rest => IntegerLit(first :: rest mkString "", 10)} }
    | positioned { '\"' ~> rep( chrExcept('\"', '\n', EofCh) ) <~ '\"' ^^ { case chars => StringLit(chars mkString "") } }
    | EofCh                                               ^^^ EOF
    | '\"' ~> failure("unclosed string literal")
    | delim
    | failure("illegal character")
    )

  def hexDigit : Parser[Char] = elem("hexDigit", ((ch) => ch.isDigit || (ch >= 'A' && ch <= 'F')))
  def bit : Parser[Char] = elem("bit", ((ch) => ch == '0' || ch == '1'))

  // see `whitespace in `Scanners`
  def whitespace: Parser[Any] = rep(
      whitespaceChar
    | '/' ~ '*' ~ comment
    | '/' ~ '/' ~ rep( chrExcept(EofCh, '\n') )
    | '/' ~ '*' ~ failure("unclosed comment")
    )

  // protected def comment: Parser[Any] = (
  //    '*' ~ '/'  ^^ { case _ => ' '  }
  //   | chrExcept(EofCh) ~ comment
  //   )
  protected def comment: Parser[Any] = (
    rep(chrExcept(EofCh, '*') | '*' ~ not('/')) ~ '*' ~ '/' 
    ^^^ ' '
    )
  /** The set of reserved identifiers: these will be returned as `Keyword`s. */
  val reserved = new mutable.HashSet[String]

  /** The set of delimiters (ordering does not matter). */
  val delimiters = new mutable.HashSet[String]

  protected def processIdent(name: String) =
    if (reserved contains name) Keyword(name) else Identifier(name)

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

