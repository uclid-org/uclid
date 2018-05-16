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
 * Parser for SMTLIB2/SyGuS S-expressions
 *
 */

package uclid
package smt

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.CharArrayReader.EofCh
import scala.collection.mutable
import scala.util.parsing.input.Positional

trait SExprTokens extends Tokens {
  abstract class SExprToken extends Token with Positional

  /** Keywords */
  case class Keyword(chars: String) extends SExprToken {
    val word = chars
    override def toString = word
  }
  /** Symbols. */
  case class Symbol(chars: String) extends SExprToken {
    val name = chars
    override def toString = name
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
  case class BitVectorLit(chars: String, base: Int) extends SExprToken {
    val value = BigInt(chars, base)
    override def toString = "#x" + value.toString(16)
  }
  /** Boolean type. */
  case class BoolLit(chars: String) extends SExprToken {
    Utils.assert(chars == "true" || chars == "false", "Expected only true or false here.")
    val value = chars == "true"
    override def toString = value.toString()
  }
}

class SExprLexical extends Lexical with SExprTokens with Positional {
  override def token: Parser[Token] =
    ( positioned { '#' ~ 'x' ~> hexDigit.+ ^^ { case chars => BitVectorLit(chars.mkString(""), 16) } }
    | positioned { '#' ~ 'b' ~> bit.+ ^^ { case chars => BitVectorLit(chars.mkString(""), 2) } }
    | positioned { digit.+ ^^ { case ds => IntegerLit(ds.mkString(""), 10) } }
    | positioned { '-' ~> digit.+ ^^ { case ds => IntegerLit("-" + ds.mkString(""), 10) } }
    | positioned { symbolStartChar ~ rep(symbolChar) ^^ { case s ~ ss => processIdent((s :: ss).mkString("")) } }
    | positioned { '\"' ~> quotedLiteralChar.+ <~ '\"' ^^ { case ls => QuotedLiteral(ls.mkString("")) } }
    | EofCh                                               ^^^ EOF
    | '\"' ~> failure("unclosed string literal")
    | delim
    | failure("illegal character")
    )

  def hexDigit : Parser[Char] = elem("hexDigit", ((ch) => ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')))
  def bit : Parser[Char] = elem("bit", ((ch) => ch == '0' || ch == '1'))
  val specialChars = "_+−∗&|!∼<>=/%?.$^"
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

  protected def processIdent(name: String) =
    if (reserved contains name) Keyword(name) else Symbol(name)

  private lazy val _delim: Parser[Token] = {
    // construct parser for delimiters by |'ing together the parsers for the individual delimiters,
    // starting with the longest one -- otherwise a delimiter D will never be matched if there is
    // another delimiter that is a prefix of D
    def parseDelim(s: String): Parser[Token] = accept(s.toList) ^^ { x => Keyword(s) }

    val d = new Array[String](delimiters.size)
    delimiters.copyToArray(d, 0)
    scala.util.Sorting.quickSort(d)
    (d.toList map parseDelim).foldRight(failure("no matching delimiter"): Parser[Token])((x, y) => y | x)
  }
  protected def delim: Parser[Token] = _delim

}

class SExprParser {
  
}