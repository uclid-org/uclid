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
class UclidLexical extends Lexical with UclidTokens with Positional {
  override def token: Parser[Token] =
    ( positioned { 'b' ~ 'v' ~> rep(digit)                             ^^ { case chars => BitVectorTypeLit(chars.mkString("")) } }
    | positioned { (letter | '_') ~ rep( letter | '_' | digit )        ^^ { case first ~ rest => processIdent(first :: rest mkString "") } }
    | positioned { digit ~ rep(digit) ~ 'b' ~ 'v' ~ digit ~ rep(digit) ^^ { case (f1 ~ r1 ~ 'b' ~ 'v' ~ f2 ~ r2) => BitVectorLit(f1 :: r1 mkString "", 10, (f2 :: r2 mkString "").toInt) } }
    | positioned { '0' ~ 'x' ~> hexDigit ~ rep( hexDigit )             ^^ { case first ~ rest => IntegerLit(first :: rest mkString "", 16) } }
    | positioned { '0' ~ 'b' ~> bit ~ rep( bit )                       ^^ { case first ~ rest => IntegerLit(first :: rest mkString "", 2) } }
    | positioned { digit ~ rep( digit )                                ^^ { case first ~ rest => IntegerLit(first :: rest mkString "", 10) } }
    | positioned { '\'' ~> rep( chrExcept('\'', '\n', EofCh) ) <~ '\'' ^^ { case chars => StringLit(chars mkString "") } }
    | positioned { '\"' ~> rep( chrExcept('\"', '\n', EofCh) ) <~ '\"' ^^ { case chars => StringLit(chars mkString "") } }
    | EofCh                                               ^^^ EOF
    | '\'' ~> failure("unclosed string literal")
    | '\"' ~> failure("unclosed string literal")
    | delim
    | failure("illegal character")
    )


  def hexDigit : Parser[Char] = elem("hexDigit", ((ch) => ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')))
  def bit : Parser[Char] = elem("bit", ((ch) => ch == '0' || ch == '1'))

  // see `whitespace in `Scanners`
  def whitespace: Parser[Any] = rep(
      whitespaceChar
    | '/' ~ '*' ~ comment
    | '/' ~ '/' ~ rep( chrExcept(EofCh, '\n') )
    | '/' ~ '*' ~ failure("unclosed comment")
    )

  protected def comment: Parser[Any] = (
      '*' ~ '/'  ^^ { case _ => ' '  }
    | chrExcept(EofCh) ~ comment
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
    def parseDelim(s: String): Parser[Token] = accept(s.toList) ^^ { x => Keyword(s) }

    val d = new Array[String](delimiters.size)
    delimiters.copyToArray(d, 0)
    scala.util.Sorting.quickSort(d)
    (d.toList map parseDelim).foldRight(failure("no matching delimiter"): Parser[Token])((x, y) => y | x)
  }
  protected def delim: Parser[Token] = _delim

}
