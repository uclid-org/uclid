package uclid.lang

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.CharArrayReader.EofCh
import scala.collection.mutable

trait UclidTokens extends Tokens {
  case class Keyword(chars: String) extends Token {
    override def toString = "`" + chars + "'"
  }
  /** The class of integer literal tokens */
  case class IntegerLit(chars: String, base: Int) extends Token {
    override def toString = chars.toString + "_" + base.toString
  }
  
  case class BitVectorTypeLit(chars: String) extends Token {
    val width = chars.toInt
    override def toString = "bv" + width.toString
  }

  case class BitVectorLit(chars: String, base: Int, width: Int) extends Token {
    val intValue = BigInt(chars, base)
    override def toString = "0x" + intValue.toString(16) + "bv" + width.toString
  }
  
  /** The class of string literal tokens */
  case class StringLit(chars: String) extends Token {
    override def toString = "\""+chars+"\""
  }   

  /** The class of identifier tokens */
  case class Identifier(chars: String) extends Token {
    override def toString = "identifier "+chars
  }
}

/** Uclid's lexical tokens. 
 *  Most of this code is based on the Scala library's StdLexical.
 *  We can't subclass StdLexical because it uses StdToken while we have more interesting tokens (UclidTokens).
 */
class UclidLexical extends Lexical with UclidTokens {
  override def token: Parser[Token] = 
    ( 'b' ~ 'v' ~> rep(digit)                             ^^ { case chars => BitVectorTypeLit(chars.mkString("")) } 
    | (letter | '_') ~ rep( letter | '_' | digit )                ^^ { case first ~ rest => processIdent(first :: rest mkString "") }
    | digit ~ rep(digit) ~ 'b' ~ 'v' ~ digit ~ rep(digit) ^^ { case (f1 ~ r1 ~ 'b' ~ 'v' ~ f2 ~ r2) => BitVectorLit(f1 :: r1 mkString "", 10, (f2 :: r2 mkString "").toInt) }  
    | '0' ~ 'x' ~> hexDigit ~ rep( hexDigit )             ^^ { case first ~ rest => IntegerLit(first :: rest mkString "", 16) }
    | '0' ~ 'b' ~> bit ~ rep( bit )                       ^^ { case first ~ rest => IntegerLit(first :: rest mkString "", 2) }
    | digit ~ rep( digit )                                ^^ { case first ~ rest => IntegerLit(first :: rest mkString "", 10) }
    | '\'' ~ rep( chrExcept('\'', '\n', EofCh) ) ~ '\''   ^^ { case '\'' ~ chars ~ '\'' => StringLit(chars mkString "") }
    | '\"' ~ rep( chrExcept('\"', '\n', EofCh) ) ~ '\"'   ^^ { case '\"' ~ chars ~ '\"' => StringLit(chars mkString "") }
    | EofCh                                               ^^^ EOF
    | '\'' ~> failure("unclosed string literal")       
    | '\"' ~> failure("unclosed string literal")       
    | delim                                             
    | failure("illegal character")
    )
   
  def hexDigit : Parser[Char] = elem("hexDigit", ((ch) => ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')))
  def bit : Parser[Char] = elem("bit", ((ch) => ch == '0' || ch == '1'))
   
     /** Returns the legal identifier chars, except digits. */
  def identChar = letter | elem('_')

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