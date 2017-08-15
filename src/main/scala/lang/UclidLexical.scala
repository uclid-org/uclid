package lang

import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.token.Tokens
import scala.util.parsing.input.CharArrayReader.EofCh

trait UclidTokens extends Tokens {
  case class Keyword(chars: String) extends Token {
    override def toString = "`" + chars + "'"
  }
  /** The class of numeric literal tokens */
  case class NumericLit(chars: String) extends Token {
    override def toString = chars
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

class UclidLexical extends StdLexical with UclidTokens {
  override def token: Parser[Token] = 
    ( letter ~ rep( letter | digit )                    ^^ { case first ~ rest => processIdent(first :: rest mkString "") }
    | digit ~ rep( digit )                              ^^ { case first ~ rest => NumericLit(first :: rest mkString "") }
    | '0' ~ 'x' ~ rep( hexDigit )                       ^^ { case first ~ rest => NumericLit(first :: rest mkString "") }
    | '\'' ~ rep( chrExcept('\'', '\n', EofCh) ) ~ '\'' ^^ { case '\'' ~ chars ~ '\'' => StringLit(chars mkString "") }
    | '\"' ~ rep( chrExcept('\"', '\n', EofCh) ) ~ '\"' ^^ { case '\"' ~ chars ~ '\"' => StringLit(chars mkString "") }
    | EofCh                                             ^^^ EOF
    | '\'' ~> failure("unclosed string literal")       
    | '\"' ~> failure("unclosed string literal")       
    | delim                                             
    | failure("illegal character")
    )
    
   def hexDigit : Parser[Char] = elem("hexDigit", ((ch) => ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')))
}