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
 * Parser for the UCLID model counter.
 *
 */

package uclid.extensions.modelcounts

import uclid.{lang => l}
import uclid.Utils
import uclid.lang.Identifier
import uclid.lang.Type
import uclid.smt.IntLit
import uclid.extensions.modelcounts.{UMCExpressions => E}

class UMCParser extends l.UclidParser {
  lazy val KwProof = "proof"
  lazy val KwDisjoint = "disjoint"
  lazy val KwConstLB = "constLB"
  lazy val KwConstUB = "constUB"
  
  lexical.reserved += (KwProof, KwDisjoint, KwConstLB, KwConstUB)

  lazy val UMCDecl: PackratParser[l.Decl] =
    positioned (TypeDecl | DefineDecl)

  lazy val CountingOpPrefix : PackratParser[(List[(Identifier, Type)], List[(Identifier, Type)])] = 
    ("#[" ~> IdTypeList)  ~ (KwFor ~> IdTypeList) <~ "]" ~ "::" ^^ {
      case xs ~ ys => (xs, ys)
    } |
    ("#[" ~> IdTypeList) <~ "]" ~ "::" ^^ {
      case xs => (xs, List.empty)
    }

  lazy val CountingExpr : PackratParser[CountingOp] = positioned {
    CountingOpPrefix ~ ("(" ~> Expr <~ ")") ^^ {
      case xs ~ e => CountingOp(xs._1, xs._2, e)
    }
  }

  lazy val AssertStmt: PackratParser[Statement] = positioned {
    KwAssert ~ KwDisjoint ~ ":" ~> 
      (CountingExpr <~ "==") ~ (CountingExpr <~ "+") ~ CountingExpr <~ ";" ^^ {
      case e1 ~ e2 ~ e3 => DisjointStmt(e1, e2, e3)
    } |
    KwAssert ~ KwRange ~ ":" ~> CountingExpr ~ ("==" ~> Expr) <~ ";" ^^ {
      case e1 ~ e2 => {
        RangeStmt(e1, e2) 
      }
    } |
    KwAssert ~ KwConstLB ~ ":" ~>  CountingExpr ~ (">=" ~> Integer) <~ ";" ^^ {
      case e ~ v => {
        ConstLbStmt(e, v)
      }
    } |
    KwAssert ~ KwConstUB ~ ":" ~>  CountingExpr ~ ("<" ~> Integer) <~ ";" ^^ {
      case e ~ v => {
        ConstUbStmt(e, v)
      }
    }
  }
  lazy val ProofStmt: PackratParser[Statement] = 
    positioned ( AssertStmt );
  lazy val ProofScript: PackratParser[List[Statement]] = {
    KwProof ~ "{" ~> rep(ProofStmt) <~ "}"
  }
  lazy val CntProof: PackratParser[CountingProof] = positioned {
    KwModule ~> Id ~ ("{" ~> rep(UMCDecl)) ~ (ProofScript <~ "}") ^^ {
      case id ~ decls ~ proof => {
        CountingProof(id, decls, proof)
      }
    }
  }

  def parseUMCModel(filename : String, text: String): CountingProof = {
    val tokens = new PackratReader(new lexical.Scanner(text))
    phrase(CntProof)(tokens) match {
      case Success(module, _) => module
      case NoSuccess(msg, next) => throw new uclid.Utils.SyntaxError(msg, Some(next.pos), Some(filename))
    }
  }
}

object UMCParser {
  val parserObj = new UMCParser()
  val rewriter = new l.RewriteDefines()
  def parseUMCModel(file: java.io.File) : CountingProof = {
    val filePath = file.getPath()
    val text = scala.io.Source.fromFile(filePath).mkString
    val model = parserObj.parseUMCModel(filePath, text)
    model.rewriteStatments(rewriter)
  }
}
