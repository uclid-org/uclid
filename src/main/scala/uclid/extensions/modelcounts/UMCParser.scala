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

import uclid.{Utils, lang => l}
import uclid.lang.{Decl, Identifier, ProcedureAnnotations, Type}
import uclid.smt.IntLit
import uclid.extensions.modelcounts.{UMCExpressions => E}

class UMCParser extends l.UclidParser {
  lazy val KwLemmas   = "lemmas"
  lazy val KwLemma    = "lemma"
  lazy val KwProof    = "proof"
  lazy val KwConstLB  = "constLB"
  lazy val KwConstUB  = "constUB"
  lazy val KwConstEq  = "constEq"
  lazy val KwUB       = "UB"
  lazy val KwAndUB    = "andUB"
  lazy val KwDisjoint = "disjoint"
  lazy val KwOr       = "or"
  lazy val KwInj      = "injectivity"
  lazy val KwIndLb    = "indLB"
  lazy val KwIndUb    = "indUB"
  lazy val KwSkolems  = "skolems"

  lexical.reserved += (KwProof, KwOr, KwConstLB, KwConstUB, KwConstEq, KwIndLb, KwSkolems, KwUB, KwAndUB,
                        KwDisjoint, KwInj, KwIndUb, KwLemmas, KwLemma)

  lazy val UMCDecl: PackratParser[l.Decl] =
    positioned (TypeDecl | DefineDecl | FuncDecl | AxiomDecl)

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

  lazy val C0: PackratParser[l.Expr] = positioned {  CountingExpr | E1 }

  override lazy val E15: PackratParser[l.Expr] = positioned {
        Literal |
        "{" ~> Expr ~ rep("," ~> Expr) <~ "}" ^^ {case e ~ es => l.Tuple(e::es)} |
        KwIf ~> ("(" ~> Expr <~ ")") ~ (KwThen ~> Expr) ~ (KwElse ~> Expr) ^^ {
          case expr ~ thenExpr ~ elseExpr => l.OperatorApplication(l.ITEOp(), List(expr, thenExpr, elseExpr))
        } |
        ConstArray |
        KwLambda ~> (IdTypeList) ~ ("." ~> Expr) ^^ { case idtyps ~ expr => l.Lambda(idtyps, expr) } |
        "(" ~> CExpr <~ ")" |
        Id <~ OpPrime ^^ { case id => l.OperatorApplication(l.GetNextValueOp(), List(id)) } |
        Id
    }

  lazy val CExpr: PackratParser[l.Expr] = positioned { C0 }

  lazy val Stmt: PackratParser[Statement] = positioned {
    KwAssert ~ KwOr ~ ":" ~>
      (CountingExpr <~ "==") ~ (CountingExpr <~ "+") ~ CountingExpr <~ ";" ^^ {
      case e1 ~ e2 ~ e3 => OrStmt(e1, e2, e3)
    } |
    KwAssert ~ KwRange ~ ":" ~> CountingExpr ~ ("==" ~> Expr) <~ ";" ^^ {
      case e1 ~ e2 => {
        RangeStmt(e1, e2) 
      }
    } |
    KwAssert ~ KwConstLB ~ ":" ~>  CountingExpr ~ (">=" ~> Integer) <~ ";" ^^ {
      case e ~ v => {
        ConstLbStmt(e, v, l.BoolLit(true))
      }
    } |
    KwAssert ~ KwConstLB ~ ":" ~>  (Expr <~ "==>") ~ CountingExpr ~ (">=" ~> Integer) <~ ";" ^^ {
      case assump ~ e ~ v => {
        ConstLbStmt(e, v, assump)
      }
    } |
    KwAssert ~ KwConstUB ~ ":" ~>  CountingExpr ~ ("<" ~> Integer) <~ ";" ^^ {
      case e ~ v => {
        ConstUbStmt(e, v, l.BoolLit(true))
      }
    } |
    KwAssert ~ KwConstUB ~ ":" ~>  (Expr <~ "==>") ~ CountingExpr ~ ("<" ~> Integer) <~ ";" ^^ {
      case assump ~ e ~ v => {
        ConstUbStmt(e, v, assump)
      }
    } |
    KwAssert ~ KwConstEq ~ ":" ~>  CountingExpr ~ ("==" ~> Integer) <~ ";" ^^ {
      case e ~ v => {
        ConstEqStmt(e, v, l.BoolLit(true))
      }
    } |
    KwAssert ~ KwConstEq ~ ":" ~> (Expr <~ "==>") ~ CountingExpr ~ ("==" ~> Integer) <~ ";" ^^ {
      case assump ~ e ~ v => {
        ConstEqStmt(e, v, assump)
      }
    } |
    KwAssert ~ KwIndLb ~ ":" ~> CountingExpr ~ (">=" ~> CountingExpr) ~ ("*" ~> CountingExpr) ~ (KwSkolems ~> ExprList <~ ";") ^^ {
      case e1 ~ e2 ~ e3 ~ es => {
        IndLbStmt(e1, e2, e3, es)
      }
    } |
    KwAssert ~ KwUB ~ ":" ~>  CountingExpr ~ ("<=" ~> CountingExpr) <~ ";" ^^ {
      case e1 ~ e2 => {
        UbStmt(e1, e2)
      }
    } |
    KwAssert ~ KwAndUB ~ ":" ~>
      (CountingExpr <~ "<=") ~ (CountingExpr <~ "*") ~ CountingExpr <~ ";" ^^ {
      case e1 ~ e2 ~ e3 => AndUbStmt(e1, e2, e3)
    } |
    KwAssert ~ KwDisjoint ~ ":" ~>
      (CountingExpr <~ "==") ~ (CountingExpr <~ "*") ~ CountingExpr <~ ";" ^^ {
      case e1 ~ e2 ~ e3 => DisjointStmt(e1, e2, e3)
    } |
    KwAssert ~ KwInj ~ ":" ~> CountingExpr ~ ("<=" ~> CountingExpr) ~ (KwSkolems ~> ExprList <~ ";") ^^ {
      case e1 ~ e2 ~ es => {
        InjectivityStmt(e1, e2, es)
      }
    } |
    KwAssert ~ KwIndUb ~ ":" ~> CountingExpr ~ ("<=" ~> CountingExpr) ~ ("*" ~> CountingExpr) ~ (KwSkolems ~> ExprList <~ ";") ^^ {
      case e1 ~ e2 ~ e3 ~ es => {
        IndUbStmt(e1, e2, e3, es)
      }
    } |
    KwAssert ~> CExpr <~ ";" ^^ {
      case e => AssertStmt(e)
    }
  }

  lazy val LemmaDecl : PackratParser[l.ProcedureDecl] = positioned {
    KwLemma ~> ProcedureAnnotationList.? ~ Id ~ IdTypeList ~ (KwReturns ~> IdTypeList) ~
      rep(ProcedureVerifExpr) ~ BlkStmt ^^
      { case annotOpt ~ id ~ args ~ outs ~ verifExprs ~ body =>
        val annotations = annotOpt match {
          case Some(ids) => ProcedureAnnotations(ids.toSet)
          case None => ProcedureAnnotations(Set.empty)
        }
        val verifExprList = verifExprs.flatMap(v => v)
        val requiresList = collectRequires(verifExprList)
        val ensuresList = collectEnsures(verifExprList)
        val modifiesList = collectModifies(verifExprList)
        l.ProcedureDecl(id, l.ProcedureSig(args,outs),
          body, requiresList, ensuresList, modifiesList.toSet, annotations) } |
      // procedure with no return value
      KwLemma ~> ProcedureAnnotationList.? ~ Id ~ IdTypeList ~ rep(ProcedureVerifExpr) ~ BlkStmt ^^
        { case annotOpt ~ id ~ args ~ verifExprs ~ body =>
          val annotations = annotOpt match {
            case Some(ids) => ProcedureAnnotations(ids.toSet)
            case None => ProcedureAnnotations(Set.empty)
          }
          val verifExprList = verifExprs.flatMap(v => v)
          val requiresList = collectRequires(verifExprList)
          val ensuresList = collectEnsures(verifExprList)
          val modifiesList = collectModifies(verifExprList)
          l.ProcedureDecl(id, l.ProcedureSig(args, List.empty),
            body, requiresList, ensuresList, modifiesList.toSet, annotations) }
  }

  lazy val LemmaDeclarations: PackratParser[l.ProcedureDecl] =
    positioned ( LemmaDecl );

  lazy val LemmaBlock: PackratParser[List[l.ProcedureDecl]] = {
    KwLemmas ~ "{" ~> rep(LemmaDeclarations) <~ "}"
  }

  lazy val ProofStmt: PackratParser[Statement] = 
    positioned ( Stmt );

  lazy val ProofScript: PackratParser[List[Statement]] = {
    KwProof ~ "{" ~> rep(ProofStmt) <~ "}"
  }

  lazy val CntProof: PackratParser[CountingProof] = positioned {
    KwModule ~> Id ~ ("{" ~> rep(UMCDecl)) ~ (ProofScript <~ "}") ^^ {
      case id ~ decls ~ proof => {
        CountingProof(id, decls, List(), proof)
      }
    } |
    KwModule ~> Id ~ ("{" ~> rep(UMCDecl)) ~ LemmaBlock ~ (ProofScript <~ "}") ^^ {
      case id ~ decls ~ lemmas ~ proof => {
        CountingProof(id, decls, lemmas, proof)
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

class RewriteDefines extends l.RewriteDefines {
  override def visitExpr(e : l.Expr, context : l.Scope) : Option[l.Expr] = {
    val eP = (e match {
      case i : Identifier => visitIdentifier(i, context)
      case eId : l.ExternalIdentifier => visitExternalIdentifier(eId, context)
      case lit : l.Literal => visitLiteral(lit, context)
      case rec : l.Tuple => visitTuple(rec, context)
      case opapp : l.OperatorApplication => visitOperatorApp(opapp, context)
      case a : l.ConstArray => visitConstArray(a, context)
      case fapp : l.FuncApplication => visitFuncApp(fapp, context)
      case lambda : l.Lambda => visitLambda(lambda, context)
      case cntOp : CountingOp =>
        visitExpr(cntOp.e, context).flatMap(eP => Some(CountingOp(cntOp.xs, cntOp.ys, eP)))
    }).flatMap(pass.rewriteExpr(_, context))
    return l.ASTNode.introducePos(true, true, eP, e.position)
  }
}
object UMCParser {
  val parserObj = new UMCParser()
  val rewriter = new RewriteDefines()
  def parseUMCModel(file: java.io.File) : CountingProof = {
    val filePath = file.getPath()
    val text = scala.io.Source.fromFile(filePath).mkString
    val model = parserObj.parseUMCModel(filePath, text)
    model.rewriteStatments(rewriter)
  }
}
