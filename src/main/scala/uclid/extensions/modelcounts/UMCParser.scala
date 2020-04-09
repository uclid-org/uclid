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
import uclid.lang.Identifier
import uclid.smt.IntLit


class UMCParser extends l.UclidParser {
  lazy val KwProof = "proof"
  lexical.reserved += (KwProof)

  lazy val ControlBlock : List[l.GenericProofCommand] = List(
    l.GenericProofCommand(
        l.Identifier("unroll"), 
        List.empty, List((l.IntLit(1), "1")), 
        Some(l.Identifier("v")), None),
    l.GenericProofCommand(
        l.Identifier("check"), 
        List.empty, List.empty, 
        None, None),
    l.GenericProofCommand(
        l.Identifier("print_results"), 
        List.empty, List.empty, 
        None, None),
    l.GenericProofCommand(
        l.Identifier("print_cex"), 
        List.empty, List.empty, 
        None, Some(l.Identifier("v")))
  )

  lazy val UMCDecl: PackratParser[l.Decl] =
    positioned (TypeDecl | DefineDecl)

  lazy val AssertStmt: PackratParser[l.AssertStmt] = positioned {
    KwAssert ~> Id ~ (":" ~> Expr <~ ";") ^^ {
      case id ~ e => l.AssertStmt(e, Some(id))
    }
  }
  lazy val ProofStmt: PackratParser[l.AssertStmt] = 
    positioned ( AssertStmt );
  lazy val ProofScript: PackratParser[List[l.AssertStmt]] = {
    KwProof ~ "{" ~> rep(ProofStmt) <~ "}"
  }
  lazy val UMCModule: PackratParser[l.Module] = positioned {
    KwModule ~> Id ~ ("{" ~> rep(UMCDecl)) ~ (ProofScript <~ "}") ^^ {
      case id ~ decls ~ proof => {
        val proc = l.ProcedureDecl(
            l.Identifier("countingProof"),           // procedure name
            l.ProcedureSig(List.empty, List.empty),  // signature
            l.BlockStmt(List.empty, proof),          // body
            List.empty, List.empty, Set.empty,       // requires, ensures, modifies
            l.ProcedureAnnotations(Set.empty))       // no annotations.
        l.Module(id, decls ++ List(proc) , ControlBlock, List.empty)
      }
    }
  }

  def parseUMCModel(filename : String, text: String): l.Module = {
    val tokens = new PackratReader(new lexical.Scanner(text))
    phrase(UMCModule)(tokens) match {
      case Success(module, _) => module
      case NoSuccess(msg, next) => throw new uclid.Utils.SyntaxError(msg, Some(next.pos), Some(filename))
    }
  }
}

object UMCParser {
  val parserObj = new UMCParser()
  val filenameAdderPass = new l.AddFilenameRewriter(None)
  def parseUMCModel(file: java.io.File) : l.Module = {
    val filePath = file.getPath()
    val text = scala.io.Source.fromFile(filePath).mkString
    filenameAdderPass.setFilename(filePath)
    filenameAdderPass.visit(
        parserObj.parseUMCModel(filePath, text), 
        l.Scope.empty).get
  }
}
