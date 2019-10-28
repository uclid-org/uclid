package uclid.lang.modelcounts

import uclid.{lang => l}


class UMCParser extends l.UclidParser {
  lazy val KwProof = "proof"
  lexical.reserved += (KwProof)

  lazy val UMCDecl: PackratParser[uclid.lang.Decl] =
    positioned (TypeDecl | DefineDecl)

  lazy val AssertStmt: PackratParser[uclid.lang.Statement] = positioned {
    KwAssert ~> Expr <~ ";" ^^ { case e => l.AssertStmt(e, None) }
  }
  lazy val ProofStmt: PackratParser[l.Statement] = 
    positioned ( AssertStmt );
  lazy val ProofScript: PackratParser[List[l.Statement]] = {
    KwProof ~ "{" ~> rep(ProofStmt) <~ "}"
  }
  lazy val UMCModule: PackratParser[l.Module] = positioned {
    KwModule ~> Id ~ ("{" ~> rep(UMCDecl)) ~ (ProofScript <~ "}") ^^ {
      case id ~ decls ~ proof => {
        val next = l.NextDecl(l.BlockStmt(List.empty, proof))
        uclid.lang.Module(id, next :: decls, List.empty, List.empty)
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
  val filenameAdderPass = new uclid.lang.AddFilenameRewriter(None)
  def parseUMCModel(file: java.io.File) : l.Module = {
    val filePath = file.getPath()
    val text = scala.io.Source.fromFile(filePath).mkString
    filenameAdderPass.setFilename(filePath)
    filenameAdderPass.visit(
        parserObj.parseUMCModel(filePath, text), 
        uclid.lang.Scope.empty).get
  }
}