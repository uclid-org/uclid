package uclid.lang.modelcounts

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

  lazy val UMCDecl: PackratParser[uclid.lang.Decl] =
    positioned (TypeDecl | DefineDecl)

  lazy val AssertDecl: PackratParser[uclid.lang.SpecDecl] = positioned {
    KwAssert ~> Id ~ (":" ~> Expr <~ ";") ^^ {
      case id ~ e => l.SpecDecl(id, e, List.empty)
    }
  }
  lazy val ProofStmt: PackratParser[l.Decl] = 
    positioned ( AssertDecl );
  lazy val ProofScript: PackratParser[List[l.Decl]] = {
    KwProof ~ "{" ~> rep(ProofStmt) <~ "}"
  }
  lazy val UMCModule: PackratParser[l.Module] = positioned {
    KwModule ~> Id ~ ("{" ~> rep(UMCDecl)) ~ (ProofScript <~ "}") ^^ {
      case id ~ decls ~ proof => {
        uclid.lang.Module(id, decls ++ proof, ControlBlock, List.empty)
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