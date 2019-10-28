package uclid.lang.modelcounts

import uclid.lang.{Decl, Module, UclidParser}

class UMCParser extends UclidParser {
  lazy val UMCDecl: PackratParser[Decl] =
    positioned (TypeDecl | DefineDecl)

  lazy val UMCModule: PackratParser[Module] = positioned {
    KwModule ~> Id ~ ("{" ~> rep(UMCDecl) <~ "}") ^^ {
      case id ~ decls => uclid.lang.Module(id, decls, List.empty, List.empty)
    }
  }

  def parseUMCModel(filename : String, text: String): Module = {
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
  def parseUMCModel(file: java.io.File) : Module = {
    val filePath = file.getPath()
    val text = scala.io.Source.fromFile(filePath).mkString
    filenameAdderPass.setFilename(filePath)
    filenameAdderPass.visit(
        parserObj.parseUMCModel(filePath, text), 
        uclid.lang.Scope.empty).get
  }
}