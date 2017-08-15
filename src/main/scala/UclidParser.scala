/**
 * Created by Rohit Sinha on 5/21/15.
 */

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.PackratParsers

object UclidParser extends StandardTokenParsers with PackratParsers {
  lazy val OpAnd = "&&"
  lazy val OpOr = "||"
  lazy val OpAdd = "+"
  lazy val OpMul = "*"
  lazy val OpBiImpl = "<==>"
  lazy val OpImpl = "==>"
  lazy val OpLT = "<"
  lazy val OpGT = ">"
  lazy val OpLE = "<="
  lazy val OpGE = ">="
  lazy val OpEQ = "=="
  lazy val OpNE = "!="
  lazy val OpConcat = "++"
  lazy val OpNeg = "!"
  lazy val OpMinus = "-"
  lazy val KwProcedure = "procedure"
  lazy val KwBool = "bool"
  lazy val KwInt = "int"
  lazy val KwEnum = "enum"
  lazy val KwRecord = "record"
  lazy val KwReturns = "returns"
  lazy val KwAssume = "assume"
  lazy val KwAssert = "assert"
  lazy val KwHavoc = "havoc"
  lazy val KwVar = "var"
  lazy val KwConst = "const"
  lazy val KwLocalVar = "localvar"
  lazy val KwSkip = "skip"
  lazy val KwCall = "call"
  lazy val KwIf = "if"
  lazy val KwElse = "else"
  lazy val KwCase = "case"
  lazy val KwEsac = "esac"
  lazy val KwFor = "for"
  lazy val KwIn = "in"
  lazy val KwRange = "range"
  lazy val KwType = "type"
  lazy val KwInput = "input"
  lazy val KwOutput = "output"
  lazy val KwInit = "init"
  lazy val KwNext = "next"
  lazy val KwModule = "module"
  lazy val KwITE = "ITE"
  lazy val KwLambda = "Lambda"
  lazy val KwFunction = "function"
  
  lazy val KwDefineProp = "property"
  lazy val TemporalOpGlobally = "G"
  lazy val TemporalOpFinally = "F"
  lazy val TemporalOpNext = "Next"
  lazy val TemporalOpUntil = "U"
  lazy val TemporalOpWUntil = "W"
  lazy val TemporalOpRelease = "R"

  lexical.delimiters ++= List("(", ")", ",", "[", "]", 
    "bv", "{", "}", ";", "=", ":=", ":", ".", "->", "*",
    OpAnd, OpOr, OpAdd, OpMul, OpBiImpl, OpImpl,
    OpLT, OpGT, OpLE, OpGE, OpEQ, OpNE, OpConcat, OpNeg, OpMinus)
  lexical.reserved += (OpAnd, OpOr, OpAdd, OpMul, OpBiImpl, OpImpl,
    OpLT, OpGT, OpLE, OpGE, OpEQ, OpNE, OpConcat, OpNeg, OpMinus,
    "false", "true", "bv", KwProcedure, KwBool, KwInt, KwReturns,
    KwAssume, KwAssert, KwVar, KwLocalVar, KwHavoc, KwCall, KwIf, KwElse,
    KwCase, KwEsac, KwFor, KwIn, KwRange, KwLocalVar, KwInput, KwOutput,
    KwModule, KwType, KwEnum, KwRecord, KwSkip, KwFunction, 
    KwInit, KwNext, KwITE, KwLambda)

  lazy val ast_binary: UclExpr ~ String ~ UclExpr => UclExpr = {
    case x ~ TemporalOpUntil   ~ y => UclTemporalOpUntil(x, y)
    case x ~ TemporalOpWUntil  ~ y => UclTemporalOpWUntil(x, y)
    case x ~ TemporalOpRelease ~ y => UclTemporalOpRelease(x, y)
    case x ~ OpBiImpl ~ y => UclBiImplication(x, y)
    case x ~ OpImpl ~ y => UclImplication(x, y)
    case x ~ OpAnd ~ y => UclConjunction(x, y)
    case x ~ OpOr ~ y => UclDisjunction(x, y)
    case x ~ OpLT ~ y => UclIFuncApplication(UclLTOperator(), List(x,y))
    case x ~ OpGT ~ y => UclIFuncApplication(UclLTOperator(), List(x,y))
    case x ~ OpLE ~ y => UclIFuncApplication(UclLTOperator(), List(x,y))
    case x ~ OpGE ~ y => UclIFuncApplication(UclLTOperator(), List(x,y))
    case x ~ OpEQ ~ y => UclEquality(x, y)
    case x ~ OpNE ~ y => UclNegation(UclEquality(x, y))
    case x ~ OpConcat ~ y => UclIFuncApplication(UclConcatOperator(), List(x,y))
    case x ~ OpAdd ~ y => UclIFuncApplication(UclAddOperator(), List(x,y))
    case x ~ OpMul ~ y => UclIFuncApplication(UclMulOperator(), List(x,y))
  }

  lazy val RelOp: Parser[String] = OpGT | OpLT | OpEQ | OpNE | OpGE | OpLE
  lazy val UnOp: Parser[String] = OpNeg | OpMinus
  lazy val RecordSelectOp: Parser[UclIdentifier] = ("." ~> Id)
  lazy val ArraySelectOp: Parser[List[UclExpr]] =
    ("[" ~> Expr ~ rep("," ~> Expr) <~ "]") ^^ 
    {case e ~ es => (e :: es)}
  lazy val ArrayStoreOp: Parser[(List[UclExpr],UclExpr)] =
    ("[" ~> (Expr ~ rep("," ~> Expr) ~ (":=" ~> Expr)) <~ "]") ^^ 
    {case e ~ es ~ r => (e :: es, r)}
  lazy val ExtractOp: Parser[UclExtractOperator] =
    ("[" ~> Number ~ ":" ~ Number <~ "]") ^^ { case x ~ ":" ~ y => UclExtractOperator(x, y) }
  lazy val Id: PackratParser[UclIdentifier] = ident ^^ {case i => UclIdentifier(i)}
  lazy val Bool: PackratParser[UclBoolean] =
    "false" ^^ { _ => UclBoolean(false) } | "true" ^^ { _ => UclBoolean(true) }
  lazy val Number: PackratParser[UclNumber] = numericLit ^^ { case i => UclNumber(BigInt(i)) }
//  lazy val Bitvector: PackratParser[UclBitVector] = (numericLit ~ "bv" ~ numericLit) ^^
//    { case h ~ "bv" ~ l => UclBitVector(h.toInt, l.toInt) }

  lazy val TemporalExpr0: PackratParser[UclExpr] = 
      TemporalExpr1 ~ TemporalOpUntil  ~ TemporalExpr0 ^^ ast_binary | TemporalExpr1 
  lazy val TemporalExpr1: PackratParser[UclExpr] =
    TemporalExpr2 ~ TemporalOpWUntil  ~ TemporalExpr1 ^^ ast_binary | TemporalExpr2
  lazy val TemporalExpr2: PackratParser[UclExpr] =
    TemporalExpr3 ~ TemporalOpRelease  ~ TemporalExpr2 ^^ ast_binary | TemporalExpr3
  lazy val TemporalExpr3: PackratParser[UclExpr] = 
    TemporalOpFinally ~> TemporalExpr4 ^^ { case expr => UclTemporalOpFinally(expr) } | TemporalExpr4
  lazy val TemporalExpr4: PackratParser[UclExpr] = 
    TemporalOpGlobally ~> TemporalExpr5 ^^ { case expr => UclTemporalOpGlobally(expr) } | TemporalExpr5
  lazy val TemporalExpr5: PackratParser[UclExpr] = 
    TemporalOpNext ~> E0 ^^ { case expr => UclTemporalOpNext(expr) } | E0
    
  /** E0 := E1 OpEquiv E0 | E1  **/
  lazy val E0: PackratParser[UclExpr] = E1 ~ OpBiImpl ~ E0 ^^ ast_binary | E1
  /** E1 := E2 OpImpl E1 | E2  **/
  lazy val E1: PackratParser[UclExpr] = E2 ~ OpImpl ~ E1 ^^ ast_binary | E2
  /** E2 := E3 OpAnd E2 | E3 OpOr E2 | E3 **/
  lazy val E2: PackratParser[UclExpr] = E3 ~ OpAnd ~ E2 ^^ ast_binary | E3 ~ OpOr ~ E2 ^^ ast_binary | E3
  /** E3 := E4 OpRel E3 | E4  **/
  lazy val E3: PackratParser[UclExpr] = E4 ~ RelOp ~ E4 ^^ ast_binary | E4
  /** E4 := E5 OpConcat E4 | E5 **/
  lazy val E4: PackratParser[UclExpr] = E5 ~ OpConcat ~ E4 ^^ ast_binary | E5
  /** E5 := E6 OpAdd E5 | E6 **/
  lazy val E5: PackratParser[UclExpr] = E6 ~ OpAdd ~ E5 ^^ ast_binary | E6
  /** E6 := E7 OpMul E6 | E7 **/
  lazy val E6: PackratParser[UclExpr] = E7 ~ OpMul ~ E6 ^^ ast_binary | E7
  /** E7 := UnOp E8 | E8 **/
  lazy val E7: PackratParser[UclExpr] = OpNeg ~> E8 ^^ { case e => UclNegation(e) } | E8
  /** E8 := E9 MapOp | E9 **/
  lazy val E8: PackratParser[UclExpr] =
      E9 ~ ExprList ^^ { case e ~ f => UclFuncApplication(e, f) } |
      E9 ~ ArraySelectOp ^^ { case e ~ m => UclArraySelectOperation(e, m) } |
      E9 ~ ArrayStoreOp ^^ { case e ~ m => UclArrayStoreOperation(e, m._1, m._2) } |
      E9 ~ ExtractOp ^^ { case e ~ m => UclIFuncApplication(m, List(e)) } |
      E9
  /** E9 := false | true | Number | Bitvector | Id FuncApplication | (Expr) **/
  lazy val E9: PackratParser[UclExpr] =
      Bool |
      Number |
      KwITE ~> ("(" ~> Expr ~ ("," ~> Expr) ~ ("," ~> Expr) <~ ")") ^^ { case e ~ t ~ f => UclITE(e,t,f) } |
      KwLambda ~> (IdTypeList) ~ ("." ~> Expr) ^^ { case idtyps ~ expr => UclLambda(idtyps, expr) } |
      "(" ~> Expr <~ ")" |
      Id
  /** Expr := E0 **/
  lazy val Expr: PackratParser[UclExpr] = TemporalExpr0
  lazy val ExprList: Parser[List[UclExpr]] =
    ("(" ~> Expr ~ rep("," ~> Expr) <~ ")") ^^ { case e ~ es => e::es } |
    "(" ~> ")" ^^ { case _ => List.empty[UclExpr] }

  /** Examples of allowed types are bool | int | [int,int,bool] int **/
  lazy val PrimitiveType : PackratParser[UclType] =
    KwBool ^^ {case _ => UclBoolType()} | KwInt ^^ {case _ => UclIntType()}
  lazy val EnumType : PackratParser[UclEnumType] =
    KwEnum ~> ("{" ~> Id) ~ rep("," ~> Id) <~ "}" ^^ { case id ~ ids => UclEnumType(id::ids) }
  lazy val RecordType : PackratParser[UclRecordType] =
    KwRecord ~> ("{" ~> IdType) ~ rep("," ~> IdType) <~ "}" ^^ 
    { case id ~ ids => UclRecordType(id::ids) }
  lazy val MapType : PackratParser[UclMapType] =
    PrimitiveType ~ rep ("*" ~> PrimitiveType) ~ ("->" ~> Type) ^^
      { case t ~ ts ~ rt => UclMapType(t :: ts, rt)}
  lazy val ArrayType : PackratParser[UclArrayType] =
    ("[") ~> PrimitiveType ~ (rep ("," ~> PrimitiveType) <~ "]") ~ Type ^^
      { case t ~ ts ~ rt => UclArrayType(t :: ts, rt)}
  lazy val SynonymType : PackratParser[UclSynonymType] = Id ^^ { case id => UclSynonymType(id) }
  lazy val Type : PackratParser[UclType] = 
    MapType | ArrayType | EnumType | RecordType | PrimitiveType | SynonymType

  lazy val IdType : PackratParser[(UclIdentifier,UclType)] =
    Id ~ (":" ~> Type) ^^ { case id ~ typ => (id,typ)}

  lazy val IdTypeList : PackratParser[List[(UclIdentifier,UclType)]] =
    "(" ~> IdType ~ (rep ("," ~> IdType) <~ ")") ^^ { case t ~ ts =>  t :: ts} |
    "(" ~ ")" ^^ { case _~_ => List.empty[(UclIdentifier,UclType)] }

  lazy val Lhs : PackratParser[UclLhs] =
    Id ~ ArraySelectOp ~ RecordSelectOp ~ rep(RecordSelectOp) ^^ 
      { case id ~ mapOp ~ rOp ~ rOps => UclLhs(id, Some(mapOp), Some(rOp::rOps))} |
    Id ~ ArraySelectOp ^^ { case id ~ op => UclLhs(id, Some(op), None) } |
    Id ~ RecordSelectOp ~ rep(RecordSelectOp) ^^ { case id ~ rOp ~ rOps => UclLhs(id, None, Some(rOp::rOps)) } |
    Id ^^ { case id => UclLhs(id, None, None) }

  lazy val LhsList: PackratParser[List[UclLhs]] =
    ("(" ~> Lhs ~ rep("," ~> Lhs) <~ ")") ^^ { case l ~ ls => l::ls } |
    "(" ~> ")" ^^ { case _ => List.empty[UclLhs] }

  lazy val RangeExpr: PackratParser[(UclNumber,UclNumber)] =
    KwRange ~> ("(" ~> Number ~ ("," ~> Number) <~ ")") ^^ { case x ~ y => (x,y) }

  lazy val LocalVarDecl : PackratParser[UclLocalVarDecl] =
    KwLocalVar ~> IdType <~ ";" ^^ { case (id,typ) => UclLocalVarDecl(id,typ)}
    
  lazy val Statement: PackratParser[UclStatement] =
    KwSkip <~ ";" ^^ { case _ => UclSkipStmt() } |
    KwAssert ~> Expr <~ ";" ^^ { case e => UclAssertStmt(e) } |
    KwAssume ~> Expr <~ ";" ^^ { case e => UclAssumeStmt(e) } |
    KwHavoc ~> Id <~ ";" ^^ { case id => UclHavocStmt(id) } |
    Lhs ~ rep("," ~> Lhs) ~ ":=" ~ Expr ~ rep("," ~> Expr) <~ ";" ^^
      { case l ~ ls ~ ":=" ~ r ~ rs => UclAssignStmt(l::ls, r::rs) } |
    KwCall ~> LhsList ~ (":=" ~> Id) ~ ExprList <~ ";" ^^
      { case lhss ~ id ~ args => UclProcedureCallStmt(id, lhss, args) } |
    KwIf ~> Expr ~ BlockStatement ~ (KwElse ~> BlockStatement) ^^
      { case e ~ f ~ g => UclIfElseStmt(e,f,g)} |
    KwCase ~> rep(CaseBlockStmt) <~ KwEsac ^^ 
      { case i => UclCaseStmt(i) } |
    KwFor ~> (Id ~ (KwIn ~> RangeExpr) ~ BlockStatement) ^^
      { case id ~ r ~ body => UclForStmt(id, r, body) }
    
  lazy val CaseBlockStmt: PackratParser[(UclExpr, List[UclStatement])] = 
    Expr ~ (":" ~> BlockStatement) ^^ { case e ~ ss => (e,ss) }
  lazy val BlockStatement: PackratParser[List[UclStatement]] = "{" ~> rep (Statement) <~ "}"

  lazy val ProcedureDecl : PackratParser[UclProcedureDecl] =
    KwProcedure ~> Id ~ IdTypeList ~ (KwReturns ~> IdTypeList) ~ 
      ("{" ~> rep(LocalVarDecl)) ~ (rep(Statement) <~ "}") ^^ 
      { case id ~ args ~ outs ~ decls ~ body =>  
        UclProcedureDecl(id, UclProcedureSig(args,outs), decls, body) } |
    KwProcedure ~> Id ~ IdTypeList ~ ("{" ~> rep(LocalVarDecl)) ~ (rep(Statement) <~ "}") ^^
      { case id ~ args ~ decls ~ body => 
        UclProcedureDecl(id, UclProcedureSig(args, List.empty[(UclIdentifier,UclType)]), decls, body) }

  lazy val TypeDecl : PackratParser[UclTypeDecl] =
    KwType ~> Id ~ ("=" ~> Type) <~ ";" ^^ { case id ~ t => UclTypeDecl(id,t) }
    
  lazy val VarDecl : PackratParser[UclStateVarDecl] =
    KwVar ~> IdType <~ ";" ^^ { case (id,typ) => UclStateVarDecl(id,typ)}
    
  lazy val InputDecl : PackratParser[UclInputVarDecl] =
    KwInput ~> IdType <~ ";" ^^ { case (id,typ) => UclInputVarDecl(id,typ)}
    
  lazy val OutputDecl : PackratParser[UclOutputVarDecl] =
    KwOutput ~> IdType <~ ";" ^^ { case (id,typ) => UclOutputVarDecl(id,typ)}
    
  lazy val ConstDecl : PackratParser[UclConstantDecl] =
    KwConst ~> IdType <~ ";" ^^ { case (id,typ) => UclConstantDecl(id,typ)}
    
  lazy val FuncDecl : PackratParser[UclFunctionDecl] =
    KwFunction ~> Id ~ IdTypeList ~ (":" ~> Type) <~ ";" ^^ 
    { case id ~ idtyps ~ rt => UclFunctionDecl(id, UclFunctionSig(idtyps, rt)) }
    
  lazy val InitDecl : PackratParser[UclInitDecl] = KwInit ~> BlockStatement ^^ 
    { case b => UclInitDecl(b) }
  
  lazy val NextDecl : PackratParser[UclNextDecl] = KwNext ~> BlockStatement ^^ 
    { case b => UclNextDecl(b) }
    
  lazy val Decl: PackratParser[UclDecl] = 
    (TypeDecl | ConstDecl | FuncDecl | VarDecl | InputDecl | OutputDecl | ProcedureDecl | InitDecl | NextDecl | SpecDecl)
  
  lazy val Module: PackratParser[UclModule] =
    KwModule ~> Id ~ ("{" ~> rep(Decl) <~ "}") ^^ { case id ~ decls => UclModule(id, decls) }

  lazy val SpecDecl: PackratParser[UclSpecDecl] =
    KwDefineProp ~> Id ~ ("=" ~> Expr) <~ ";" ^^ { case id ~ expr => UclSpecDecl(id,expr) }
    
//  lazy val Spec: PackratParser[UclSpec] =
//    KwSpec ~> "{" ~> rep(SpecDecl) <~ "}" ^^ { case specDecls => UclSpec(specDecls) }
    
  
  def parseExpr(input: String): UclExpr = {
    val tokens = new PackratReader(new lexical.Scanner(input))
    phrase(Expr)(tokens) match {
      case Success(ast, _) => ast
      case e: NoSuccess => throw new IllegalArgumentException(e.toString)
    }
  }

  def parseModule(input: String): UclModule = {
    val tokens = new PackratReader(new lexical.Scanner(input))
    phrase(Module)(tokens) match {
      case Success(ast, _) => ast
      case e: NoSuccess => throw new IllegalArgumentException(e.toString)
    }
  }
}