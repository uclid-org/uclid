
/**
 * @author rohitsinha
 */

abstract class UclOperator
case class UclLTOperator() extends UclOperator { override def toString = "<" }
case class UclLEOperator() extends UclOperator { override def toString = "<=" }
case class UclGTOperator() extends UclOperator { override def toString = ">" }
case class UclGEOperator() extends UclOperator { override def toString = ">=" }
case class UclAddOperator() extends UclOperator { override def toString = "+" }
case class UclMulOperator() extends UclOperator { override def toString = "*" }
case class UclExtractOperator(high: UclNumber, low: UclNumber) extends UclOperator {
  override def toString = "[" + high + ":" + low + "]"
}
case class UclConcatOperator() extends UclOperator { override def toString = "++" }
case class UclRecordSelectOperator(id: UclIdentifier) extends UclOperator {
  override def toString = "." + id
}

abstract class UclExpr
case class UclIdentifier(value: String) extends UclExpr {
  override def toString = value.toString
}
case class UclNumber(value: BigInt) extends UclExpr {
  override def toString = value.toString
}
//TODO: check that value can be expressed using "width" bits
case class UclBitVector(value: BigInt, width: BigInt) extends UclExpr {
  override def toString = value + "bv" + width //TODO: print in hex
}
case class UclBoolean(value: Boolean) extends UclExpr {
  override def toString = value.toString
}
case class UclBiImplication(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " <==> " + right + ")"
}
case class UclImplication(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " ==> " + right + ")"
}
case class UclConjunction(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " /\\ " + right + ")"
}
case class UclDisjunction(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " \\/ " + right + ")"
}
case class UclNegation(expr: UclExpr) extends UclExpr {
  override def toString = "! " + expr
}
case class UclEquality(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " = " + right + ")"
}
//for symbols interpreted by underlying Theory solvers
case class UclIFuncApplication(op: UclOperator, operands: List[UclExpr]) extends UclExpr {
  override def toString = op + "(" + operands.foldLeft(""){(acc,i) => acc + "," + i} + ")"
}
case class UclArraySelectOperation(e: UclExpr, index: List[UclExpr]) extends UclExpr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]"
}
case class UclArrayStoreOperation(e: UclExpr, index: List[UclExpr], value: UclExpr) extends UclExpr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]" + " := " + value
}
//for uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class UclFuncApplication(e: UclExpr, args: List[UclExpr]) extends UclExpr {
  override def toString = e + "(" + args.tail.fold(args.head.toString)
    { (acc,i) => acc + "," + i } + ")"
}
case class UclITE(e: UclExpr, t: UclExpr, f: UclExpr) extends UclExpr {
  override def toString = "ITE(" + e + "," + t + "," + f + ")"
}
case class UclLambda(ids: List[(UclIdentifier,UclType)], e: UclExpr) extends UclExpr {
  override def toString = "Lambda(" + ids + "). " + e
}
case class UclTemporalOpUntil(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " U " + right + ")"
}
case class UclTemporalOpWUntil(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " W " + right + ")"
}
case class UclTemporalOpRelease(left: UclExpr, right: UclExpr) extends UclExpr {
  override def toString = "(" + left + " R " + right + ")"
}
case class UclTemporalOpFinally(expr: UclExpr) extends UclExpr {
  override def toString = "(F " + expr + ")"
}
case class UclTemporalOpGlobally(expr: UclExpr) extends UclExpr {
  override def toString = "(G " + expr + ")"
}
case class UclTemporalOpNext(expr: UclExpr) extends UclExpr {
  override def toString = "(Next " + expr + ")"
}

case class UclLhs(id: UclIdentifier, 
                  arraySelect: Option[List[UclExpr]], 
                  recordSelect: Option[List[UclIdentifier]]) {
  val t1 = arraySelect match 
    { case Some(as) => as.toString; case None => "" }
  val t2 = recordSelect match 
    { case Some(rs) => rs.fold(""){(acc,i) => acc + "." + i}; case None => ""}
  override def toString = id.toString + t1 + t2
}

abstract class UclType
case class UclBoolType() extends UclType { 
  override def toString = "bool" 
  override def equals(other: Any) = other.isInstanceOf[UclBoolType]
}
case class UclIntType() extends UclType { 
  override def toString = "int" 
  override def equals(other: Any) = other.isInstanceOf[UclIntType]  
}
case class UclEnumType(ids: List[UclIdentifier]) extends UclType {
  override def toString = "enum {" + 
    ids.tail.foldLeft(ids.head.toString) {(acc,i) => acc + "," + i} + "}"
  override def equals(other: Any) = other match {
      case that: UclEnumType =>
        if (that.ids.size == this.ids.size) {
          (that.ids zip this.ids).forall(i => i._1.value == i._2.value)
        } else { false }
      case _ => false
    }
}
case class UclRecordType(fields: List[(UclIdentifier,UclType)]) extends UclType {
  override def toString = "record {" + 
    fields.tail.foldLeft(fields.head.toString) {(acc,i) => acc + "," + i} + "}"
  override def equals(other: Any) = other match {
      case that: UclRecordType =>
        if (that.fields.size == this.fields.size) {
          (that.fields zip this.fields).forall(i => i._1._1.value == i._2._1.value && i._1._2 == i._2._2)
        } else { false }
      case _ => false
    }
}
//class UclBitvectorType extends UclType
case class UclMapType(inTypes: List[UclType], outType: UclType) extends UclType {
  override def toString = "map [" + inTypes.tail.fold(inTypes.head.toString)
  { (acc,i) => acc + "," + i } + "] " + outType
  override def equals(other: Any) = other match {
      case that: UclMapType =>
        if (that.inTypes.size == this.inTypes.size) {
          (that.outType == this.outType) && (that.inTypes zip this.inTypes).forall(i => i._1 == i._2)
        } else { false }
      case _ => false
    }
}
case class UclArrayType(inTypes: List[UclType], outType: UclType) extends UclType {
  override def toString = "array [" + inTypes.tail.fold(inTypes.head.toString)
  { (acc,i) => acc + "," + i } + "] " + outType
  override def equals(other: Any) = other match {
      case that: UclArrayType =>
        if (that.inTypes.size == this.inTypes.size) {
          (that.outType == this.outType) && (that.inTypes zip this.inTypes).forall(i => i._1 == i._2)
        } else { false }
      case _ => false
    }
}
case class UclSynonymType(id: UclIdentifier) extends UclType {
  override def toString = id.toString
  override def equals(other: Any) = other match {
    case that: UclSynonymType => that.id.value == this.id.value
    case _ => false
  }
}

/** Statements **/
abstract class UclStatement
case class UclSkipStmt() extends UclStatement {
  override def toString = "skip;"
}
case class UclAssertStmt(e: UclExpr) extends UclStatement {
  override def toString = "assert " + e + ";"
}
case class UclAssumeStmt(e: UclExpr) extends UclStatement {
  override def toString = "assume " + e + ";"
}
case class UclHavocStmt(id: UclIdentifier) extends UclStatement {
  override def toString = "havoc " + id + ";"
}
case class UclAssignStmt(lhss: List[UclLhs], rhss: List[UclExpr]) extends UclStatement {
  override def toString = lhss.tail.foldLeft(lhss.head.toString) { (acc,i) => acc + "," + i } +
    " := " +rhss.tail.foldLeft(rhss.head.toString) { (acc,i) => acc + "," + i } + ";"
}
case class UclIfElseStmt(cond: UclExpr, ifblock: List[UclStatement], elseblock: List[UclStatement])
  extends UclStatement {
  override def toString = "if " + cond + " {\n" + ifblock + "\n} else {\n" + elseblock + "\n}"
}
case class UclForStmt(id: UclIdentifier, range: (UclNumber,UclNumber), body: List[UclStatement])
  extends UclStatement
{
  override def toString = "for " + id + " in range(" + range._1 +"," + range._2 + ") {\n" + 
    body.fold(""){(acc,i) => acc + i.toString} + "}"
}
case class UclCaseStmt(body: List[(UclExpr,List[UclStatement])]) extends UclStatement {
  override def toString = "case" +
    body.foldLeft("") { (acc,i) => acc + "\n" + i._1 + " : " + i._2 + "\n"} + "esac"
}
case class UclProcedureCallStmt(id: UclIdentifier, callLhss: List[UclLhs], args: List[UclExpr])
  extends UclStatement {
  override def toString = "call (" +
    callLhss.foldLeft("") { (acc,i) => acc + "," + i } + ") := " + id + "(" +
    args.foldLeft("") { (acc,i) => acc + "," + i } + ")"
}

case class UclLocalVarDecl(id: UclIdentifier, typ: UclType) {
  override def toString = "localvar " + id + ": " + typ + ";"
}

case class UclProcedureSig(inParams: List[(UclIdentifier,UclType)], outParams: List[(UclIdentifier,UclType)]) {
  type T = (UclIdentifier,UclType)
  val printfn = {(a: T) => a._1.toString + ":" + a._2}
  override def toString =
    "(" + inParams.foldLeft("") { (acc, i) => acc + "," + printfn(i) } + ")" +
    " returns " + "(" + outParams.foldLeft("") { (acc,i) => acc + "," + printfn(i) } + ")"
}
case class UclFunctionSig(args: List[(UclIdentifier,UclType)], retType: UclType) {
  type T = (UclIdentifier,UclType)
  val printfn = {(a: T) => a._1.toString + ":" + a._2}
  override def toString = "(" + args.tail.foldLeft(printfn(args.head)) { (acc, i) => acc + "," + printfn(i) } + ")" +
    ": " + retType
}

abstract class UclDecl
case class UclProcedureDecl(id: UclIdentifier, sig: UclProcedureSig, 
    decls: List[UclLocalVarDecl], body: List[UclStatement]) extends UclDecl {
  override def toString = "procedure " + id + sig +
    " {\n" + body.foldLeft("") { case (acc,i) => acc + "\t" + i + "\n" } + "}"
}
case class UclTypeDecl(id: UclIdentifier, typ: UclType) extends UclDecl {
  override def toString = "type " + id + " = " + typ 
}
case class UclStateVarDecl(id: UclIdentifier, typ: UclType) extends UclDecl {
  override def toString = "var " + id + ": " + typ + ";"
}
case class UclInputVarDecl(id: UclIdentifier, typ: UclType) extends UclDecl {
  override def toString = "input " + id + ": " + typ + ";"
}
case class UclOutputVarDecl(id: UclIdentifier, typ: UclType) extends UclDecl {
  override def toString = "output " + id + ": " + typ + ";"
}
case class UclConstantDecl(id: UclIdentifier, typ: UclType) extends UclDecl {
  override def toString = "constant " + id + ": " + typ + ";"
}
case class UclFunctionDecl(id: UclIdentifier, sig: UclFunctionSig)
extends UclDecl {
  override def toString = "function " + id + sig + ";"
}
case class UclInitDecl(body: List[UclStatement]) extends UclDecl {
  override def toString = 
    "init {\n" + body.foldLeft("") { case (acc,i) => acc + "\t" + i + "\n" } + "}"
}
case class UclNextDecl(body: List[UclStatement]) extends UclDecl {
  override def toString = 
    "next {\n" + body.foldLeft("") { case (acc,i) => acc + "\t" + i + "\n" } + "}"
}
case class UclSpecDecl(id: UclIdentifier, expr: UclExpr) extends UclDecl {
  override def toString = "property " + id + ":" + expr + ";"
}

case class UclModule(id: UclIdentifier, decls: List[UclDecl]) {
  override def toString = "\nmodule " + id + "{\n" + 
  decls.foldLeft("") { case (acc,i) => acc + i + "\n" } + "}\n"
}
