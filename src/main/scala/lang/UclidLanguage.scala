
/**
 * @author rohitsinha
 * With modifications by pramod.
 */
package uclid
package lang

import scala.collection.immutable.Map


object PrettyPrinter
{
  val indentSeq = "  "
  def indent(n : Int) = indentSeq * n
}

sealed abstract class Operator {
  def isInfix = false
  def isPolymorphic = false
}
sealed abstract class InfixOperator extends Operator {
  override def isInfix = true
}
// This is the polymorphic operator type. Typerchecker.rewrite converts these operators
// to either the integer or bitvector versions.
sealed abstract class PolymorphicOperator extends InfixOperator {
  var reifiedOp : Option[Operator] = None
  override def isPolymorphic = true
}
case class LTOp() extends PolymorphicOperator { override def toString = "<" }
case class LEOp() extends PolymorphicOperator { override def toString = "<=" }
case class GTOp() extends PolymorphicOperator { override def toString = ">" }
case class GEOp() extends PolymorphicOperator { override def toString = ">=" }
case class AddOp() extends PolymorphicOperator { override def toString = "+" }
case class SubOp() extends PolymorphicOperator { override def toString = "-" }
case class MulOp() extends PolymorphicOperator { override def toString = "*" }
// These are operators with integer operators.
sealed abstract class IntArgOperator extends InfixOperator
case class IntLTOp() extends IntArgOperator { override def toString = "<" }
case class IntLEOp() extends IntArgOperator { override def toString = "<=" }
case class IntGTOp() extends IntArgOperator { override def toString = ">" }
case class IntGEOp() extends IntArgOperator { override def toString = ">=" }
case class IntAddOp() extends IntArgOperator { override def toString ="+" }
case class IntSubOp() extends IntArgOperator { override def toString = "-" }
case class IntMulOp() extends IntArgOperator { override def toString = "*" }
// These operators take bitvector operands.
sealed abstract class BVArgOperator extends InfixOperator
case class BVLTOp(w : Int) extends BVArgOperator { override def toString = "<_" + w.toString }
case class BVLEOp(w : Int) extends BVArgOperator { override def toString = "<=_" + w.toString }
case class BVGTOp(w : Int) extends BVArgOperator { override def toString = ">_" + w.toString }
case class BVGEOp(w : Int) extends BVArgOperator { override def toString = ">=_" + w.toString }
case class BVAddOp(w : Int) extends BVArgOperator { override def toString ="+_" + w.toString }
case class BVSubOp(w : Int) extends BVArgOperator { override def toString = "-_" + w.toString }
case class BVMulOp(w : Int) extends BVArgOperator { override def toString = "*_" + w.toString }
// Boolean operators.
sealed abstract class BooleanOperator() extends Operator { override def isInfix = true }
case class ConjunctionOp() extends BooleanOperator { override def toString = "&&" }
case class DisjunctionOp() extends BooleanOperator { override def toString = "||" }
case class IffOp() extends BooleanOperator { override def toString = "<==>" }
case class ImplicationOp() extends BooleanOperator { override def toString = "==>" }
case class NegationOp() extends BooleanOperator { 
  override def toString = "!"
  override def isInfix = false
}
// (In-)equality operators.
sealed abstract class ComparisonOperator() extends InfixOperator
case class EqualityOp() extends ComparisonOperator { override def toString = "==" }
case class InequalityOp() extends ComparisonOperator { override def toString = "!=" } 

sealed abstract class TemporalOperator() extends Operator
sealed abstract class TemporalInfixOperator() extends TemporalOperator { override def isInfix = true }
sealed abstract class TemporalPrefixOperator() extends TemporalOperator { override def isInfix = false }
case class UntilTemporalOp() extends TemporalInfixOperator { override def toString = "U" }
case class WUntilTemporalOp() extends TemporalInfixOperator { override def toString = "W" }
case class ReleaseTemporalOp() extends TemporalInfixOperator { override def toString = "R" }
case class FinallyTemporalOp() extends TemporalPrefixOperator { override def toString = "F" }
case class GloballyTemporalOp() extends TemporalPrefixOperator { override def toString = "G" }
case class NextTemporalOp() extends TemporalPrefixOperator { override def toString = "X" }

case class ExtractOp(high: IntLit, low: IntLit) extends Operator {
  override def toString = "[" + high + ":" + low + "]"
}
case class ConcatOp() extends Operator { override def toString = "++" }
case class RecordSelect(id: Identifier) extends Operator {
  override def toString = "." + id
}

sealed abstract class Expr
case class Identifier(value: String) extends Expr {
  override def toString = value.toString
}

sealed abstract class Literal extends Expr
case class BoolLit(value: Boolean) extends Literal {
  override def toString = value.toString
}
case class IntLit(value: BigInt) extends Literal {
  override def toString = value.toString
}
//TODO: check that value can be expressed using "width" bits
case class BitVectorLit(value: BigInt, width: Int) extends Literal {
  override def toString = value.toString + "bv" + width.toString
}
case class Record(value: List[Expr]) extends Expr {
  override def toString = "{" + value.foldLeft(""){(acc,i) => acc + i} + "}"
}
//for symbols interpreted by underlying Theory solvers
case class UclOperatorApplication(op: Operator, operands: List[Expr]) extends Expr {
  override def toString = {
    if (op.isInfix) {
      "(" + Utils.join(operands.map(_.toString), " " + op + " ") + ")"
    } else {
      op + "(" + Utils.join(operands.map(_.toString), ", ") + ")"
    }
  }
}
case class UclArraySelectOperation(e: Expr, index: List[Expr]) extends Expr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]"
}
case class UclArrayStoreOperation(e: Expr, index: List[Expr], value: Expr) extends Expr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]" + " := " + value
}
//for uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class UclFuncApplication(e: Expr, args: List[Expr]) extends Expr {
  override def toString = e + "(" + args.tail.fold(args.head.toString)
    { (acc,i) => acc + "," + i } + ")"
}
case class UclITE(e: Expr, t: Expr, f: Expr) extends Expr {
  override def toString = "ITE(" + e + "," + t + "," + f + ")"
}
case class UclLambda(ids: List[(Identifier,Type)], e: Expr) extends Expr {
  override def toString = "Lambda(" + ids + "). " + e
}

case class UclLhs(id: Identifier, 
                  arraySelect: Option[List[Expr]], 
                  recordSelect: Option[List[Identifier]]) {
  val t1 = arraySelect match 
    { case Some(as) => as.toString; case None => "" }
  val t2 = recordSelect match 
    { case Some(rs) => rs.fold(""){(acc,i) => acc + "." + i}; case None => ""}
  override def toString = id.toString + t1 + t2
}

sealed abstract class Type {
  def isBool = false
  def isNumeric = false
  def isTemporal = false
}

/** 
 *  Numeric types base class. 
 */
sealed abstract class NumericType extends Type {
  override def isNumeric = true
}

/**
 * Temporal types.
 */
case class TemporalType() extends Type {
  override def toString = "temporal"
  override def isTemporal = true
}

/**
 * Regular types.
 */
case class BoolType() extends Type {
  override def toString = "bool"
  override def isBool = true
}
case class IntType() extends NumericType { 
  override def toString = "int"
}
case class BitVectorType(width: Int) extends NumericType {
  override def toString = "bv" + width.toString
}
case class EnumType(ids: List[Identifier]) extends Type {
  override def toString = "enum {" + 
    ids.tail.foldLeft(ids.head.toString) {(acc,i) => acc + "," + i} + "}"
}
case class TupleType(fieldTypes: List[Type]) extends Type {
  override def toString = "tuple {" + Utils.join(fieldTypes.map(_.toString), ", ") + "}" 
}
case class RecordType(fields: List[(Identifier,Type)]) extends Type {
  Utils.assert(Utils.allUnique(fields.map(_._1)), "Record field names must be unique.")
  def fieldType(fieldName: Identifier) : Option[Type] = {
    fields.find((f) => f._1 == fieldName).flatMap((fp) => Some(fp._2))
  }
  override def toString = "record {" + Utils.join(fields.map((f) => f._1.toString + " : " + f._2.toString), ", ")  + "}"
}
case class MapType(inTypes: List[Type], outType: Type) extends Type {
  override def toString = "map [" + inTypes.tail.fold(inTypes.head.toString)
  { (acc,i) => acc + "," + i } + "] " + outType
  override def equals(other: Any) = other match {
      case that: MapType =>
        if (that.inTypes.size == this.inTypes.size) {
          (that.outType == this.outType) && (that.inTypes zip this.inTypes).forall(i => i._1 == i._2)
        } else { false }
      case _ => false
    }
}
case class ArrayType(inTypes: List[Type], outType: Type) extends Type {
  override def toString = "array [" + Utils.join(inTypes.map(_.toString), ", ") + "]" + outType.toString
}
case class SynonymType(id: Identifier /* FIXME: needs another argument? */) extends Type {
  override def toString = id.toString
  override def equals(other: Any) = other match {
    case that: SynonymType => that.id.value == this.id.value
    case _ => false
  }
}

/** Statements **/
sealed abstract class UclStatement
case class UclSkipStmt() extends UclStatement {
  override def toString = "skip;"
}
case class UclAssertStmt(e: Expr) extends UclStatement {
  override def toString = "assert " + e + ";"
}
case class UclAssumeStmt(e: Expr) extends UclStatement {
  override def toString = "assume " + e + ";"
}
case class UclHavocStmt(id: Identifier) extends UclStatement {
  override def toString = "havoc " + id + ";"
}
case class UclAssignStmt(lhss: List[UclLhs], rhss: List[Expr]) extends UclStatement {
  override def toString = 
    Utils.join(lhss.map (_.toString), ", ") + " := " + Utils.join(rhss.map(_.toString), ", ") + ";"
}
case class UclIfElseStmt(cond: Expr, ifblock: List[UclStatement], elseblock: List[UclStatement]) extends UclStatement {
  override def toString = "if " + cond + " {\n" + ifblock + "\n} else {\n" + elseblock + "\n}"
}
case class UclForStmt(id: Identifier, range: (IntLit,IntLit), body: List[UclStatement])
  extends UclStatement
{
  override def toString = "for " + id + " in range(" + range._1 +"," + range._2 + ") {\n" + 
    body.fold(""){(acc,i) => acc + i.toString} + "}"
}
case class UclCaseStmt(body: List[(Expr,List[UclStatement])]) extends UclStatement {
  override def toString = "case" +
    body.foldLeft("") { (acc,i) => acc + "\n" + i._1 + " : " + i._2 + "\n"} + "esac"
}
case class UclProcedureCallStmt(id: Identifier, callLhss: List[UclLhs], args: List[Expr])
  extends UclStatement {
  override def toString = "call (" +
    Utils.join(callLhss.map(_.toString), ", ") + ") := " + id + "(" +
    Utils.join(args.map(_.toString), ", ") + ")"
}

case class UclLocalVarDecl(id: Identifier, typ: Type) {
  override def toString = "localvar " + id + ": " + typ + ";"
}

case class UclProcedureSig(inParams: List[(Identifier,Type)], outParams: List[(Identifier,Type)]) {
  type T = (Identifier,Type)
  val printfn = {(a: T) => a._1.toString + ": " + a._2}
  val typ = MapType(inParams.map(_._2), TupleType(outParams.map(_._2)))
  override def toString =
    "(" + Utils.join(inParams.map(printfn(_)), ", ") + ")" +
    " returns " + "(" + Utils.join(outParams.map(printfn(_)), ", ") + ")"
}
case class UclFunctionSig(args: List[(Identifier,Type)], retType: Type) {
  type T = (Identifier,Type)
  val typ = MapType(args.map(_._2), retType)
  val printfn = {(a: T) => a._1.toString + ": " + a._2}
  override def toString = "(" + Utils.join(args.map(printfn(_)), ", ") + ")" +
    ": " + retType
}

sealed abstract class UclDecl
case class UclProcedureDecl(id: Identifier, sig: UclProcedureSig, 
    decls: List[UclLocalVarDecl], body: List[UclStatement]) extends UclDecl {
  override def toString = "procedure " + id + sig +
    PrettyPrinter.indent(1) + "{\n" + body.foldLeft("") { 
      case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" 
    } + 
    PrettyPrinter.indent(1) + "}"
}
case class UclTypeDecl(id: Identifier, typ: Type) extends UclDecl {
  override def toString = "type " + id + " = " + typ 
}
case class UclStateVarDecl(id: Identifier, typ: Type) extends UclDecl {
  override def toString = "var " + id + ": " + typ + ";"
}
case class UclInputVarDecl(id: Identifier, typ: Type) extends UclDecl {
  override def toString = "input " + id + ": " + typ + ";"
}
case class UclOutputVarDecl(id: Identifier, typ: Type) extends UclDecl {
  override def toString = "output " + id + ": " + typ + ";"
}
case class UclConstantDecl(id: Identifier, typ: Type) extends UclDecl {
  override def toString = "constant " + id + ": " + typ + ";"
}
case class UclFunctionDecl(id: Identifier, sig: UclFunctionSig)
extends UclDecl {
  override def toString = "function " + id + sig + ";"
}
case class UclInitDecl(body: List[UclStatement]) extends UclDecl {
  override def toString = 
    "init {\n" + 
    body.foldLeft("") { 
      case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" 
    } + 
    PrettyPrinter.indent(1) + "}"
}
case class UclNextDecl(body: List[UclStatement]) extends UclDecl {
  override def toString = 
    "next {\n" + 
    body.foldLeft("") { 
      case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" 
    } + 
    PrettyPrinter.indent(1) + "}"
}
case class UclSpecDecl(id: Identifier, expr: Expr) extends UclDecl {
  override def toString = "property " + id + ":" + expr + ";"
}

sealed abstract class UclCmd
case class UclInitializeCmd() extends UclCmd {
  override def toString = "initialize;"
}
case class UclUnrollCmd(steps : IntLit) extends UclCmd {
  override def toString = "unroll (" + steps.toString + ");"
}
case class UclSimulateCmd(steps : IntLit) extends UclCmd {
  override def toString = "simulate (" + steps.toString + ");"
}
case class UclDecideCmd() extends UclCmd {
  override def toString = "decide; "
}

case class Module(id: Identifier, decls: List[UclDecl], cmds : List[UclCmd]) {
  override def toString = 
    "\nmodule " + id + " {\n" + 
      decls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i + "\n" } +
      PrettyPrinter.indent(1) + "control {" + "\n" + 
        cmds.foldLeft("")  { case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" } +
      PrettyPrinter.indent(1) + "}\n" + 
    "}\n"
}

object Scope {
  sealed abstract class NamedExpression(val id : Identifier, val typ: Type) {
    val isReadOnly = false
  }
  sealed abstract class ReadOnlyNamedExpression(id : Identifier, typ: Type) extends NamedExpression(id, typ) {
    override val isReadOnly = true
  }
  case class TypeSynonym(typId : Identifier, sTyp: Type) extends ReadOnlyNamedExpression(typId, sTyp)
  case class StateVar(varId : Identifier, varTyp: Type) extends NamedExpression(varId, varTyp)
  case class InputVar(inpId : Identifier, inpTyp: Type) extends ReadOnlyNamedExpression(inpId, inpTyp)
  case class OutputVar(outId : Identifier, outTyp: Type) extends NamedExpression(outId, outTyp)
  case class ConstantVar(cId : Identifier, cTyp : Type) extends ReadOnlyNamedExpression(cId, cTyp)
  case class Function(fId : Identifier, fTyp: Type) extends ReadOnlyNamedExpression(fId, fTyp)
  case class Procedure(pId : Identifier, pTyp: Type) extends ReadOnlyNamedExpression(pId, pTyp)
  case class ProcedureInputArg(argId : Identifier, argTyp: Type) extends ReadOnlyNamedExpression(argId, argTyp)
  case class ProcedureOutputArg(argId : Identifier, argTyp: Type) extends NamedExpression(argId, argTyp)
  case class ProcedureLocalVar(vId : Identifier, vTyp : Type) extends NamedExpression(vId, vTyp)
  case class LambdaVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)
  case class SpecVar(varId : Identifier, expr: Expr) extends NamedExpression(varId, BoolType())

  type IdentifierMap = Map[Identifier, NamedExpression]
  def addToMap(map : Scope.IdentifierMap, expr: Scope.NamedExpression) : Scope.IdentifierMap = {
    Utils.assert(!map.contains(expr.id), "Error: identifier '" + expr.id.toString + "' hides previous declaration with the same name.")
    map + (expr.id -> expr)
  }
}

case class ScopeMap (map: Scope.IdentifierMap) {
  /** Create an empty context. */
  def this() {
    this(Map.empty[Identifier, Scope.NamedExpression])
  }
  /** Return a new context with this identifier added to the current context. */
  def +(expr: Scope.NamedExpression) : ScopeMap = {
    new ScopeMap(map + (expr.id -> expr))
  }
  /** Return a new context with the declarations in this module added to it. */
  def +(module: Module) : ScopeMap = { 
    val newMap = module.decls.foldLeft(map){ (mapAcc, decl) =>
      decl match {
        case UclProcedureDecl(id, sig, _, _) => Scope.addToMap(mapAcc, Scope.Procedure(id, sig.typ))
        case UclTypeDecl(id, typ) => Scope.addToMap(mapAcc, Scope.TypeSynonym(id, typ))
        case UclStateVarDecl(id, typ) => Scope.addToMap(mapAcc, Scope.StateVar(id, typ))
        case UclInputVarDecl(id, typ) => Scope.addToMap(mapAcc, Scope.InputVar(id, typ))
        case UclOutputVarDecl(id, typ) => Scope.addToMap(mapAcc, Scope.OutputVar(id, typ))
        case UclConstantDecl(id, typ) => Scope.addToMap(mapAcc, Scope.ConstantVar(id, typ)) 
        case UclFunctionDecl(id, sig) => Scope.addToMap(mapAcc, Scope.Function(id, sig.typ))
        case UclSpecDecl(id, expr) => Scope.addToMap(mapAcc, Scope.SpecVar(id, expr))
        case UclInitDecl(_) | UclNextDecl(_) => mapAcc
      }
    }
    return new ScopeMap(newMap)
  }
  /** Return a new context with the declarations in this procedure added to it. */
  def +(proc: UclProcedureDecl) : ScopeMap = {
    val map1 = proc.sig.inParams.foldLeft(map){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureInputArg(arg._1, arg._2))
    }
    val map2 = proc.sig.outParams.foldLeft(map1){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureOutputArg(arg._1, arg._2))
    }
    val map3 = proc.decls.foldLeft(map2){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureLocalVar(arg.id, arg.typ))
    }
    return new ScopeMap(map3)
  }
  /** Return a new context with the declarations in this lambda expression added to it. */
  def +(lambda: UclLambda) : ScopeMap = {
    val newMap = lambda.ids.foldLeft(map){ 
      (mapAcc, id) => Scope.addToMap(mapAcc, Scope.LambdaVar(id._1, id._2))
    }
    return new ScopeMap(newMap)
  }
  /** Return the type of an identifier in this context. */
  def typeOf(id : Identifier) : Option[Type] = {
    map.get(id).flatMap((e) => Some(e.typ))
  }
}
