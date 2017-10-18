
/**
 * @author rohitsinha
 * With modifications by pramod.
 */
package uclid
package lang

import scala.collection.immutable.Map
import scala.util.parsing.input.Positional
import scala.util.parsing.input.Position

object PrettyPrinter
{
  val indentSeq = "  "
  def indent(n : Int) = indentSeq * n
}

/** Singleton that generates unique ids for AST nodes. */
object IdGenerator {
  type Id = Int
  var idCounter : Id = 0
  def newId() : Id = {
    val id = idCounter
    idCounter = idCounter + 1
    return id
  }
}
/**
 * An AST position consists of a filename and the Position type from the Scala std library.
 */
case class ASTPosition(filename : Option[String], pos : Position)  {
  override def toString : String = {
    (filename match {
      case Some(fn) => fn
      case None     => ""
    }) + ":" + pos.line.toString
  }
}

/** All elements in the AST are derived from this class.
 *  The plan is to stick an ID into this later so that we can use the ID to store auxiliary information.
 */
sealed trait ASTNode extends Positional {
  var filename : Option[String] = None
  def position : ASTPosition = ASTPosition(filename, pos)
  val astNodeId = IdGenerator.newId()
}

object ASTNode {
  def introducePos[T <: Positional](node : Option[T], pos : Position) : Option[T] = {
    node match {
      case Some(n) => 
        var nP = n
        nP.pos = pos
        Some(nP)
      case None =>
        None
    }
  }
  def introducePos[T <: Positional](node : List[T], pos : Position) : List[T] = {
    node.map((n) => {
      var nP = n
      nP.pos = pos
      nP
    })
  }
}
object Operator {
  val PREFIX = 0
  val INFIX = 1
  val POSTFIX = 2
}
sealed trait Operator extends ASTNode {
  def fixity : Int
  def isPolymorphic = false
}
// This is the polymorphic operator type. Typerchecker.rewrite converts these operators
// to either the integer or bitvector versions.
sealed abstract class PolymorphicOperator extends Operator {
  override def isPolymorphic = true
  override def fixity = Operator.INFIX
}
case class LTOp() extends PolymorphicOperator { override def toString = "<" }
case class LEOp() extends PolymorphicOperator { override def toString = "<=" }
case class GTOp() extends PolymorphicOperator { override def toString = ">" }
case class GEOp() extends PolymorphicOperator { override def toString = ">=" }
case class AddOp() extends PolymorphicOperator { override def toString = "+" }
case class SubOp() extends PolymorphicOperator { override def toString = "-" }
case class MulOp() extends PolymorphicOperator { override def toString = "*" }
// These are operators with integer operators.
sealed abstract class IntArgOperator extends Operator {
  override def fixity = Operator.INFIX
}
case class IntLTOp() extends IntArgOperator { override def toString = "<" }
case class IntLEOp() extends IntArgOperator { override def toString = "<=" }
case class IntGTOp() extends IntArgOperator { override def toString = ">" }
case class IntGEOp() extends IntArgOperator { override def toString = ">=" }
case class IntAddOp() extends IntArgOperator { override def toString ="+" }
case class IntSubOp() extends IntArgOperator { override def toString = "-" }
case class IntMulOp() extends IntArgOperator { override def toString = "*" }
// These operators take bitvector operands.
sealed abstract class BVArgOperator(val w : Int) extends Operator {
  override def fixity = Operator.INFIX
}
case class BVLTOp(override val w : Int) extends BVArgOperator(w) { override def toString = "<" }
case class BVLEOp(override val w : Int) extends BVArgOperator(w) { override def toString = "<=" }
case class BVGTOp(override val w : Int) extends BVArgOperator(w) { override def toString = ">" }
case class BVGEOp(override val w : Int) extends BVArgOperator(w) { override def toString = ">=" }
case class BVAddOp(override val w : Int) extends BVArgOperator(w) { override def toString ="+"  }
case class BVSubOp(override val w : Int) extends BVArgOperator(w) { override def toString = "-" }
case class BVMulOp(override val w : Int) extends BVArgOperator(w) { override def toString = "*" }
case class BVAndOp(override val w : Int) extends BVArgOperator(w) { override def toString = "&" }
case class BVOrOp(override val w : Int) extends BVArgOperator(w) { override def toString = "|" }
case class BVXorOp(override val w : Int) extends BVArgOperator(w) { override def toString = "^" }
case class BVNotOp(override val w : Int) extends BVArgOperator(w) { override def toString = "~" }
// Boolean operators.
sealed abstract class BooleanOperator extends Operator { 
  override def fixity = Operator.INFIX 
}
case class ConjunctionOp() extends BooleanOperator { override def toString = "&&" }
case class DisjunctionOp() extends BooleanOperator { override def toString = "||" }
case class IffOp() extends BooleanOperator { override def toString = "<==>" }
case class ImplicationOp() extends BooleanOperator { override def toString = "==>" }
case class NegationOp() extends BooleanOperator { 
  override def toString = "!"
  override def fixity = Operator.INFIX
}
// Quantifiers
sealed abstract class QuantifiedBooleanOperator extends BooleanOperator {
  override def fixity = Operator.PREFIX
  def variables : List[(Identifier, Type)]
}
case class ForallOp(vs : List[(Identifier, Type)]) extends QuantifiedBooleanOperator { 
  override def toString = "forall"
  override def variables = vs
}
case class ExistsOp(vs: List[(Identifier, Type)]) extends QuantifiedBooleanOperator { 
  override def toString = "exists"
  override def variables = vs
}

// (In-)equality operators.
sealed abstract class ComparisonOperator() extends Operator {
  override def fixity = Operator.INFIX
}
case class EqualityOp() extends ComparisonOperator { override def toString = "==" }
case class InequalityOp() extends ComparisonOperator { override def toString = "!=" } 

sealed abstract class TemporalOperator() extends Operator
sealed abstract class TemporalInfixOperator() extends TemporalOperator { override def fixity = Operator.INFIX }
sealed abstract class TemporalPrefixOperator() extends TemporalOperator { override def fixity = Operator.INFIX }
case class UntilTemporalOp() extends TemporalInfixOperator { override def toString = "U" }
case class WUntilTemporalOp() extends TemporalInfixOperator { override def toString = "W" }
case class ReleaseTemporalOp() extends TemporalInfixOperator { override def toString = "R" }
case class FinallyTemporalOp() extends TemporalPrefixOperator { override def toString = "F" }
case class GloballyTemporalOp() extends TemporalPrefixOperator { override def toString = "G" }
case class NextTemporalOp() extends TemporalPrefixOperator { override def toString = "X" }

abstract class BitVectorSlice extends ASTNode {
  def highIndex : Int = throw new Utils.UnimplementedException("Method highIndex not implemented.") 
  def lowIndex : Int = throw new Utils.UnimplementedException("Method lowIndex not implemented.")
  def width : Int = throw new Utils.UnimplementedException("Method width not implemented.")
  def isConstant : Boolean = throw new Utils.UnimplementedException("Method isConstant not implemented.")
}

case class ConstBitVectorSlice(hi: Int, lo: Int) extends BitVectorSlice  {
  Utils.assert(hi >= lo && hi >= 0 && lo >= 0, "Invalid bitvector slice: [" + hi.toString + ":" + lo.toString + "].")
  override def highIndex = hi
  override def lowIndex = lo
  override def width = (hi - lo + 1)
  override def isConstant = true
  override def toString = "[" + hi.toString + ":" + lo.toString + "]"
}
case class VarBitVectorSlice(hi: Expr, lo: Expr) extends BitVectorSlice {
  override def toString = "[" + hi.toString + ":" + lo.toString + "]"
}

case class ExtractOp(slice : ConstBitVectorSlice) extends Operator {
  override def toString = slice.toString
  override def fixity = Operator.POSTFIX
}

case class ConcatOp() extends Operator { 
  override def toString = "++"
  override def fixity = Operator.INFIX
}
case class RecordSelect(id: Identifier) extends Operator {
  override def toString = "." + id
  override def fixity = Operator.INFIX
}

sealed abstract class Expr extends ASTNode {
  /** Is this value a statically-defined constant? */
  def isConstant = false
}
sealed abstract class IdentifierBase(nam : String) extends Expr {
  val name = nam
  override def toString = name.toString
  override def equals (other: Any) : Boolean = {
    other match {
      case that : IdentifierBase => name == that.name
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()
}

case class Identifier(nam : String) extends IdentifierBase(nam)

// These are identifiers whose value is a statically-defined constant.
// For now, these are only created for the index variables in for loops.
case class ConstIdentifier(nam : String) extends IdentifierBase(nam) {
  override def isConstant = true
  override def toString = name.toString + "#const"
}

sealed abstract class Literal extends Expr {
  /** All literals are constants. */
  override def isConstant = true
  def isNumeric = false
}
sealed abstract class NumericLit extends Literal {
  override def isNumeric = true
  def typeOf : NumericType
  def to (n : NumericLit) : Seq[NumericLit]
}
case class BoolLit(value: Boolean) extends Literal {
  override def toString = value.toString
}

case class IntLit(value: BigInt) extends NumericLit {
  override def toString = value.toString
  override def typeOf : NumericType = IntType()
  override def to (n : NumericLit) : Seq[NumericLit]  = {
    n match {
      case i : IntLit => (value to i.value).map(IntLit(_))
      case _ => throw new Utils.RuntimeError("Cannot create range for differing types of numeric literals.")
    }
  } 
}

case class BitVectorLit(value: BigInt, width: Int) extends NumericLit {
  override def toString = value.toString + "bv" + width.toString
  override def  typeOf : NumericType = BitVectorType(width)
  override def to (n : NumericLit) : Seq[NumericLit] = {
    n match {
      case bv : BitVectorLit => (value to bv.value).map(BitVectorLit(_, width))
      case _ => throw new Utils.RuntimeError("Cannot create range for differening types of numeric literals.")
    }
  }
}

case class Tuple(values: List[Expr]) extends Expr {
  override def toString = "{" + Utils.join(values.map(_.toString), ", ") + "}"
}
//for symbols interpreted by underlying Theory solvers
case class OperatorApplication(op: Operator, operands: List[Expr]) extends Expr {
  override def isConstant = operands.forall(_.isConstant)
  override def toString = {
    op match {
      case RecordSelect(r) => 
        operands(0).toString + "." + r.toString
      case _ => 
        if (op.fixity == Operator.INFIX) {
          "(" + Utils.join(operands.map(_.toString), " " + op + " ") + ")"
        } else if (op.fixity == Operator.PREFIX) {
          op + "(" + Utils.join(operands.map(_.toString), ", ") + ")"
        } else {
          "(" + Utils.join(operands.map(_.toString), ", ") + ")" + op
        }
    }
  }
}
case class ArraySelectOperation(e: Expr, index: List[Expr]) extends Expr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]"
}
case class ArrayStoreOperation(e: Expr, index: List[Expr], value: Expr) extends Expr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]" + " := " + value
}
//for uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class FuncApplication(e: Expr, args: List[Expr]) extends Expr {
  override def toString = e + "(" + args.tail.fold(args.head.toString)
    { (acc,i) => acc + "," + i } + ")"
}
case class ITE(e: Expr, t: Expr, f: Expr) extends Expr {
  override def toString = "ITE(" + e + "," + t + "," + f + ")"
}
case class Lambda(ids: List[(Identifier,Type)], e: Expr) extends Expr {
  override def toString = "Lambda(" + ids + "). " + e
}

sealed abstract class Lhs(val ident: Identifier) extends ASTNode
case class LhsId(id: Identifier) extends Lhs(id) {
  override def toString = id.toString
}
case class LhsArraySelect(id: Identifier, indices: List[Expr]) extends Lhs(id) {
  override def toString = id.toString + "[" + Utils.join(indices.map(_.toString), ", ") + "]"
}
case class LhsRecordSelect(id: Identifier, fields: List[Identifier]) extends Lhs(id) {
  override def toString = id.toString + "." + Utils.join(fields.map(_.toString), ".")
}
case class LhsSliceSelect(id: Identifier, bitslice: ConstBitVectorSlice) extends Lhs(id) {
  override def toString = id.toString + bitslice.toString
}

sealed abstract class Type extends Positional {
  def isBool = false
  def isNumeric = false
  def isInt = false
  def isBitVector = false
  def isTemporal = false
  def isPrimitive = false
  def isProduct = false
  def isRecord = false
  def isTuple = false
  def isMap = false
  def isArray = false
  def matches (t2 : Type) = (this == t2)
}

/**
 * Primitive types: Int, Bool and BitVector.
 */
sealed abstract class PrimitiveType extends Type {
  override def isPrimitive = true
}
/** 
 *  Numeric types base class. All numeric types are also primitive types.
 */
sealed abstract class NumericType extends PrimitiveType {
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
case class BoolType() extends PrimitiveType {
  override def toString = "bool"
  override def isBool = true
}
case class IntType() extends NumericType { 
  override def toString = "int"
  override def isInt = true
}
case class BitVectorType(width: Int) extends NumericType {
  override def toString = "bv" + width.toString
  override def isBitVector = true
  def isValidSlice(slice : ConstBitVectorSlice) : Boolean = {
    return (slice.lo >= 0 && slice.hi < width)
  }
}
case class EnumType(ids: List[Identifier]) extends Type {
  override def toString = "enum {" + 
    ids.tail.foldLeft(ids.head.toString) {(acc,i) => acc + "," + i} + "}"
}
abstract sealed class ProductType extends Type {
  override def isProduct = true
  def fields : List[(Identifier, Type)]
  def numFields : Int = fields.length
  def fieldType(i : Int) : Option[Type] = {
    if (i >= 0 && i < fields.length) Some(fields(i)._2)
    else None
  }
  
  def fieldType(fieldName : Identifier) : Option[Type] = {
    fieldIndex(fieldName) match {
      case -1 => None
      case i  => Some(fields(i)._2)
    }
  }

  def nestedFieldType(fields : List[Identifier]) : Option[Type] = {
    val thisType : Option[Type] = Some(this)
    fields.foldLeft(thisType)((acc, f) => {
      acc.flatMap((typ) => {
        typ match {
          case prodType : ProductType => prodType.fieldType(f)
          case _ => None
        }
      })
    }) 
  }
  
  def fieldIndex(name : Identifier) : Int = fields.indexWhere((p) => p._1 == name)
  def hasField(fieldName : Identifier) : Boolean = {
    fieldIndex(fieldName) != -1
  }
}
case class TupleType(fieldTypes: List[Type]) extends ProductType {
  override def fields = fieldTypes.zipWithIndex.map(p  => (Identifier("_" + (p._2+1).toString), p._1))  
  override def toString = "{" + Utils.join(fieldTypes.map(_.toString), ", ") + "}"
  override def isTuple = true
}

case class RecordType(fields_ : List[(Identifier,Type)]) extends ProductType {
  Utils.assert(Utils.allUnique(fields_.map(_._1)), "Record field names must be unique.")
  override def fields = fields_
  override def toString = "record {" + Utils.join(fields.map((f) => f._1.toString + " : " + f._2.toString), ", ")  + "}"
  override def isRecord = true
  override def matches(t2 : Type) : Boolean = {
    t2 match {
      case tup : TupleType => 
          fields.size == tup.fieldTypes.size && 
          (fields.map(_._2) zip tup.fieldTypes).forall( tpair => tpair._1.matches(tpair._2))
      case _ => this == t2
    }
  }
}
case class MapType(inTypes: List[Type], outType: Type) extends Type {
  override def toString = Utils.join(inTypes.map(_.toString), " * ") + " -> " + outType.toString
  override def isMap = true
}

case class ArrayType(inTypes: List[Type], outType: Type) extends Type {
  override def toString = "[" + Utils.join(inTypes.map(_.toString), " * ") + "] " + outType.toString
  override def isArray = true
}
case class SynonymType(id: Identifier) extends Type {
  override def toString = id.toString
  override def equals(other: Any) = other match {
    case that: SynonymType => that.id.name == this.id.name
    case _ => false
  }
}

/** Statements **/
sealed abstract class Statement extends ASTNode {
  override def toString = Utils.join(toLines, "\n") + "\n"
  def isLoop = false
  def toLines : List[String]
}
case class SkipStmt() extends Statement {
  override def toLines = List("skip; //" + pos.toString)
}
case class AssertStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assert " + e + "; //" + pos.toString)
}
case class AssumeStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assume " + e + "; //" + pos.toString)
}
case class HavocStmt(id: Identifier) extends Statement {
  override def toLines = List("havoc " + id + "; //" + pos.toString)
}
case class AssignStmt(lhss: List[Lhs], rhss: List[Expr]) extends Statement {
  override def toLines = 
    List(Utils.join(lhss.map (_.toString), ", ") + " := " + Utils.join(rhss.map(_.toString), ", ") + "; // " + pos.toString)
}
case class IfElseStmt(cond: Expr, ifblock: List[Statement], elseblock: List[Statement]) extends Statement {
  override def toLines = List("if " + cond.toString + " // " + pos.toString, "{ ") ++ 
                         ifblock.flatMap(_.toLines).map(PrettyPrinter.indent(1) + _) ++ 
                         List("} else {") ++ 
                         elseblock.flatMap(_.toLines).map(PrettyPrinter.indent(1) + _) ++ List("}")
}
case class ForStmt(id: ConstIdentifier, range: (NumericLit,NumericLit), body: List[Statement])
  extends Statement
{
  override def isLoop = true
  override def toLines = List("for " + id + " in range(" + range._1 +"," + range._2 + ") {  // " + pos.toString) ++ 
                         body.flatMap(_.toLines).map(PrettyPrinter.indent(1) + _) ++ List("}")
}
case class CaseStmt(body: List[(Expr,List[Statement])]) extends Statement {
  override def toLines = List("case") ++
    body.flatMap{ (i) => List(PrettyPrinter.indent(1) + i._1.toString + " : ") ++ i._2.flatMap(_.toLines).map(PrettyPrinter.indent(2) + _)} ++ 
    List("esac")
}
case class ProcedureCallStmt(id: Identifier, callLhss: List[Lhs], args: List[Expr])  extends Statement {
  override def toLines = List("call (" +
    Utils.join(callLhss.map(_.toString), ", ") + ") := " + id + "(" +
    Utils.join(args.map(_.toString), ", ") + ") // " + id.pos.toString)
}

case class LocalVarDecl(id: Identifier, typ: Type) extends ASTNode {
  override def toString = "var " + id + ": " + typ + "; // " + id.pos.toString
}

case class ProcedureSig(inParams: List[(Identifier,Type)], 
                           outParams: List[(Identifier,Type)]) 
           extends ASTNode
{
  type T = (Identifier,Type)
  val printfn = {(a: T) => a._1.toString + ": " + a._2}
  val typ = MapType(inParams.map(_._2), TupleType(outParams.map(_._2)))
  override def toString =
    "(" + Utils.join(inParams.map(printfn(_)), ", ") + ")" +
    " returns " + "(" + Utils.join(outParams.map(printfn(_)), ", ") + ")"
}
case class FunctionSig(args: List[(Identifier,Type)], retType: Type) extends ASTNode {
  type T = (Identifier,Type)
  val typ = MapType(args.map(_._2), retType)
  val printfn = {(a: T) => a._1.toString + ": " + a._2}
  override def toString = "(" + Utils.join(args.map(printfn(_)), ", ") + ")" +
    ": " + retType
}

sealed abstract class Decl extends ASTNode
case class ProcedureDecl(id: Identifier, sig: ProcedureSig, 
  decls: List[LocalVarDecl], body: List[Statement]) extends Decl {
  override def toString = "procedure " + id + sig + PrettyPrinter.indent(1) + "{  // " + id.pos.toString + "\n" +
                          Utils.join(decls.map(PrettyPrinter.indent(2) + _.toString), "\n") + "\n" + 
                          Utils.join(body.flatMap(_.toLines).map(PrettyPrinter.indent(2) + _), "\n") + 
                          "\n" + PrettyPrinter.indent(1) + "}"
}
case class TypeDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "type " + id + " = " + typ + "; // " + pos.toString 
}
case class StateVarDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "var " + id + ": " + typ + "; // " + pos.toString
}
case class InputVarDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "input " + id + ": " + typ + "; // " + pos.toString
}
case class OutputVarDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "output " + id + ": " + typ + "; // " + pos.toString
}
case class ConstantDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "constant " + id + ": " + typ + "; // " + pos.toString
}
case class FunctionDecl(id: Identifier, sig: FunctionSig)
extends Decl {
  override def toString = "function " + id + sig + ";  // " + pos.toString 
}
case class InitDecl(body: List[Statement]) extends Decl {
  override def toString = 
    "init { // " + pos.toString + "\n" +
    Utils.join(body.flatMap(_.toLines).map(PrettyPrinter.indent(2) + _), "\n") +  
    "\n" + PrettyPrinter.indent(1) + "}"
}
case class NextDecl(body: List[Statement]) extends Decl {
  override def toString = 
    "next {  // " + pos.toString + "\n" + 
    Utils.join(body.flatMap(_.toLines).map(PrettyPrinter.indent(2) + _), "\n") +  
    "\n" + PrettyPrinter.indent(1) + "}"
}
case class SpecDecl(id: Identifier, expr: Expr) extends Decl {
  override def toString = "property " + id + ":" + expr + ";  // " + id.pos.toString
}

case class ProofCommand(name : Identifier, params: List[Identifier], args : List[Expr]) extends ASTNode {
  override def toString = {
    val nameStr = name.toString 
    val paramStr = if (params.size > 0) { "[" + Utils.join(params.map(_.toString), ", ") + "]" } else { "" }
    val argStr = if (args.size > 0) { "(" + Utils.join(args.map(_.toString), ", ") + ")" } else { "" }
    nameStr + paramStr + argStr + ";"
  }
}

case class Module(id: Identifier, decls: List[Decl], cmds : List[ProofCommand]) extends ASTNode {
  // create a new module with with the filename set.
  def withFilename(name : String) : Module = {
    val newModule = Module(id, decls, cmds)
    newModule.filename = Some(name)
    return newModule
  }

  override def toString = 
    "\nmodule " + id + " {\n" + 
      decls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i + "\n" } +
      PrettyPrinter.indent(1) + "control {" + "\n" + 
      cmds.foldLeft("")  { case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" } +
      PrettyPrinter.indent(1) + "}\n" + 
    "}\n"
}

object Scope {
  sealed abstract class NamedExpression(val id : IdentifierBase, val typ: Type) {
    val isReadOnly = false
  }
  sealed abstract class ReadOnlyNamedExpression(id : IdentifierBase, typ: Type) extends NamedExpression(id, typ) {
    override val isReadOnly = true
  }
  case class TypeSynonym(typId : Identifier, sTyp: Type) extends ReadOnlyNamedExpression(typId, sTyp)
  case class StateVar(varId : Identifier, varTyp: Type) extends NamedExpression(varId, varTyp)
  case class InputVar(inpId : Identifier, inpTyp: Type) extends ReadOnlyNamedExpression(inpId, inpTyp)
  case class OutputVar(outId : Identifier, outTyp: Type) extends NamedExpression(outId, outTyp)
  case class ConstantVar(cId : IdentifierBase, cTyp : Type) extends ReadOnlyNamedExpression(cId, cTyp)
  case class Function(fId : Identifier, fTyp: Type) extends ReadOnlyNamedExpression(fId, fTyp)
  case class Procedure(pId : Identifier, pTyp: Type) extends ReadOnlyNamedExpression(pId, pTyp)
  case class ProcedureInputArg(argId : Identifier, argTyp: Type) extends ReadOnlyNamedExpression(argId, argTyp)
  case class ProcedureOutputArg(argId : Identifier, argTyp: Type) extends NamedExpression(argId, argTyp)
  case class ProcedureLocalVar(vId : Identifier, vTyp : Type) extends NamedExpression(vId, vTyp)
  case class LambdaVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)
  case class ForIndexVar(iId : ConstIdentifier, iTyp : Type) extends ReadOnlyNamedExpression(iId, iTyp)
  case class SpecVar(varId : Identifier, expr: Expr) extends NamedExpression(varId, BoolType())
  case class EnumIdentifier(enumId : Identifier, enumTyp : EnumType) extends NamedExpression(enumId, enumTyp)
  case class ForallVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)
  case class ExistsVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)

  type IdentifierMap = Map[IdentifierBase, NamedExpression]
  def addToMap(map : Scope.IdentifierMap, expr: Scope.NamedExpression) : Scope.IdentifierMap = {
    map + (expr.id -> expr)
  }
  def addTypeToMap(map : Scope.IdentifierMap, typ : Type, module : Option[Module]) : Scope.IdentifierMap = {
    typ match {
      case enumTyp : EnumType => 
        enumTyp.ids.foldLeft(map)((m, id) => {
          m.get(id) match {
            case Some(namedExpr) =>
              namedExpr match {
                case EnumIdentifier(eId, eTyp) =>
                  Utils.checkParsingError(eTyp == enumTyp, 
                      "Identifier " + eId.nam + " redeclared as a member of a different enum.", 
                      eTyp.pos, module.flatMap(_.filename))
                  m
                case _ =>
                  Utils.raiseParsingError("Redeclaration of identifier " + id.name, id.pos, module.flatMap(_.filename))
                  m
              }
            case None =>
              m + (id -> EnumIdentifier(id, enumTyp))
          }
        })
      case _ =>
        map
    }
  }
}

case class ScopeMap (map: Scope.IdentifierMap, module : Option[Module], procedure : Option[ProcedureDecl]) {
  /** Check if a variable name exists in this context. */
  def doesNameExist(name: IdentifierBase) = map.contains(name)
  /** Return the NamedExpression. */
  def get(id: IdentifierBase) : Option[Scope.NamedExpression] = map.get(id)
  /** Return the filename. */
  def filename : Option[String] = {
    module.flatMap((m) => m.filename)
  }
  /** Create an empty context. */
  def this() {
    this(Map.empty[IdentifierBase, Scope.NamedExpression], None, None)
  }
  /** Return a new context with this identifier added to the current context. */
  def +(expr: Scope.NamedExpression) : ScopeMap = {
    new ScopeMap(map + (expr.id -> expr), module, procedure)
  }
  def +(typ : Type) : ScopeMap = {
    ScopeMap(Scope.addTypeToMap(map, typ, module), module, procedure)
  }
  
  /** Return a new context with the declarations in this module added to it. */
  def +(m: Module) : ScopeMap = { 
    Utils.assert(module.isEmpty, "A module was already added to this Context.")
    val m1 = m.decls.foldLeft(map){ (mapAcc, decl) =>
      decl match {
        case ProcedureDecl(id, sig, _, _) => Scope.addToMap(mapAcc, Scope.Procedure(id, sig.typ))
        case TypeDecl(id, typ) => Scope.addToMap(mapAcc, Scope.TypeSynonym(id, typ))
        case StateVarDecl(id, typ) => Scope.addToMap(mapAcc, Scope.StateVar(id, typ))
        case InputVarDecl(id, typ) => Scope.addToMap(mapAcc, Scope.InputVar(id, typ))
        case OutputVarDecl(id, typ) => Scope.addToMap(mapAcc, Scope.OutputVar(id, typ))
        case ConstantDecl(id, typ) => Scope.addToMap(mapAcc, Scope.ConstantVar(id, typ)) 
        case FunctionDecl(id, sig) => Scope.addToMap(mapAcc, Scope.Function(id, sig.typ))
        case SpecDecl(id, expr) => Scope.addToMap(mapAcc, Scope.SpecVar(id, expr))
        case InitDecl(_) | NextDecl(_) => mapAcc
      }
    }
    val m2 = m.decls.foldLeft(m1){(mapAcc, decl) =>
      decl match {
        case ProcedureDecl(id, sig, _, _) => 
          val m1 = sig.inParams.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = sig.outParams.foldLeft(m1)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          m2
        case FunctionDecl(id, sig) =>
          val m1 = sig.args.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = Scope.addTypeToMap(m1, sig.retType, Some(m))
          m2
        case TypeDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case StateVarDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case InputVarDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case OutputVarDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case ConstantDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case _ => mapAcc          
      }
    }
    ScopeMap(m2, Some(m), None)
  }
  /** Return a new context with the declarations in this procedure added to it. */
  def +(proc: ProcedureDecl) : ScopeMap = {
    Utils.assert(procedure.isEmpty, "A procedure was already added to this context.")
    val map1 = proc.sig.inParams.foldLeft(map){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureInputArg(arg._1, arg._2))
    }
    val map2 = proc.sig.outParams.foldLeft(map1){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureOutputArg(arg._1, arg._2))
    }
    val map3 = proc.decls.foldLeft(map2){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureLocalVar(arg.id, arg.typ))
    }
    return new ScopeMap(map3, module, Some(proc))
  }
  /** Return a new context with the declarations in this lambda expression added to it. */
  def +(lambda: Lambda) : ScopeMap = {
    val newMap = lambda.ids.foldLeft(map){ 
      (mapAcc, id) => Scope.addToMap(mapAcc, Scope.LambdaVar(id._1, id._2))
    }
    return new ScopeMap(newMap, module, procedure)
  }
  /** Return a new context with quantifier variables added. */
  def +(opapp : OperatorApplication) : ScopeMap = {
    return opapp.op match {
      case ForallOp(vs) =>
        new ScopeMap(
            vs.foldLeft(map)((mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ForallVar(arg._1, arg._2))),
            module, procedure)
      case ExistsOp(vs) =>
        new ScopeMap(
            vs.foldLeft(map)((mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ForallVar(arg._1, arg._2))),
            module, procedure)
      case _ => this
    }
  }

  /** Return the type of an identifier in this context. */
  def typeOf(id : IdentifierBase) : Option[Type] = {
    map.get(id).flatMap((e) => Some(e.typ))
  }
}
