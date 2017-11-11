/*
 * UCLID5 Verification and Synthesis Engine
 * 
 * Copyright (c) 2017. The Regents of the University of California (Regents). 
 * All Rights Reserved. 
 * 
 * Permission to use, copy, modify, and distribute this software
 * and its documentation for educational, research, and not-for-profit purposes,
 * without fee and without a signed licensing agreement, is hereby granted,
 * provided that the above copyright notice, this paragraph and the following two
 * paragraphs appear in all copies, modifications, and distributions. 
 * 
 * Contact The Office of Technology Licensing, UC Berkeley, 2150 Shattuck Avenue,
 * Suite 510, Berkeley, CA 94720-1620, (510) 643-7201, otl@berkeley.edu,
 * http://ipira.berkeley.edu/industry-info for commercial licensing opportunities.
 * 
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
 * INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING OUT OF
 * THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS
 * PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 * 
 * Authors: Rohit Sinha, Pramod Subramanyan

 * Defines ASTs for UCLID5
 *
 */

package uclid
package lang

import scala.collection.immutable.Map
import scala.util.parsing.input.Positional
import scala.util.parsing.input.Position
import scala.reflect.ClassTag

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
    filename match {
      case Some(fn) => fn + ", line " + pos.line.toString
      case None     => "line " + pos.line.toString
    }
  }
}

sealed  trait PositionedNode extends Positional {
  var filename : Option[String] = None
  def position = ASTPosition(filename, pos)
}

object ASTNode {
  def introducePos[T <: PositionedNode](setFilename : Boolean, node : Option[T], pos : ASTPosition) : Option[T] = {
    node match {
      case Some(n) => 
        var nP = n
        if (setFilename) { nP.filename = pos.filename }
        nP.pos = pos.pos
        Some(nP)
      case None =>
        None
    }
  }
  def introducePos[T <: PositionedNode](setFilename: Boolean, nodes : List[T], pos : ASTPosition) : List[T] = {
    nodes.map((n) => {
      var nP = n
      if (setFilename) { nP.filename = pos.filename }
      nP.pos = pos.pos
      nP
    })
  }
}


/** All elements in the AST are derived from this class.
 *  The plan is to stick an ID into this later so that we can use the ID to store auxiliary information.
 */
sealed trait ASTNode extends Positional with PositionedNode {
  val astNodeId = IdGenerator.newId()
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
  override def toString = "forall (" + Utils.join(vs.map((v) => v._1.toString + " : " + v._2.toString), ", ") + ") :: " 
  override def variables = vs
}
case class ExistsOp(vs: List[(Identifier, Type)]) extends QuantifiedBooleanOperator { 
  override def toString = "exists (" + Utils.join(vs.map((v) => v._1.toString + " : " + v._2.toString), ", ") + ") :: " 
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
  def width : Option[Int]
  def isConstantWidth : Boolean
}

case class ConstBitVectorSlice(hi: Int, lo: Int) extends BitVectorSlice  {
  Utils.assert(hi >= lo && hi >= 0 && lo >= 0, "Invalid bitvector slice: [" + hi.toString + ":" + lo.toString + "].")
  override def width = Some(hi - lo + 1)
  override def isConstantWidth = true
  override def toString = "[" + hi.toString + ":" + lo.toString + "]"
}
case class VarBitVectorSlice(hi: Expr, lo: Expr, wd : Option[Int] = None) extends BitVectorSlice {
  override def toString = "[" + hi.toString + ":" + lo.toString + "]"
  override def width = wd
  override def isConstantWidth = wd.isDefined
}

sealed abstract class ExtractOp extends Operator
case class ConstExtractOp(slice : ConstBitVectorSlice) extends ExtractOp {
  override def toString = slice.toString
  override def fixity = Operator.POSTFIX
}
case class VarExtractOp(slice : VarBitVectorSlice) extends ExtractOp {
  override def toString = slice.toString()
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
case class LhsSliceSelect(id: Identifier, bitslice : ConstBitVectorSlice) extends Lhs(id) {
  override def toString = id.toString + bitslice.toString
}
case class LhsVarSliceSelect(id: Identifier, bitslice: VarBitVectorSlice) extends Lhs(id) {
  override def toString = id.toString + bitslice.toString
}

sealed abstract class Type extends PositionedNode {
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
  def isUninterpreted = false
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
/** Undefined type. These will eventually be replaced.
 */
case class UndefinedType() extends Type {
  override def toString = "undefined"
}
/** 
 *  Uninterpreted types.
 */
case class UninterpretedType(name: Identifier) extends Type {
  override def toString = name.toString
  override def isUninterpreted = true
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

case class RecordType(members : List[(Identifier,Type)]) extends ProductType {
  override def fields = members
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
case class ModuleInstanceType(args : List[(Identifier, Option[Type])]) extends Type {
  def argToString(arg : (Identifier, Option[Type])) : String = {
    val id = arg._1
    arg._2 match {
      case Some(t) => id.toString + " : (" + t.toString + ")"
      case None => id.toString + " : ()"  
    }
  }
  override def toString = "(" + Utils.join(args.map(argToString(_)), ", ") + ")"
}
case class ModuleType(inputs: List[(Identifier, Type)], outputs: List[(Identifier, Type)]) extends Type {
  def argToString(arg: (Identifier, Type)) : String = {
    arg._1.toString + ": (" + arg._2.toString + ")"
  }
  def argsToString(args: List[(Identifier, Type)]) = 
    Utils.join(args.map(argToString(_)), ", ")

  override def toString = 
    "inputs (" + argsToString(inputs) + ") outputs (" + argsToString(outputs) + ")" 
}

/** Statements **/
sealed abstract class Statement extends ASTNode {
  override def toString = Utils.join(toLines, "\n") + "\n"
  def isLoop = false
  def toLines : List[String]
}
case class SkipStmt() extends Statement {
  override def toLines = List("skip; // " + position.toString)
}
case class AssertStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assert " + e + "; // " + position.toString)
}
case class AssumeStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assume " + e + "; // " + position.toString)
}
case class HavocStmt(id: Identifier) extends Statement {
  override def toLines = List("havoc " + id + "; // " + position.toString)
}
case class AssignStmt(lhss: List[Lhs], rhss: List[Expr]) extends Statement {
  override def toLines = 
    List(Utils.join(lhss.map (_.toString), ", ") + " := " + Utils.join(rhss.map(_.toString), ", ") + "; // " + position.toString)
}
case class IfElseStmt(cond: Expr, ifblock: List[Statement], elseblock: List[Statement]) extends Statement {
  override def toLines = List("if " + cond.toString + " // " + position.toString, "{ ") ++ 
                         ifblock.flatMap(_.toLines).map(PrettyPrinter.indent(1) + _) ++ 
                         List("} else {") ++ 
                         elseblock.flatMap(_.toLines).map(PrettyPrinter.indent(1) + _) ++ List("}")
}
case class ForStmt(id: ConstIdentifier, range: (NumericLit,NumericLit), body: List[Statement])
  extends Statement
{
  override def isLoop = true
  override def toLines = List("for " + id + " in range(" + range._1 +"," + range._2 + ") {  // " + position.toString) ++ 
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
    Utils.join(args.map(_.toString), ", ") + ") // " + id.position.toString)
}
case class ModuleCallStmt(id: Identifier) extends Statement {
  override def toLines = List("call (" + id.toString +")")
}
case class LocalVarDecl(id: Identifier, typ: Type) extends ASTNode {
  override def toString = "var " + id + ": " + typ + "; // " + id.position.toString
}
sealed abstract class IOSig(inputs: List[(Identifier,Type)], outputs: List[(Identifier,Type)]) extends ASTNode {
  type T = (Identifier,Type)
  val printfn = {(a: T) => a._1.toString + ": " + a._2}
  val typ = MapType(inputs.map(_._2), TupleType(outputs.map(_._2)))
}

case class ModuleSig(inParams: List[(Identifier, Type)], outParams: List[(Identifier, Type)]) extends IOSig(inParams, outParams) 
{
  override def toString =
    "inputs (" + Utils.join(inParams.map(printfn(_)), ", ") + ")" +
    " outputs " + "(" + Utils.join(outParams.map(printfn(_)), ", ") + ")"
}

case class ProcedureSig(inParams: List[(Identifier,Type)], outParams: List[(Identifier,Type)]) extends IOSig(inParams, outParams)
{
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

sealed abstract class Decl extends ASTNode {
  def declNames : List[Identifier]
}

case class InstanceDecl(moduleId : Identifier, instanceId : Identifier, arguments: List[(Identifier, Option[Expr])], instType : Option[ModuleInstanceType], modType : Option[ModuleType]) extends Decl
{
  def argToString(arg : (Identifier, Option[Expr])) = arg._2 match {
    case Some(e) => arg._1.toString + ":" + e.toString
    case None => arg._1.toString + ": ()"
  }
  val argsToString = Utils.join(arguments.map(argToString(_)), ", ")
  override def toString = "instance " + instanceId.toString + " : " + moduleId.toString + "(" + argsToString + "); // " + position.toString
  override def declNames = List(instanceId)
  def instanceType : Type = instType match {
    case None => UndefinedType()
    case Some(instT) => instT
  }
}

case class ProcedureDecl(id: Identifier, sig: ProcedureSig, 
  decls: List[LocalVarDecl], body: List[Statement]) extends Decl {
  override def toString = "procedure " + id + sig + PrettyPrinter.indent(1) + "{  // " + id.position.toString + "\n" +
                          Utils.join(decls.map(PrettyPrinter.indent(2) + _.toString), "\n") + "\n" + 
                          Utils.join(body.flatMap(_.toLines).map(PrettyPrinter.indent(2) + _), "\n") + 
                          "\n" + PrettyPrinter.indent(1) + "}"
  override def declNames = List(id)
}
case class TypeDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "type " + id + " = " + typ + "; // " + position.toString 
  override def declNames = List(id)
}
case class StateVarDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "var " + id + ": " + typ + "; // " + position.toString
  override def declNames = List(id)
}
/** StateVarsDecl represents var declarations of the form: vars x1, x2 : int.
 */
case class StateVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override def toString = "var " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class InputVarDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "input " + id + ": " + typ + "; // " + position.toString
  override def declNames = List(id)
}
/** InputVarsDecl is analogous to StateVarsDecl.
 */
case class InputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override def toString = "input " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class OutputVarDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "output " + id + ": " + typ + "; // " + position.toString
  override def declNames = List(id)
}
/** OutputVarsDecl is analogous to StateVarsDecl and InputVarsDecl.
 */
case class OutputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override def toString = "output " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class ConstantDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "constant " + id + ": " + typ + "; // " + position.toString
  override def declNames = List(id)
}
case class FunctionDecl(id: Identifier, sig: FunctionSig) extends Decl {
  override def toString = "function " + id + sig + ";  // " + position.toString 
  override def declNames = List(id)
}
case class InitDecl(body: List[Statement]) extends Decl {
  override def toString = 
    "init { // " + position.toString + "\n" +
    Utils.join(body.flatMap(_.toLines).map(PrettyPrinter.indent(2) + _), "\n") +  
    "\n" + PrettyPrinter.indent(1) + "}"
  override def declNames = List.empty
}
case class NextDecl(body: List[Statement]) extends Decl {
  override def toString = 
    "next {  // " + position.toString + "\n" + 
    Utils.join(body.flatMap(_.toLines).map(PrettyPrinter.indent(2) + _), "\n") +  
    "\n" + PrettyPrinter.indent(1) + "}"
  override def declNames = List.empty
}
case class SpecDecl(id: Identifier, expr: Expr) extends Decl {
  override def toString = "property " + id + ":" + expr + ";  // " + id.position.toString
  override def declNames = List(id)
}
case class AxiomDecl(id : Option[Identifier], expr: Expr) extends Decl {
  override def toString = {
    id match {
      case Some(id) => "axiom " + id.toString + " : " + expr.toString()
      case None => "axiom " + expr.toString
    }
  }
  override def declNames = id match { 
    case Some(i) => List(i)
    case _ => List.empty
  }
}
case class ProofCommand(name : Identifier, params: List[Identifier], args : List[Expr]) extends ASTNode {
  override def toString = {
    val nameStr = name.toString 
    val paramStr = if (params.size > 0) { "[" + Utils.join(params.map(_.toString), ", ") + "]" } else { "" }
    val argStr = if (args.size > 0) { "(" + Utils.join(args.map(_.toString), ", ") + ")" } else { "" }
    nameStr + paramStr + argStr + ";" + " // " + position.toString
  }
}

case class Module(id: Identifier, decls: List[Decl], cmds : List[ProofCommand]) extends ASTNode {
  // create a new module with with the filename set.
  def withFilename(name : String) : Module = {
    val newModule = Module(id, decls, cmds)
    newModule.filename = Some(name)
    return newModule
  }
  // find inputs.
  val inputs : List[InputVarDecl] = decls.filter(_.isInstanceOf[InputVarDecl]).map(_.asInstanceOf[InputVarDecl])
  // find outputs.
  val outputs : List[OutputVarDecl] = decls.filter(_.isInstanceOf[OutputVarDecl]).map(_.asInstanceOf[OutputVarDecl])
  // compute the "type" of this module.
  val moduleType : ModuleType = ModuleType(inputs.map(i => (i.id, i.typ)), outputs.map(o => (o.id, o.typ)))
  // find procedures.
  val procedures : List[ProcedureDecl] = decls.filter(_.isInstanceOf[ProcedureDecl]).map(_.asInstanceOf[ProcedureDecl])
  // find instances of other modules.
  val instances : List[InstanceDecl] = decls.filter(_.isInstanceOf[InstanceDecl]).map(_.asInstanceOf[InstanceDecl])
  // set of instance names (for easy searching.)
  lazy val instanceNames : Set[Identifier] = instances.map(_.instanceId).toSet 
  // find the init block.
  val init : Option[InitDecl] = {
    decls.find(_.isInstanceOf[InitDecl]).flatMap((d) => Some(d.asInstanceOf[InitDecl]))
  }
  // find the next block. 
  val next : Option[NextDecl] = {
    decls.find(_.isInstanceOf[NextDecl]).flatMap((d) => Some(d.asInstanceOf[NextDecl]))
  }
  // find all axioms.
  val axioms : List[AxiomDecl] = {
    decls.filter(_.isInstanceOf[AxiomDecl]).map(_.asInstanceOf[AxiomDecl])
  }

  override def toString = 
    "\nmodule " + id + " {\n" + 
      decls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i + "\n" } +
      PrettyPrinter.indent(1) + "control {" + "\n" + 
      cmds.foldLeft("")  { case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" } +
      PrettyPrinter.indent(1) + "}\n" + 
    "}\n"
}
