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
 * Authors: Rohit Sinha, Pramod Subramanyan

 * Defines ASTs for UCLID5
 *
 */

package uclid
package lang

import scala.collection.immutable.Map
import scala.collection.mutable.{Map => MutableMap}
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
  def errorString() : String = {
    if (pos.line > 0) {
      filename match {
        case Some(fn) => " at " + fn + ", line " + pos.line.toString()
        case None => "at line " + pos.line.toString()
      }
    } else {
      ""
    }
  }
}

sealed  trait PositionedNode extends Positional {
  var filename : Option[String] = None
  def position = ASTPosition(filename, pos)
}

object ASTNode {
  def introducePos[T <: PositionedNode](setPosition : Boolean, setFilename : Boolean, node : T, pos : ASTPosition) : T = {
    if (setPosition || node.pos.line == 0) {
      var nodeP = node
      if (setFilename || nodeP.filename.isEmpty) { nodeP.filename = pos.filename }
      nodeP.pos = pos.pos
      nodeP
    } else {
      node
    }
  }

  def introducePos[T <: PositionedNode](setPosition : Boolean, setFilename : Boolean, node : Option[T], pos : ASTPosition) : Option[T] = {
    node match {
      case Some(n) =>
        if (setPosition || n.pos.line == 0) {
          var nP = n
          if (setFilename || nP.filename.isEmpty) { nP.filename = pos.filename }
          nP.pos = pos.pos
          Some(nP)
        } else {
          Some(n)
        }
      case None =>
        None
    }
  }
  def introducePos[T <: PositionedNode](setPosition : Boolean, setFilename: Boolean, nodes : List[T], pos : ASTPosition) : List[T] = {
    nodes.map((n) => {
      if (setPosition || n.pos.line == 0) {
        var nP = n
        if (setFilename || nP.filename.isEmpty) { nP.filename = pos.filename }
        nP.pos = pos.pos
        nP
      } else {
        n
      }
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

  def Y(x : Expr) = OperatorApplication(HistoryOperator(), List(x, IntLit(1)))
  def not(x : Expr) = OperatorApplication(NegationOp(), List(x))
  def and(x : Expr, y : Expr) = OperatorApplication(ConjunctionOp(), List(x, y))
  def or(x : Expr, y : Expr) = OperatorApplication(DisjunctionOp(), List(x, y))
  def imply(x : Expr, y : Expr) = OperatorApplication(ImplicationOp(), List(x, y))
  def ite(c : Expr, x : Expr, y : Expr) = OperatorApplication(ITEOp(), List(c, x, y))
  def old(c : Identifier) = OperatorApplication(OldOperator(), List(c))
  def history(c : Identifier, e : Expr) = OperatorApplication(HistoryOperator(), List(c, e))
}
sealed trait Operator extends ASTNode {
  def fixity : Int
  def isPolymorphic = false
  def isTemporal = false
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
case class UnaryMinusOp() extends PolymorphicOperator {
  override def toString = "-"
  override def fixity = Operator.PREFIX
}
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
case class IntUnaryMinusOp() extends IntArgOperator {
  override def toString = "-"
  override def fixity = Operator.PREFIX
}
// These operators take bitvector operands.
sealed abstract class BVArgOperator(val w : Int) extends Operator {
  override def fixity = Operator.INFIX
  val arity = 2
}
case class BVLTOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<"
}
case class BVLEOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<="
}
case class BVGTOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">"
}
case class BVGEOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">="
}
case class BVAddOp(override val w : Int) extends BVArgOperator(w) {
  override def toString ="+"
}
case class BVSubOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "-"
}
case class BVMulOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "*"
}
case class BVAndOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "&"
}
case class BVOrOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "|"
}
case class BVXorOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "^"
}
case class BVNotOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "~"
  override val arity = 1
}
case class BVUnaryMinusOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "-"
  override val arity = 1
}
case class BVSignExtOp(override val w : Int, val e : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_sign_extend"
  override val arity = 1
}
case class BVZeroExtOp(override val w : Int, val e : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_zero_extend"
  override val arity = 1
}
case class BVLeftShiftOp(override val w : Int, val e : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_left_shift"
  override val arity = 1
}
case class BVLRightShiftOp(override val w : Int, val e : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_l_right_shift"
  override val arity = 1
}
case class BVARightShiftOp(override val w : Int, val e : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_a_right_shift"
  override val arity = 1
}
// Boolean operators.
sealed abstract class BooleanOperator extends Operator {
  override def fixity = Operator.INFIX
  def isQuantified = false
}
case class ConjunctionOp() extends BooleanOperator {
  override def toString = "&&"
}
case class DisjunctionOp() extends BooleanOperator {
  override def toString = "||"
}
case class IffOp() extends BooleanOperator {
  override def toString = "<==>"
}
case class ImplicationOp() extends BooleanOperator {
  override def toString = "==>"
}
case class NegationOp() extends BooleanOperator {
  override def fixity = Operator.PREFIX
  override def toString = "!"
}
// Quantifiers
sealed abstract class QuantifiedBooleanOperator extends BooleanOperator {
  override def fixity = Operator.PREFIX
  override def isQuantified = true
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

sealed abstract class TemporalOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def isTemporal = true
}
case class GloballyTemporalOp() extends TemporalOperator { override def toString = "G" }
case class NextTemporalOp() extends TemporalOperator { override def toString = "X" }
case class UntilTemporalOp() extends TemporalOperator { override def toString = "U" }
case class FinallyTemporalOp() extends TemporalOperator { override def toString = "F" }
case class ReleaseTemporalOp() extends TemporalOperator { override def toString = "R" }
case class WUntilTemporalOp() extends TemporalOperator { override def toString = "W" }

// "Old" operator.
case class OldOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def toString = "old"
}
case class PastOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def toString = "past"
}
case class HistoryOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def toString = "history"
}
// ITE operator
case class ITEOp() extends Operator {
  override def toString = "ite"
  override def fixity = Operator.PREFIX
}

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
case class PolymorphicSelect(id : Identifier) extends Operator {
  override def toString = "." + id
  override def fixity = Operator.POSTFIX
}
case class RecordSelect(id: Identifier) extends Operator {
  override def toString = "." + id
  override def fixity = Operator.INFIX
}
case class HyperSelect(i: Int) extends Operator {
  override def toString: String = "." + i.toString
  override def fixity = Operator.INFIX
}
case class SelectFromInstance(varId : Identifier) extends Operator {
  override def toString = "." + varId
  override def fixity = Operator.INFIX
}
case class GetNextValueOp() extends Operator {
  override def toString = "'"
  override def fixity = Operator.POSTFIX
}
case class DistinctOp() extends Operator {
  override def toString = "distinct"
  override def fixity = Operator.INFIX
}
sealed abstract class Expr extends ASTNode {
  /** Is this value a statically-defined constant? */
  def isConstant = false
  def isTemporal = false
}
sealed abstract class PossiblyTemporalExpr extends Expr

case class Identifier(name : String) extends Expr {
  override def toString = name.toString
}
case class ExternalIdentifier(moduleId : Identifier, id : Identifier) extends Expr {
  override def toString = moduleId.toString + "::" + id.toString
}
sealed abstract class Literal extends Expr {
  /** All literals are constants. */
  override def isConstant = true
  def isNumeric = false
}
/** A non-deterministic new constant. */
case class FreshLit(typ : Type) extends Literal {
  override def toString = "*"
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
  override def typeOf : NumericType = IntegerType()
  override def to (n : NumericLit) : Seq[NumericLit]  = {
    n match {
      case i : IntLit => (value to i.value).map(IntLit(_))
      case _ => throw new Utils.RuntimeError("Cannot create range for differing types of numeric literals.")
    }
  }
}

case class BitVectorLit(value: BigInt, width: Int) extends NumericLit {
  override def toString = value.toString + "bv" + width.toString
  override def typeOf : NumericType = BitVectorType(width)
  override def to (n : NumericLit) : Seq[NumericLit] = {
    n match {
      case bv : BitVectorLit => (value to bv.value).map(BitVectorLit(_, width))
      case _ => throw new Utils.RuntimeError("Cannot create range for differening types of numeric literals.")
    }
  }
}

case class StringLit(value: String) extends Literal {
  override def toString = "\"" + value + "\""
}

case class ConstArray(exp: Expr, typ: Type) extends Expr {
  override def toString  = "const(%s, %s)".format(exp.toString(), typ.toString())
}

case class Tuple(values: List[Expr]) extends Expr {
  override def toString = "{" + Utils.join(values.map(_.toString), ", ") + "}"
  // FIXME: We should not have temporal values inside of a tuple.
  override def isTemporal = false
}
//for symbols interpreted by underlying Theory solvers
case class OperatorApplication(op: Operator, operands: List[Expr]) extends PossiblyTemporalExpr {
  override def isConstant = operands.forall(_.isConstant)
  override def toString = {
    op match {
      case PolymorphicSelect(r) =>
        operands(0).toString + "." + r.toString()
      case RecordSelect(r) =>
        operands(0).toString + "." + r.toString
      case HyperSelect(i) =>
        operands(0).toString + "." + i.toString
      case SelectFromInstance(f) =>
        operands(0).toString + "." + f.toString
      case ForallOp(_) | ExistsOp(_) =>
        "(" + op.toString + operands(0).toString + ")"
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
  override def isTemporal = op.isTemporal || operands.exists(_.isTemporal)
}
case class ArraySelectOperation(e: Expr, index: List[Expr]) extends Expr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]"
}
case class ArrayStoreOperation(e: Expr, index: List[Expr], value: Expr) extends Expr {
  override def toString = e + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i } + "]" + " = " + value
}
//for uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class FuncApplication(e: Expr, args: List[Expr]) extends Expr {
  override def toString = e + "(" + Utils.join(args.map(_.toString), ", ") + ")"
}
case class Lambda(ids: List[(Identifier,Type)], e: Expr) extends Expr {
  override def toString = "Lambda(" + ids + "). " + e
}

sealed abstract class Lhs(val ident: Identifier) extends ASTNode {
  def isProceduralLhs : Boolean
}
case class LhsId(id: Identifier) extends Lhs(id) {
  override def toString = id.toString
  override def isProceduralLhs = true
}
case class LhsNextId(id: Identifier) extends Lhs(id) {
  override def toString = id.toString + "'"
  override def isProceduralLhs = false
}
case class LhsArraySelect(id: Identifier, indices: List[Expr]) extends Lhs(id) {
  override def toString = id.toString + "[" + Utils.join(indices.map(_.toString), ", ") + "]"
  override def isProceduralLhs = true
}
case class LhsRecordSelect(id: Identifier, fields: List[Identifier]) extends Lhs(id) {
  override def toString = id.toString + "." + Utils.join(fields.map(_.toString), ".")
  override def isProceduralLhs = true
}
case class LhsSliceSelect(id: Identifier, bitslice : ConstBitVectorSlice) extends Lhs(id) {
  override def toString = id.toString + bitslice.toString
  override def isProceduralLhs = true
}
case class LhsVarSliceSelect(id: Identifier, bitslice: VarBitVectorSlice) extends Lhs(id) {
  override def toString = id.toString + bitslice.toString
  override def isProceduralLhs = true
}

/** Type decorators for expressions. */
sealed abstract class ExprDecorator extends ASTNode
case class UnknownDecorator(value: String) extends ExprDecorator {
  override def toString = value
}
case object LTLExprDecorator extends ExprDecorator {
  override def toString = "LTL"
}
case class HyperpropertyDecorator(k: Int) extends ExprDecorator {
  override def toString = k.toString()
}
case object LTLSafetyFragmentDecorator extends ExprDecorator {
  override def toString = "LTLSafetyFragment"
}
case object LTLLivenessFragmentDecorator extends ExprDecorator {
  override def toString = "LTLLivenessFragment"
}
case object CoverDecorator extends ExprDecorator {
  override def toString = "cover"
}

object ExprDecorator {
  /** Factory constructor. */
  def parse(e : Expr) : ExprDecorator = {
    val dec = e match {
      case Identifier(id) =>
        if (id == "LTL") {
          LTLExprDecorator
        } else {
          UnknownDecorator(e.toString)
        }
      case _ => UnknownDecorator(e.toString)
    }
    dec.pos = e.pos
    return dec
  }
  def isLTLProperty(decs : List[ExprDecorator]) : Boolean = {
    decs.exists(p => p == LTLSafetyFragmentDecorator ||
                     p == LTLLivenessFragmentDecorator ||
                     p == LTLExprDecorator)
  }
  def isHyperproperty(decs : List[ExprDecorator]) : Boolean = {
    decs.exists(p => p.isInstanceOf[HyperpropertyDecorator])
  }
}

sealed abstract class Type extends PositionedNode {
  def isBool = false
  def isNumeric = false
  def isInt = false
  def isBitVector = false
  def isPrimitive = false
  def isProduct = false
  def isRecord = false
  def isTuple = false
  def isMap = false
  def isArray = false
  def isUninterpreted = false
  def ids = List.empty[Identifier]
  def matches (t2 : Type) = (this == t2)
  def defaultValue : Option[Expr] = None
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

/** Undefined type. These will eventually be rewritten in the AST.
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
case class BooleanType() extends PrimitiveType {
  override def toString = "boolean"
  override def isBool = true
  override def defaultValue = Some(BoolLit(false))
}
case class IntegerType() extends NumericType {
  override def toString = "integer"
  override def isInt = true
  override def defaultValue = Some(IntLit(0))
}
case class BitVectorType(width: Int) extends NumericType {
  override def toString = "bv" + width.toString
  override def isBitVector = true
  def isValidSlice(slice : ConstBitVectorSlice) : Boolean = {
    return (slice.lo >= 0 && slice.hi < width)
  }
  override def defaultValue = Some(BitVectorLit(0, width))
}
case class StringType() extends PrimitiveType {
  override def toString = "string"
  override def defaultValue = Some(StringLit(""))
}
case class EnumType(ids_ : List[Identifier]) extends Type {
  override def ids = ids_
  override def toString = "enum {" +
    ids.tail.foldLeft(ids.head.toString) {(acc,i) => acc + "," + i} + "}"
  override def defaultValue = {
    ids match {
      case hd :: tl => Some(hd)
      case nil => None
    }
  }
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
  override def defaultValue = {
    val defaults = fieldTypes.map(_.defaultValue).flatten
    if (defaults.size == fieldTypes.size) {
      Some(Tuple(defaults))
    } else {
      None
    }
  }
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

case class ProcedureType(inTypes : List[Type], outTypes: List[Type]) extends Type {
  override def toString =
    "procedure (" + Utils.join(inTypes.map(_.toString), ", ") + ") returns " +
        "(" + Utils.join(outTypes.map(_.toString), ", ") + ")"
}
case class ArrayType(inTypes: List[Type], outType: Type) extends Type {
  override def toString = "[" + Utils.join(inTypes.map(_.toString), " * ") + "]" + outType.toString
  override def isArray = true
}
case class SynonymType(id: Identifier) extends Type {
  override def toString = id.toString
  override def equals(other: Any) = other match {
    case that: SynonymType => that.id.name == this.id.name
    case _ => false
  }
}
case class ExternalType(moduleId : Identifier, typeId : Identifier) extends Type {
  override def toString = moduleId.toString + "." + typeId.toString
}

case class ModuleInstanceType(args : List[(Identifier, Option[Type])]) extends Type {
  lazy val argMap = args.map(a => (a._1 -> a._2)).toMap
  def argToString(arg : (Identifier, Option[Type])) : String = {
    val id = arg._1
    arg._2 match {
      case Some(t) => id.toString + " : (" + t.toString + ")"
      case None => id.toString + " : ()"
    }
  }
  override def toString = "(" + Utils.join(args.map(argToString(_)), ", ") + ")"
}
case class ModuleType(
    inputs: List[(Identifier, Type)], outputs: List[(Identifier, Type)], sharedVars: List[(Identifier, Type)],
    constLits : List[(Identifier, NumericLit)], constants: List[(Identifier, Type)], variables: List[(Identifier, Type)],
    functions: List[(Identifier, FunctionSig)], instances: List[(Identifier, ModuleType)]) extends Type {

  def argToString(arg: (Identifier, Type)) : String = {
    arg._1.toString + ": (" + arg._2.toString + ")"
  }
  def argsToString(args: List[(Identifier, Type)]) =
    Utils.join(args.map(argToString(_)), ", ")

  lazy val inputMap : Map[Identifier, Type] = inputs.toMap
  lazy val outputMap : Map[Identifier, Type] = outputs.toMap
  lazy val sharedVarMap : Map[Identifier, Type] = sharedVars.toMap
  lazy val argSet = inputs.map(_._1).toSet union outputs.map(_._1).toSet union sharedVars.map(_._1).toSet
  lazy val constLitMap : Map[Identifier, NumericLit] = constLits.toMap
  lazy val constantMap : Map[Identifier, Type] = constants.map(a => (a._1 -> a._2)).toMap
  lazy val varMap : Map[Identifier, Type] = variables.map(a => (a._1 -> a._2)).toMap
  lazy val funcMap : Map[Identifier, FunctionSig] = functions.map(a => (a._1 -> a._2)).toMap
  lazy val instanceMap : Map[Identifier, ModuleType] = instances.map(a => (a._1 -> a._2)).toMap
  lazy val typeMap : Map[Identifier, Type] = inputMap ++ outputMap ++ constantMap ++ varMap ++ funcMap.map(f => (f._1 -> f._2.typ))  ++ instanceMap
  lazy val externalTypeMap : Map[Identifier, Type] = constantMap ++ funcMap.map(f => (f._1 -> f._2.typ)) ++ constLitMap.map(f => (f._1 -> f._2.typeOf))
  def typeOf(id : Identifier) : Option[Type] = {
    typeMap.get(id)
  }

  override def toString =
    "inputs (" + argsToString(inputs) + ") outputs (" + argsToString(outputs) + ")"
}

/** Havocable entities. */
sealed abstract class HavocableEntity extends ASTNode
case class HavocableId(id : Identifier) extends HavocableEntity {
  override def toString = id.toString()
}
case class HavocableNextId(id : Identifier) extends HavocableEntity {
  override def toString = id.toString()
}
case class HavocableFreshLit(f : FreshLit) extends HavocableEntity {
  override def toString = f.toString()
}

/** Statements **/
sealed abstract class Statement extends ASTNode {
  override def toString = Utils.join(toLines, "\n") + "\n"
  def hasStmtBlock = false
  val isLoop = false
  val hasLoop = false
  val hasCall : Boolean
  def toLines : List[String]
}
case class SkipStmt() extends Statement {
  override def toLines = List("skip; // " + position.toString)
  override val hasCall = false
}
case class AssertStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assert " + e + "; // " + position.toString)
  override val hasCall = false
}
case class AssumeStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assume " + e + "; // " + position.toString)
  override val hasCall = false
}
case class HavocStmt(havocable : HavocableEntity) extends Statement {
  override def toLines = List("havoc " + havocable.toString() + "; // " + position.toString)
  override val hasCall = false
}
case class AssignStmt(lhss: List[Lhs], rhss: List[Expr]) extends Statement {
  override def toLines =
    List(Utils.join(lhss.map (_.toString), ", ") + " = " + Utils.join(rhss.map(_.toString), ", ") + "; // " + position.toString)
  override val hasCall = false
}
case class BlockStmt(vars: List[BlockVarsDecl], stmts: List[Statement]) extends Statement {
  override def hasStmtBlock = true
  override val hasLoop = stmts.exists(st => st.hasLoop)
  override def toLines = { 
    List("{") ++
      vars.map(PrettyPrinter.indent(1) + _.toString()) ++
      stmts.flatMap(_.toLines).map(PrettyPrinter.indent(1) + _) ++
    List("}")
  }
  override val hasCall = stmts.exists(st => st.hasCall)
}
case class IfElseStmt(cond: Expr, ifblock: Statement, elseblock: Statement) extends Statement {
  override def hasStmtBlock = true
  override val hasLoop = ifblock.hasLoop || elseblock.hasLoop
  lazy val lines : List[String] = {
    List("if(%s)".format(cond.toString())) ++
    ifblock.toLines.map(PrettyPrinter.indent(1) + _) ++
    List("else") ++
    elseblock.toLines.map(PrettyPrinter.indent(1) + _)
  }
  override def toLines = lines
  override val hasCall = ifblock.hasCall || elseblock.hasCall
}
case class ForStmt(id: Identifier, typ : Type, range: (Expr,Expr), body: Statement)
  extends Statement
{
  override def hasStmtBlock = true
  override val isLoop = true
  override val hasLoop = true
  override val toLines = {
    val forLine = "for " + id + " in range(" + range._1 +"," + range._2 + ") {  // " + position.toString
    List(forLine) ++ body.toLines.map(PrettyPrinter.indent(1) + _) ++ List("}")
  }
  override val hasCall = body.hasCall
}
case class WhileStmt(cond: Expr, body: Statement, invariants: List[Expr])
  extends Statement
{
  override def hasStmtBlock = true
  override val isLoop = true
  override val hasLoop = true
  override val toLines = {
    val headLine = "while(%s)  // %s".format(cond.toString(), position.toString())
    val invLines = invariants.map(inv => PrettyPrinter.indent(1) + "invariant " + inv.toString() + "; // " + inv.position.toString())
    List(headLine) ++ invLines ++ body.toLines.map(PrettyPrinter.indent(1) + _)
  }
  override val hasCall = body.hasCall
}
case class CaseStmt(body: List[(Expr,Statement)]) extends Statement {
  override def hasStmtBlock = true
  override def toLines = List("case") ++
    body.flatMap{ (i) => List(PrettyPrinter.indent(1) + i._1.toString + " : ") ++ i._2.toLines } ++
    List("esac")
  override val hasCall = body.exists(b => b._2.hasCall)
}
case class ProcedureCallStmt(id: Identifier, callLhss: List[Lhs], args: List[Expr])  extends Statement {
  override def toLines = List("call (" +
    Utils.join(callLhss.map(_.toString), ", ") + ") = " + id + "(" +
    Utils.join(args.map(_.toString), ", ") + ") // " + id.position.toString)
  override val hasCall = true
}
case class ModuleCallStmt(id: Identifier) extends Statement {
  override def toLines = List("next (" + id.toString +")")
  override val hasCall = false
}
case class BlockVarsDecl(ids : List[Identifier], typ : Type) extends ASTNode {
  override def toString = "var " + Utils.join(ids.map(id => id.toString()), ", ") +
                          " : " + typ.toString() + "; // " + typ.position.toString()
}

/**
 * Base class for module and procedure signatures.
 */
sealed abstract class IOSig(inputs: List[(Identifier,Type)], outputs: List[(Identifier,Type)]) extends ASTNode {
  type T = (Identifier,Type)
  lazy val printfn = {(a: T) => a._1.toString + ": " + a._2}
}
/**
 * Module signatures.
 */
case class ModuleSig(inParams: List[(Identifier, Type)], outParams: List[(Identifier, Type)]) extends IOSig(inParams, outParams)
{
  override def toString =
    "inputs (" + Utils.join(inParams.map(printfn(_)), ", ") + ")" +
    " outputs " + "(" + Utils.join(outParams.map(printfn(_)), ", ") + ")"
}
/**
 * Procedure signatures.
 */
case class ProcedureSig(inParams: List[(Identifier,Type)], outParams: List[(Identifier,Type)]) extends IOSig(inParams, outParams)
{
  override def toString =
    "(" + Utils.join(inParams.map(printfn(_)), ", ") + ")" +
    " returns " + "(" + Utils.join(outParams.map(printfn(_)), ", ") + ")"
  lazy val typ = ProcedureType(inParams.map(_._2), outParams.map(_._2))
}
/** Function signatures.
 */
case class FunctionSig(args: List[(Identifier,Type)], retType: Type) extends ASTNode {
  type T = (Identifier,Type)
  val typ = MapType(args.map(_._2), retType)
  val printfn = {(a: T) => a._1.toString + ": " + a._2}
  override def toString =
    "(" + Utils.join(args.map(printfn(_)), ", ") + ")" + ": " + retType
}

sealed abstract class Decl extends ASTNode {
  def declNames : List[Identifier]
  val hashId : Int
}

case class InstanceDecl(instanceId : Identifier, moduleId : Identifier, arguments: List[(Identifier, Option[Expr])], instType : Option[ModuleInstanceType], modType : Option[ModuleType]) extends Decl
{
  override val hashId = 901
  lazy val argMap = arguments.foldLeft(Map.empty[Identifier, Expr]) {
    (acc, arg) => {
      arg._2 match {
        case Some(expr) => acc + (arg._1 -> expr)
        case None => acc
      }
    }
  }
  lazy val inputMap = modType.get.inputs.map({
    p => argMap.get(p._1) match {
      case Some(expr) => Some(p._1, p._2, expr)
      case None => None
    }
  }).flatten
  lazy val sharedVarMap = modType.get.sharedVars.map({ 
    p => argMap.get(p._1) match {
      case Some(expr) => Some(p._1, p._2, expr)
      case None => None
    }
  }).flatten
  lazy val outputMap = modType.get.outputs.map({ 
    p => argMap.get(p._1) match {
      case Some(expr) => Some(p._1, p._2, expr)
      case None => None
    }
  }).flatten

  def argToString(arg : (Identifier, Option[Expr])) = arg._2 match {
    case Some(e) => arg._1.toString + ":" + e.toString
    case None => arg._1.toString + ": ()"
  }
  lazy val argsToString = Utils.join(arguments.map(argToString(_)), ", ")
  override def toString = "instance " + instanceId.toString + " : " + moduleId.toString + "(" + argsToString + "); // " + position.toString
  override def declNames = List(instanceId)
  def instanceType : Type = instType match {
    case None => UndefinedType()
    case Some(instT) => instT
  }
  def moduleType : Type = modType match {
    case None => UndefinedType()
    case Some(modT) => modT
  }
}

sealed abstract class ProcedureVerificationExpr extends ASTNode {
  val expr : Expr
}
case class ProcedureRequiresExpr(e : Expr) extends ProcedureVerificationExpr {
  override val expr = e
  override val toString = "requires " + e.toString()
}
case class ProcedureEnsuresExpr(e : Expr) extends ProcedureVerificationExpr {
  override val expr = e
  override val toString = "ensures " + e.toString()
}
case class ProcedureModifiesExpr(id : Identifier) extends ProcedureVerificationExpr {
  override val expr = id
  override val toString = "modifies " + id.toString
}

case class ProcedureAnnotations(ids : Set[Identifier]) extends ASTNode {
  override val toString = {
    if (ids.size > 0) {
      "[" + Utils.join(ids.map(id => id.toString()).toList, ", ") + "] "
    } else {
      ""
    }
  }
}

case class ProcedureDecl(
    id: Identifier, sig: ProcedureSig, body: Statement,
    requires: List[Expr], ensures: List[Expr], modifies: Set[Identifier],
    annotations : ProcedureAnnotations) extends Decl
{
  override val hashId = 902
  override def toString = {
    val modifiesString = if (modifies.size > 0) {
      PrettyPrinter.indent(2) + "modifies " + Utils.join(modifies.map(_.toString).toList, ", ") + ";\n"
    } else { "" }
    "procedure " + annotations.toString + id + sig + "\n" +
    modifiesString +
    Utils.join(requires.map(PrettyPrinter.indent(2) + "requires " + _.toString + ";\n"), "") +
    Utils.join(ensures.map(PrettyPrinter.indent(2) + "ensures " + _.toString + "; \n"), "") +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  }
  override def declNames = List(id)
  def hasPrePost = requires.size > 0 || ensures.size > 0
  val shouldInline =
    (annotations.ids.contains(Identifier("inline")) && !annotations.ids.contains(Identifier("noinline"))) ||
    (ensures.size == 0)
}
case class TypeDecl(id: Identifier, typ: Type) extends Decl {
  override val hashId = 903
  override def toString = "type " + id + " = " + typ + "; // " + position.toString
  override def declNames = List(id)
}
case class ModuleTypesImportDecl(id : Identifier) extends Decl {
  override val hashId = 904
  override def toString = "type * = %s.*; // %s".format(id.toString(), position.toString())
  override def declNames = List.empty
}
case class StateVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 905
  override def toString = "var " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class InputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 906
  override def toString = "input " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class OutputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 907
  override def toString = "output " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class SharedVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 908
  override def toString = "sharedvar " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString()
  override def declNames = ids
}
/** This is base trait for all entities that are exported from a module. */
sealed abstract trait ModuleExternal {
  def extNames : List[Identifier]
  def extType : Type
}
case class ConstantLitDecl(id : Identifier, lit : NumericLit) extends Decl {
  override val hashId = 909
  override def toString = "const %s = %s; // %s".format(id.toString(), lit.toString(), position.toString())
  override def declNames = List(id)
}
case class ConstantsDecl(ids: List[Identifier], typ: Type) extends Decl with ModuleExternal {
  override val hashId = 910
  override def toString = "const " + Utils.join(ids.map(_.toString), ", ") + ": " + typ + "; // " + position.toString
  override def declNames = ids
  override def extNames = ids
  override def extType = typ
}
case class FunctionDecl(id: Identifier, sig: FunctionSig) extends Decl with ModuleExternal {
  override val hashId = 911
  override def toString = "function " + id + sig + ";  // " + position.toString
  override def declNames = List(id)
  override def extNames = List(id)
  override def extType = sig.typ
}
case class DefineDecl(id: Identifier, sig: FunctionSig, expr: Expr) extends Decl {
  override val hashId = 912
  override def toString = "define %s %s = %s;".format(id.toString, sig.toString, expr.toString)
  override def declNames = List(id)
}

sealed abstract class GrammarTerm extends ASTNode
case class FuncAppTerm(id: Identifier, args: List[GrammarTerm]) extends GrammarTerm {
  override def toString = {
    val argString = Utils.join(args.map(_.toString), ", ")
    "%s(%s)".format(id.toString, argString)
  }
}
case class OpAppTerm(op: Operator, args: List[GrammarTerm]) extends GrammarTerm {
  override def toString = {
    val argStr = args.map(_.toString)
    val str = if (op.fixity == Operator.INFIX) {
      Utils.join(argStr, " " + op.toString + " ")
    } else if(op.fixity == Operator.PREFIX) {
      op.toString + "(" + Utils.join(argStr, ", ") + ")"
    } else {
      "(" + Utils.join(argStr, ", ") + ")" + op.toString
    }
    "(" + str + ")"
  }
}

case class LiteralTerm(lit: Literal) extends GrammarTerm {
  override def toString = lit.toString()
}
case class SymbolTerm(id: Identifier) extends GrammarTerm {
  override def toString = id.toString()
}
case class ConstantTerm(typ: Type) extends GrammarTerm {
  override def toString = "const " + typ.toString()
}
case class ParameterTerm(typ: Type) extends GrammarTerm {
  override def toString = "function input " + typ.toString()
}
// These three terms aren't supported yet.
case class LetVariableTerm(typ: Type) extends GrammarTerm {
  override def toString = "function var " + typ.toString()
}
case class VariableTerm(typ: Type) extends GrammarTerm {
  override def toString = "var " + typ.toString()
}
case class LetTerm(assigns: List[(Identifier, Type, GrammarTerm)], expr: GrammarTerm) extends GrammarTerm {
  override def toString = {
    "let (%s) = (%s) in %s".format(
      Utils.join(assigns.map(a => "(" + a._1.toString + ": " + a._2.toString + ")"), ", "),
      Utils.join(assigns.map(_._3.toString), ", "),
      expr.toString)
  }
}

case class NonTerminal(id: Identifier, typ: Type, terms: List[GrammarTerm]) extends ASTNode {
  override def toString = {
    "(%s : %s) ::= %s;".format(id.toString, typ.toString, Utils.join(terms.map(_.toString), " | "))
  }
}

case class GrammarDecl(id: Identifier, sig: FunctionSig, nonterminals: List[NonTerminal]) extends Decl {
  override val hashId = 913
  override def toString = {
    val argTypes = Utils.join(sig.args.map(a => a._1.toString + ": " + a._2.toString), ", ")
    val header :String = "grammar %s %s = { // %s".format(id.toString, sig.toString(), position.toString)
    val lines = nonterminals.map(PrettyPrinter.indent(2) + _.toString)
    header + "\n" + Utils.join(lines, "\n") + "\n" + PrettyPrinter.indent(1) + "}"
  }
  override def declNames = List(id)
}

case class SynthesisFunctionDecl(id: Identifier, sig: FunctionSig, grammarId : Option[Identifier], grammarArgs: List[Identifier], conditions: List[Expr]) extends Decl {
  override val hashId = 914
  override def toString = "synthesis function " + id + sig + "; //" + position.toString()
  override def declNames = List(id)
}

case class InitDecl(body: Statement) extends Decl {
  override val hashId = 915
  override def toString =
    "init // " + position.toString + "\n" +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  override def declNames = List.empty
}
case class NextDecl(body: Statement) extends Decl {
  override val hashId = 916
  override def toString =
    "next // " + position.toString + "\n" +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  override def declNames = List.empty
}
case class SpecDecl(id: Identifier, expr: Expr, params: List[ExprDecorator]) extends Decl {
  override val hashId = 917
  val propertyKeyword = if (ExprDecorator.isHyperproperty(params)) {
    "hyperproperty"
  } else {
    "property"
  }
  override def toString = {
    val declString = if (params.size > 0) {
      "[" + Utils.join(params.map(_.toString), ", ") + "]"
    } else {
      ""
    }
    "%s %s%s : %s; // %s".format(propertyKeyword, id.toString, declString, expr.toString, position.toString)
  }
  override def declNames = List(id)
  def name = "%s %s".format(propertyKeyword, id.toString())
}


case class AxiomDecl(id : Option[Identifier], expr: Expr) extends Decl {
  override val hashId = 918
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

sealed abstract class ProofCommand extends ASTNode

case class GenericProofCommand(name : Identifier, params: List[Identifier], args : List[(Expr, String)], resultVar: Option[Identifier], argObj: Option[Identifier]) extends ProofCommand {
  def getContext(context : Scope) : Scope = {
    argObj match {
      case Some(arg) =>
        try {
          val mod = context.module.get
          val verifCmd = context.get(arg).get.asInstanceOf[Scope.VerifResultVar].cmd
          if (verifCmd.isVerify) {
            val procName = verifCmd.args(0)._1.asInstanceOf[Identifier]
            val proc = mod.procedures.find(p => p.id == procName).get
            context + proc
          } else {
            context
          }
        } catch {
          // if something goes wrong return context unchanged.
          case e : java.util.NoSuchElementException => context
          case e : scala.ClassCastException => context
        }
      case None => context
    }
  }
  def isVerify : Boolean = { name == Identifier("verify") }
  override def toString = {
    val nameStr = name.toString
    val paramStr = if (params.size > 0) { "[" + Utils.join(params.map(_.toString), ", ") + "]" } else { "" }
    val argStr = if (args.size > 0) { "(" + Utils.join(args.map(_.toString), ", ") + ")" } else { "" }
    val resultStr = resultVar match { case Some(id) => id.toString + " = "; case None => "" }
    val objStr = argObj match { case Some(id) => id.toString + "->"; case None => "" }
    resultStr + objStr + nameStr + paramStr + argStr + ";" + " // " + position.toString
  }
}

sealed abstract class Annotation extends ASTNode
case class InstanceVarMapAnnotation(iMap: Map[List[Identifier], Identifier]) extends Annotation {
  lazy val rMap : Map[Identifier, String] = {
    iMap.map {
      p => {
        p._2 -> Utils.join(p._1.map(id => id.toString()), ".")
      }
    }
  }
  override def toString : String = {
    val start = PrettyPrinter.indent(1) + "// instance_var_map { "
    val lines = iMap.map(p => PrettyPrinter.indent(1) + "//   " + Utils.join(p._1.map(_.toString), ".") + " ::==> " + p._2.toString)
    val end = PrettyPrinter.indent(1) + "// } end_instance_var_map"
    Utils.join(List(start) ++ lines ++ List(end), "\n") +"\n"
  }
}

case class ExprRenameMapAnnotation(renameMap_ : MutableMap[Expr, BigInt]) extends Annotation {
  lazy val renameMap : MutableMap[Expr, BigInt] = renameMap_

  override def toString : String = {
    val start = PrettyPrinter.indent(1) + "// expr_rename_map { "
    val lines = renameMap_.map(p => PrettyPrinter.indent(1) + "//   " + (p._1.toString + " => " + p._2.toString))
    val end = PrettyPrinter.indent(1) + "// } end_expr_rename_map"
    Utils.join(List(start) ++ lines ++ List(end), "\n") +"\n"
  }
}

object Annotation {
  val default = List(InstanceVarMapAnnotation(Map.empty))
  def defaultVars(decls : List[Decl]) : List[Annotation] = {
    val inputs = decls.collect{ case inps : InputVarsDecl => inps.ids }
    val outputs = decls.collect{ case outs : OutputVarsDecl => outs.ids }
    val vars = decls.collect{ case vars : StateVarsDecl => vars.ids }
    val sharedVars = decls.collect{ case sharedVars : SharedVarsDecl => sharedVars.ids }
    def flatten (l : List[List[Identifier]]) : List[Identifier] = l.flatMap(ll => ll)
    val names = flatten(inputs) ++ flatten(outputs) ++ flatten(vars) ++ flatten(sharedVars)
    val instMap = names.map(n => (List(n) -> n)).toMap
    List(InstanceVarMapAnnotation(instMap))
  }
}

case class Module(id: Identifier, decls: List[Decl], cmds : List[GenericProofCommand], notes: List[Annotation]) extends ASTNode {
  // create a new module with with the filename set.
  def withFilename(name : String) : Module = {
    val newModule = Module(id, decls, cmds, notes)
    newModule.filename = Some(name)
    return newModule
  }
  // module inputs.
  lazy val inputs : List[(Identifier, Type)] =
    decls.collect { case inps : InputVarsDecl => inps }.flatMap(i => i.ids.map(id => (id, i.typ)))
  // module outputs.
  lazy val outputs : List[(Identifier, Type)] =
    decls.collect { case outs : OutputVarsDecl => outs }.flatMap(o => o.ids.map(id => (id, o.typ)))
  // module state variables.
  lazy val vars : List[(Identifier, Type)] =
    decls.collect { case vars : StateVarsDecl => vars }.flatMap(v => v.ids.map(id => (id, v.typ)))
  lazy val sharedVars: List[(Identifier, Type)] =
    decls.collect { case sVars : SharedVarsDecl => sVars }.flatMap(sVar => sVar.ids.map(id => (id, sVar.typ)))
  lazy val constLits: List[(Identifier, NumericLit)] =
    decls.collect { case constLit : ConstantLitDecl => (constLit.id, constLit.lit) }
  // module constants.
  lazy val constantDecls = decls.collect { case cnsts : ConstantsDecl => cnsts }
  lazy val constants : List[(Identifier, Type)] =
    constantDecls.flatMap(cnst => cnst.ids.map(id => (id, cnst.typ)))
  // module functions.
  lazy val functions : List[FunctionDecl] =
    decls.filter(_.isInstanceOf[FunctionDecl]).map(_.asInstanceOf[FunctionDecl])
  // module properties.
  lazy val properties : List[SpecDecl] = decls.collect{ case spec : SpecDecl => spec }

  lazy val externalMap : Map[Identifier, ModuleExternal] =
    (functions.map(f => (f.id -> f)) ++ (constantDecls.flatMap(c => c.ids.map(id => (id, c))).map(p => p._1 -> p._2))).toMap

  // module procedures.
  lazy val procedures : List[ProcedureDecl] = decls.filter(_.isInstanceOf[ProcedureDecl]).map(_.asInstanceOf[ProcedureDecl])
  // inlineable procedures.
  lazy val inlineableProcedures : Set[Identifier] = decls.collect{ case p : ProcedureDecl => p.id }.toSet
  // helper method for inlineableProcedures.
  def isInlineableProcedure(id : Identifier) : Boolean = inlineableProcedures.contains(id)
  // module instances of other modules.
  lazy val instances : List[InstanceDecl] = decls.filter(_.isInstanceOf[InstanceDecl]).map(_.asInstanceOf[InstanceDecl])
  // set of instance names (for easy searching.)
  lazy val instanceNames : Set[Identifier] = instances.map(_.instanceId).toSet
  // set of type declarations.
  lazy val typeDeclarationMap : Map[Identifier, Type] = decls.filter(_.isInstanceOf[TypeDecl]).map(_.asInstanceOf[TypeDecl]).map {
    t => (t.id -> t.typ)
  }.toMap

  // compute the "type" of this module.
  lazy val moduleType : ModuleType = ModuleType(
      inputs, outputs, sharedVars,
      constLits, constants, vars,
      functions.map(c => (c.id, c.sig)),
      instances.map(inst => (inst.instanceId, inst.modType.get)))

  // the init block.
  lazy val init : Option[InitDecl] = {
    decls.find(_.isInstanceOf[InitDecl]).flatMap((d) => Some(d.asInstanceOf[InitDecl]))
  }
  // the next block.
  lazy val next : Option[NextDecl] = {
    decls.find(_.isInstanceOf[NextDecl]).flatMap((d) => Some(d.asInstanceOf[NextDecl]))
  }
  // find all axioms.
  lazy val axioms : List[AxiomDecl] = {
    decls.filter(_.isInstanceOf[AxiomDecl]).map(_.asInstanceOf[AxiomDecl])
  }

  // return a specific annotation.
  def getAnnotation[T <: Annotation]()(implicit tag: ClassTag[T]) : Option[T] = {
    val matchingNotes : List[T] = notes.collect { case n : T => n }
    if (matchingNotes.size == 0) {
      None
    } else {
      Utils.assert(matchingNotes.size == 1, "Too many annotations of type: " + tag.toString())
      Some(matchingNotes(0))
    }
  }

  // replace the first occurrence of a specific annotation.
  def withReplacedAnnotation[T <: Annotation](note : T)(implicit tag: ClassTag[T]) : Module = {
    val newNotes : List[Annotation] = notes.map {
      n => {
        n match {
          case nt : T => note
          case _ => n
        }
      }
    }
    Module(id, decls, cmds, newNotes)
  }

  override def toString =
    "\nmodule " + id + " {\n" +
      decls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i + "\n" } +
      PrettyPrinter.indent(1) + "control {" + "\n" +
      cmds.foldLeft("")  { case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" } +
      PrettyPrinter.indent(1) + "}\n" +
      notes.foldLeft("")((acc, i) => acc + i) +
    "}\n"
}
