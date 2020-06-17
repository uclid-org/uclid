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

sealed  trait PositionedNode extends Positional with Hashable {
  var filename : Option[String] = None
  def position = ASTPosition(filename, pos)
  override val hashBaseId = 32575
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
  
  /*
   * Introduced to reference old state variables of an instance.
   */
  def oldInstance(c : OperatorApplication) = OperatorApplication(OldOperator(), List(c))
  def history(c : Identifier, e : Expr) = OperatorApplication(HistoryOperator(), List(c, e))
}
sealed trait Operator extends ASTNode {
  def fixity : Int
  def dumpC = toString()
  def isPolymorphic = false
  def isTemporal = false
  override val hashBaseId = 32400
}
// This is the polymorphic operator type. Typerchecker.rewrite converts these operators
// to either the integer or bitvector versions.
sealed abstract class PolymorphicOperator extends Operator {
  override def isPolymorphic = true
  override def fixity = Operator.INFIX
}
case class LTOp() extends PolymorphicOperator {
  override def toString = "<"
  override val hashId = 1000
  override val md5hashCode = computeMD5Hash
}
case class LEOp() extends PolymorphicOperator {
  override def toString = "<="
  override val hashId = 1001
  override val md5hashCode = computeMD5Hash
}
case class GTOp() extends PolymorphicOperator {
  override def toString = ">"
  override val hashId = 1002
  override val md5hashCode = computeMD5Hash
}
case class GEOp() extends PolymorphicOperator {
  override def toString = ">="
  override val hashId = 1003
  override val md5hashCode = computeMD5Hash
}
case class AddOp() extends PolymorphicOperator {
  override def toString = "+"
  override val hashId = 1004
  override val md5hashCode = computeMD5Hash
}
case class SubOp() extends PolymorphicOperator {
  override def toString = "-"
  override val hashId = 1005
  override val md5hashCode = computeMD5Hash
}
case class MulOp() extends PolymorphicOperator {
  override def toString = "*"
  override val hashId = 1006
  override val md5hashCode = computeMD5Hash
}
case class UnaryMinusOp() extends PolymorphicOperator {
  override def toString = "-"
  override def fixity = Operator.PREFIX
  override val hashId = 1007
  override val md5hashCode = computeMD5Hash
}

// These are operators with integer operators.
sealed abstract class IntArgOperator extends Operator {
  override def fixity = Operator.INFIX
}
case class IntLTOp() extends IntArgOperator {
  override def toString = "<"
  override val hashId = 1100
  override val md5hashCode = computeMD5Hash
}
case class IntLEOp() extends IntArgOperator {
  override def toString = "<="
  override val hashId = 1101
  override val md5hashCode = computeMD5Hash
}
case class IntGTOp() extends IntArgOperator {
  override def toString = ">"
  override val hashId = 1102
  override val md5hashCode = computeMD5Hash
}
case class IntGEOp() extends IntArgOperator {
  override def toString = ">="
  override val hashId = 1103
  override val md5hashCode = computeMD5Hash
}
case class IntAddOp() extends IntArgOperator {
  override def toString ="+"
  override val hashId = 1104
  override val md5hashCode = computeMD5Hash
}
case class IntSubOp() extends IntArgOperator {
  override def toString = "-"
  override val hashId = 1105
  override val md5hashCode = computeMD5Hash
}
case class IntMulOp() extends IntArgOperator {
  override def toString = "*"
  override val hashId = 1106
  override val md5hashCode = computeMD5Hash
}
case class IntUnaryMinusOp() extends IntArgOperator {
  override def toString = "-"
  override def fixity = Operator.PREFIX
  override val hashId = 1107
  override val md5hashCode = computeMD5Hash
}
// These operators take bitvector operands and return bitvector results.
sealed abstract class BVArgOperator(val w : Int) extends Operator {
  override def fixity = Operator.INFIX
  def signed_operands = false
  val arity = 2
}
case class BVLTOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<"
  override def signed_operands = true
  override val hashId = 1200
  override val md5hashCode = computeMD5Hash(w)
}
case class BVLEOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<="
  override def signed_operands = true
  override val hashId = 1201
  override val md5hashCode = computeMD5Hash(w)
}
case class BVGTOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">"
  override def signed_operands = true
  override val hashId = 1202
  override val md5hashCode = computeMD5Hash(w)
}
case class BVGEOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">="
  override def signed_operands = true
  override val hashId = 1203
  override val md5hashCode = computeMD5Hash(w)
}
case class BVLTUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<_u"
  override def dumpC = "<"
  override val hashId = 1204
  override val md5hashCode = computeMD5Hash(w)
}
case class BVLEUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<=_u"
  override def dumpC = "<="
  override val hashId = 1205
  override val md5hashCode = computeMD5Hash(w)
}
case class BVGTUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">_u"
  override def dumpC = ">"
  override val hashId = 1206
  override val md5hashCode = computeMD5Hash(w)
}
case class BVGEUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">=_u"
  override def dumpC = ">="
  override val hashId = 1207
  override val md5hashCode = computeMD5Hash(w)
}
case class BVAddOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "+"
  override val hashId = 1208
  override val md5hashCode = computeMD5Hash(w)
}
case class BVSubOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "-"
  override val hashId = 1209
  override val md5hashCode = computeMD5Hash(w)
}
case class BVMulOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "*"
  override val hashId = 1210
  override val md5hashCode = computeMD5Hash(w)
}
case class BVAndOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "&"
  override val hashId = 1211
  override val md5hashCode = computeMD5Hash(w)
}
case class BVOrOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "|"
  override val hashId = 1212
  override val md5hashCode = computeMD5Hash(w)
}
case class BVXorOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "^"
  override val hashId = 1213
  override val md5hashCode = computeMD5Hash(w)
}
case class BVNotOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "~"
  override val arity = 1
  override val hashId = 1214
  override val md5hashCode = computeMD5Hash(w)
}
case class BVUnaryMinusOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "-"
  override val arity = 1
  override val hashId = 1215
  override val md5hashCode = computeMD5Hash(w)
}
case class BVSignExtOp(override val w : Int, val e : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_sign_extend"
  override val arity = 1
  override val hashId = 1216
  override val md5hashCode = computeMD5Hash(w, e)
}
case class BVZeroExtOp(override val w : Int, val e : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_zero_extend"
  override val arity = 1
  override val hashId = 1217
  override val md5hashCode = computeMD5Hash(w, e)
}

case class BVLeftShiftBVOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_left_shift"
  override def dumpC = "<<"
  override val hashId = 1221
  override val md5hashCode = computeMD5Hash(w)
}
case class BVLRightShiftBVOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_l_right_shift"
  override def dumpC = ">>"
  override val hashId = 1222
  override val md5hashCode = computeMD5Hash(w)
}
case class BVARightShiftBVOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_a_right_shift"
  override def signed_operands = true
  override def dumpC = ">>"
  override val hashId = 1223
  override val md5hashCode = computeMD5Hash(w)
}
case class BVUremOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "%_u"
  override def dumpC = "%"
  override val hashId = 1224
  override val md5hashCode = computeMD5Hash(w)
}
case class BVSremOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "%"
  override def signed_operands = true
  override val hashId = 1225
  override val md5hashCode = computeMD5Hash(w)
}
// Boolean operators.
sealed abstract class BooleanOperator extends Operator {
  override def fixity = Operator.INFIX
  def isQuantified = false
}
case class ConjunctionOp() extends BooleanOperator {
  override def toString = "&&"
  override val hashId = 1300
  override val md5hashCode = computeMD5Hash
}
case class DisjunctionOp() extends BooleanOperator {
  override def toString = "||"
  override val hashId = 1301
  override val md5hashCode = computeMD5Hash
}
case class IffOp() extends BooleanOperator {
  override def toString = "<==>"
  override def dumpC = "=="
  override val hashId = 1302
  override val md5hashCode = computeMD5Hash
}
case class ImplicationOp() extends BooleanOperator {
  override def toString = "==>"
  override val hashId = 1303
  override val md5hashCode = computeMD5Hash
}
case class NegationOp() extends BooleanOperator {
  override def fixity = Operator.PREFIX
  override def toString = "!"
  override val hashId = 1304
  override val md5hashCode = computeMD5Hash
}
// Quantifiers
sealed abstract class QuantifiedBooleanOperator extends BooleanOperator {
  override def fixity = Operator.PREFIX
  override def isQuantified = true
  def variables : List[(Identifier, Type)]
}
object QuantifiedBooleanOperator {
  def toString(quantifier: String, vs: List[(Identifier, Type)], patterns: List[List[Expr]]) = {
    val args = Utils.join(vs.map((v) => v._1.toString + " : " + v._2.toString), ", ")
    val pats = if (patterns.size == 0) { "" } else {
      "pattern[" +
        Utils.join(patterns.map(p => Utils.join(p.map(_.toString()), ", ")), "; ") +
      "] "
    }
    quantifier + " (" + args + ") " + pats + ":: "
  }
}
case class ForallOp(vs : List[(Identifier, Type)], patterns: List[List[Expr]]) extends QuantifiedBooleanOperator {
  override def variables = vs
  override def toString = QuantifiedBooleanOperator.toString("forall", vs, patterns)
  override val hashId = 1400
  override val md5hashCode = computeMD5Hash(vs, patterns)
}
case class ExistsOp(vs: List[(Identifier, Type)], patterns: List[List[Expr]]) extends QuantifiedBooleanOperator {
  override def toString = QuantifiedBooleanOperator.toString("exists", vs, patterns)
  override def variables = vs
  override val hashId = 1401
  override val md5hashCode = computeMD5Hash(vs, patterns)
}

// (In-)equality operators.
sealed abstract class ComparisonOperator() extends Operator {
  override def fixity = Operator.INFIX
}
case class EqualityOp() extends ComparisonOperator {
  override def toString = "=="
  override val hashId = 1500
  override val md5hashCode = computeMD5Hash
}
case class InequalityOp() extends ComparisonOperator {
  override def toString = "!="
  override val hashId = 1501
  override val md5hashCode = computeMD5Hash
}
// BV2Int and Int2BV
case class BV2SignedIntOp() extends Operator {
  override def toString() = "bv_to_signed_int"
  override def fixity = Operator.PREFIX
  override val hashId = 1502
  override val md5hashCode = computeMD5Hash
}
case class BV2UnsignedIntOp() extends Operator {
  override def toString() = "bv_to_unsigned_int"
  override def fixity = Operator.PREFIX
  override val hashId = 1503
  override val md5hashCode = computeMD5Hash
}
// Int2BV
case class Int2BVOp(val w: Int) extends Operator {
  override def toString() = "int_to_bv"
  override def fixity = Operator.PREFIX
  override val hashId = 1504
  override val md5hashCode = computeMD5Hash
}
// LTL Operators
sealed abstract class TemporalOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def isTemporal = true
}
case class GloballyTemporalOp() extends TemporalOperator {
  override def toString = "G"
  override val hashId = 1600
  override val md5hashCode = computeMD5Hash
}
case class NextTemporalOp() extends TemporalOperator {
  override def toString = "X"
  override val hashId = 1601
  override val md5hashCode = computeMD5Hash
}
case class UntilTemporalOp() extends TemporalOperator {
  override def toString = "U"
  override val hashId = 1602
  override val md5hashCode = computeMD5Hash
}
case class FinallyTemporalOp() extends TemporalOperator {
  override def toString = "F"
  override val hashId = 1603
  override val md5hashCode = computeMD5Hash
}
case class ReleaseTemporalOp() extends TemporalOperator {
  override def toString = "R"
  override val hashId = 1604
  override val md5hashCode = computeMD5Hash
}
case class WUntilTemporalOp() extends TemporalOperator {
  override def toString = "W"
  override val hashId = 1605
  override val md5hashCode = computeMD5Hash
}

// "Old" operator.
case class OldOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def toString = "old"
  override val hashId = 1700
  override val md5hashCode = computeMD5Hash
}
case class PastOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def toString = "past"
  override val hashId = 1701
  override val md5hashCode = computeMD5Hash
}
case class HistoryOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def toString = "history"
  override val hashId = 1702
  override val md5hashCode = computeMD5Hash
}
// ITE operator
case class ITEOp() extends Operator {
  override def toString = "ite"
  override def fixity = Operator.PREFIX
  override val hashId = 1703
  override val md5hashCode = computeMD5Hash
}

abstract class BitVectorSlice extends ASTNode {
  def width : Option[Int]
  def isConstantWidth : Boolean
  def dumpC = toString()
}
case class ConstBitVectorSlice(hi: Int, lo: Int) extends BitVectorSlice  {
  Utils.assert(hi >= lo && hi >= 0 && lo >= 0, "Invalid bitvector slice: [" + hi.toString + ":" + lo.toString + "].")
  override def width = Some(hi - lo + 1)
  override def isConstantWidth = true
  override def toString = "[" + hi.toString + ":" + lo.toString + "]"
  override val hashId = 1800
  override val md5hashCode = computeMD5Hash(hi, lo)
}
case class VarBitVectorSlice(hi: Expr, lo: Expr, wd : Option[Int] = None) extends BitVectorSlice {
  override def toString = "[" + hi.toString + ":" + lo.toString + "]"
  override def width = wd
  override def isConstantWidth = wd.isDefined
  override val hashId = 1801
  override val md5hashCode = computeMD5Hash(hi, lo, wd)
}

sealed abstract class ExtractOp extends Operator
case class ConstExtractOp(slice : ConstBitVectorSlice) extends ExtractOp {
  override def toString = slice.toString
  override def fixity = Operator.POSTFIX
  override val hashId = 1900
  override val md5hashCode = computeMD5Hash(slice)
}
case class VarExtractOp(slice : VarBitVectorSlice) extends ExtractOp {
  override def toString = slice.toString()
  override def fixity = Operator.POSTFIX
  override val hashId = 1901
  override val md5hashCode = computeMD5Hash(slice)
}

case class ConcatOp() extends Operator {
  override def toString = "++"
  override def fixity = Operator.INFIX
  override val hashId = 1704
  override val md5hashCode = computeMD5Hash
}
sealed abstract class SelectorOperator extends Operator {
  val ident : Identifier
}
case class PolymorphicSelect(id : Identifier) extends SelectorOperator {
  override val ident = id
  override def toString = "." + id
  override def fixity = Operator.POSTFIX
  override val hashId = 2000
  override val md5hashCode = computeMD5Hash(id)
}
case class RecordSelect(id: Identifier) extends SelectorOperator {
  override val ident = id
  override def toString = "." + id
  override def fixity = Operator.POSTFIX
  override val hashId = 2001
  override val md5hashCode = computeMD5Hash(id)
}
case class SelectFromInstance(varId : Identifier) extends SelectorOperator {
  override val ident = varId
  override def toString = "." + varId
  override def fixity = Operator.INFIX
  override val hashId = 2002
  override val md5hashCode = computeMD5Hash(varId)
}
case class HyperSelect(i: Int) extends Operator {
  override def toString: String = "." + i.toString
  override def fixity = Operator.POSTFIX
  override val hashId = 1705
  override val md5hashCode = computeMD5Hash(i)
}
case class ArraySelect(indices: List[Expr]) extends Operator {
  override def toString = {
    val indexStr = Utils.join(indices.map(_.toString()), ", ")
    "[" + indexStr + "]"
  }
  override def fixity = Operator.POSTFIX
  override val hashId = 1706
  override val md5hashCode = computeMD5Hash(indices)
}
case class ArrayUpdate(indices: List[Expr], value: Expr) extends Operator {
  override def toString: String = {
    val indexStr = Utils.join(indices.map(_.toString()), ", ")
    "[" + indexStr + " -> " + value.toString() + "]"
  }
  override def fixity = Operator.POSTFIX
  override val hashId = 1707
  override val md5hashCode = computeMD5Hash(indices)
}
case class GetNextValueOp() extends Operator {
  override def toString = "'"
  override def fixity = Operator.POSTFIX
  override val hashId = 1708
  override val md5hashCode = computeMD5Hash
}
case class DistinctOp() extends Operator {
  override def toString = "distinct"
  override def fixity = Operator.INFIX
  override val hashId = 1709
  override val md5hashCode = computeMD5Hash
}
sealed abstract class Expr extends ASTNode {
  /** Is this value a statically-defined constant? */
  def isConstant = false
  def isTemporal = false
  def dumpC = toString()
}
sealed abstract class PossiblyTemporalExpr extends Expr

case class Identifier(name : String) extends Expr {
  override def toString = name.toString
  override val hashId = 2100
  override val md5hashCode = computeMD5Hash(name)
}
case class ExternalIdentifier(moduleId : Identifier, id : Identifier) extends Expr {
  override def toString = moduleId.toString + "::" + id.toString
  override val hashId = 2101
  override val md5hashCode = computeMD5Hash(moduleId, id)
}
sealed abstract class Literal extends Expr {
  /** All literals are constants. */
  override def isConstant = true
  def isNumeric = false
}
/** A non-deterministic new constant. */
case class FreshLit(typ : Type) extends Literal {
  override def toString = "*"
  override def dumpC = "nondet()"
  override val hashId = 2200
  override val md5hashCode = computeMD5Hash(typ)
}
sealed abstract class NumericLit extends Literal {
  override def isNumeric = true
  def typeOf : NumericType
  def to (n : NumericLit) : Seq[NumericLit]
  def negate: NumericLit
}
case class BoolLit(value: Boolean) extends Literal {
  override def toString = value.toString
  override val hashId = 2201
  override val md5hashCode = computeMD5Hash(value)
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
  override def negate = IntLit(-value)
  override val hashId = 2300
  override val md5hashCode = computeMD5Hash(value)
}

case class BitVectorLit(value: BigInt, width: Int) extends NumericLit {
  override def toString = value.toString + "bv" + width.toString
  override def dumpC = value.toString
  override def typeOf : NumericType = BitVectorType(width)
  override def to (n : NumericLit) : Seq[NumericLit] = {
    n match {
      case bv : BitVectorLit => (value to bv.value).map(BitVectorLit(_, width))
      case _ => throw new Utils.RuntimeError("Cannot create range for differening types of numeric literals.")
    }
  }
  override def negate = BitVectorLit(-value, width)
  override val hashId = 2301
  override val md5hashCode = computeMD5Hash(value, width)
}

case class StringLit(value: String) extends Literal {
  override def toString = "\"" + value + "\""
  override val hashId = 2202
  override val md5hashCode = computeMD5Hash(value)
}

case class ConstArray(exp: Expr, typ: Type) extends Expr {
  override def toString  = "const(%s, %s)".format(exp.toString(), typ.toString())
  override val hashId = 2102
  override val md5hashCode = computeMD5Hash(exp, typ)
}

case class Tuple(values: List[Expr]) extends Expr {
  override def toString = "{" + Utils.join(values.map(_.toString), ", ") + "}"
  // FIXME: We should not have temporal values inside of a tuple.
  override def isTemporal = false
  override val hashId = 2103
  override val md5hashCode = computeMD5Hash(values)
}
//for symbols interpreted by underlying Theory solvers
case class OperatorApplication(op: Operator, operands: List[Expr]) extends PossiblyTemporalExpr {
  override def isConstant = operands.forall(_.isConstant)
  override def dumpC = {
    op match {
      case PolymorphicSelect(r) =>
        operands(0).dumpC + "." + r.dumpC
      case RecordSelect(r) =>
        operands(0).dumpC + "." + r.dumpC
      case HyperSelect(i) =>
        operands(0).dumpC + "." + i
      case SelectFromInstance(f) =>
        operands(0).dumpC + "." + f.dumpC
      case ForallOp(_, _) | ExistsOp(_, _) =>
        "{" + op.dumpC + operands(0).dumpC + "}"
      case _ =>
        if (op.fixity == Operator.INFIX) {
          "(" + Utils.join(operands.map(_.dumpC), " " + op + " ") + ")"
        } else if (op.fixity == Operator.PREFIX) {
          op + "(" + Utils.join(operands.map(_.dumpC), ", ") + ")"
        } else {
          "(" + Utils.join(operands.map(_.dumpC), ", ") + ")" + op
        }
      }
  }
  override def toString = {
    op match {
      case PolymorphicSelect(r) =>
        operands(0).toString + "." + r.toString
      case RecordSelect(r) =>
        operands(0).toString + "." + r.toString
      case HyperSelect(i) =>
        operands(0).toString + "." + i.toString
      case SelectFromInstance(f) =>
        operands(0).toString + "." + f.toString
      case ForallOp(_, _) | ExistsOp(_, _) =>
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
  override val hashId = 2400
  override val md5hashCode = computeMD5Hash(op, operands)
}
//for uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class FuncApplication(e: Expr, args: List[Expr]) extends Expr {
  override def toString = e + "(" + Utils.join(args.map(_.toString), ", ") + ")"
  override val hashId = 2104
  override val md5hashCode = computeMD5Hash(e, args)
}
case class Lambda(ids: List[(Identifier,Type)], e: Expr) extends Expr {
  override def toString = "Lambda(" + ids + "). " + e
  override val hashId = 2105
  override val md5hashCode = computeMD5Hash(ids, e)
}

sealed abstract class Lhs(val ident: Identifier) extends ASTNode {
  def isProceduralLhs : Boolean
  def dumpC = toString()
}
case class LhsId(id: Identifier) extends Lhs(id) {
  override def toString = id.toString
  override def isProceduralLhs = true
  override val hashId = 2500
  override val md5hashCode = computeMD5Hash(id)
}
case class LhsNextId(id: Identifier) extends Lhs(id) {
  override def toString = id.toString + "'"
  override def isProceduralLhs = false
  override val hashId = 2501
  override val md5hashCode = computeMD5Hash(id)
}
case class LhsArraySelect(id: Identifier, indices: List[Expr]) extends Lhs(id) {
  override def toString = id.toString + "[" + Utils.join(indices.map(_.toString), ", ") + "]"
  override def isProceduralLhs = true
  override val hashId = 2502
  override val md5hashCode = computeMD5Hash(id, indices)
}
case class LhsRecordSelect(id: Identifier, fields: List[Identifier]) extends Lhs(id) {
  override def toString = id.toString + "." + Utils.join(fields.map(_.toString), ".")
  override def isProceduralLhs = true
  override val hashId = 2503
  override val md5hashCode = computeMD5Hash(id, fields)
}
case class LhsSliceSelect(id: Identifier, bitslice : ConstBitVectorSlice) extends Lhs(id) {
  override def toString = id.toString + bitslice.toString
  override def isProceduralLhs = true
  override val hashId = 2504
  override val md5hashCode = computeMD5Hash(id, bitslice)
}
case class LhsVarSliceSelect(id: Identifier, bitslice: VarBitVectorSlice) extends Lhs(id) {
  override def toString = id.toString + bitslice.toString
  override def isProceduralLhs = true
  override val hashId = 2505
  override val md5hashCode = computeMD5Hash(id, bitslice)
}

/** Type decorators for expressions. */
sealed abstract class ExprDecorator extends ASTNode
case class UnknownDecorator(value: String) extends ExprDecorator {
  override def toString = value
  override val hashId = 2600
  override val md5hashCode = computeMD5Hash(value)
}
case object LTLExprDecorator extends ExprDecorator {
  override def toString = "LTL"
  override val hashId = 2601
  override val md5hashCode = computeMD5Hash
}
case class HyperpropertyDecorator(k: Int) extends ExprDecorator {
  override def toString = k.toString()
  override val hashId = 2602
  override val md5hashCode = computeMD5Hash(k)
}
case object LTLSafetyFragmentDecorator extends ExprDecorator {
  override def toString = "LTLSafetyFragment"
  override val hashId = 2603
  override val md5hashCode = computeMD5Hash
}
case object LTLLivenessFragmentDecorator extends ExprDecorator {
  override def toString = "LTLLivenessFragment"
  override val hashId = 2604
  override val md5hashCode = computeMD5Hash
}
case object CoverDecorator extends ExprDecorator {
  override def toString = "cover"
  override val hashId = 2605
  override val md5hashCode = computeMD5Hash
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
  def dumpC = toString()
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
  override val hashId = 2700
  override val md5hashCode = computeMD5Hash
}
/**
 *  Uninterpreted types.
 */
case class UninterpretedType(name: Identifier) extends Type {
  override def toString = name.toString
  override def isUninterpreted = true
  override val hashId = 2701
  override val md5hashCode = computeMD5Hash(name)
}
/**
 * Regular types.
 */
case class BooleanType() extends PrimitiveType {
  override def toString = "boolean"
  override def isBool = true
  override def defaultValue = Some(BoolLit(false))
  override val hashId = 2702
  override val md5hashCode = computeMD5Hash
}
case class IntegerType() extends NumericType {
  override def toString = "integer"
  override def isInt = true
  override def defaultValue = Some(IntLit(0))
  override val hashId = 2703
  override val md5hashCode = computeMD5Hash
  override def dumpC = "int"
}
case class BitVectorType(width: Int) extends NumericType {
  override def toString = "bv" + width.toString
  override def isBitVector = true
  override def dumpC = "__CPROVERbitvec["+ width.toString+"]"
  def isValidSlice(slice : ConstBitVectorSlice) : Boolean = {
    return (slice.lo >= 0 && slice.hi < width)
  }
  override def defaultValue = Some(BitVectorLit(0, width))
  override val hashId = 2704
  override val md5hashCode = computeMD5Hash(width)
}
case class StringType() extends PrimitiveType {
  override def toString = "string"
  override def defaultValue = Some(StringLit(""))
  override val hashId = 2705
  override val md5hashCode = computeMD5Hash
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
  override val hashId = 2706
  override val md5hashCode = computeMD5Hash(ids_)
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
  override val hashId = 2800
  override val md5hashCode = computeMD5Hash(fieldTypes)
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
  override val hashId = 2801
  override val md5hashCode = computeMD5Hash(members)
}
case class MapType(inTypes: List[Type], outType: Type) extends Type {
  override def toString = Utils.join(inTypes.map(_.toString), " * ") + " -> " + outType.toString
  override def isMap = true
  override val hashId = 2707
  override val md5hashCode = computeMD5Hash(inTypes, outType)
}

case class ProcedureType(inTypes : List[Type], outTypes: List[Type]) extends Type {
  override def toString =
    "procedure (" + Utils.join(inTypes.map(_.toString), ", ") + ") returns " +
        "(" + Utils.join(outTypes.map(_.toString), ", ") + ")"
  override val hashId = 2708
  override val md5hashCode = computeMD5Hash(inTypes, outTypes)
}
case class ArrayType(inTypes: List[Type], outType: Type) extends Type {
  override def toString = "[" + Utils.join(inTypes.map(_.toString), " * ") + "]" + outType.toString
  override def isArray = true
  override val hashId = 2709
  override val md5hashCode = computeMD5Hash(inTypes, outType)
}
case class SynonymType(id: Identifier) extends Type {
  override def toString = id.toString
  override def equals(other: Any) = other match {
    case that: SynonymType => that.id.name == this.id.name
    case _ => false
  }
  override val hashId = 2710
  override val md5hashCode = computeMD5Hash(id)
}
case class ExternalType(moduleId : Identifier, typeId : Identifier) extends Type {
  override def toString = moduleId.toString + "." + typeId.toString
  override val hashId = 2711
  override val md5hashCode = computeMD5Hash(moduleId, typeId)
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
  override val hashId = 2712
  override val md5hashCode = computeMD5Hash(args)
}
case class ModuleType(
    inputs: List[(Identifier, Type)], outputs: List[(Identifier, Type)], sharedVars: List[(Identifier, Type)],
    constLits : List[(Identifier, NumericLit)], constants: List[(Identifier, Type)], variables: List[(Identifier, Type)],
    functions: List[(Identifier, FunctionSig)], instances: List[(Identifier, Type)]) extends Type {

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
  lazy val instanceMap : Map[Identifier, Type] = instances.map(a => (a._1 -> a._2)).toMap
  lazy val typeMap : Map[Identifier, Type] = inputMap ++ outputMap ++ constantMap ++ varMap ++ funcMap.map(f => (f._1 -> f._2.typ))  ++ instanceMap
  lazy val externalTypeMap : Map[Identifier, Type] = constantMap ++ funcMap.map(f => (f._1 -> f._2.typ)) ++ constLitMap.map(f => (f._1 -> f._2.typeOf))
  def typeOf(id : Identifier) : Option[Type] = {
    typeMap.get(id)
  }

  override def toString =
    "inputs (" + argsToString(inputs) + ") outputs (" + argsToString(outputs) + ")"
  override val hashId = 2713
  override val md5hashCode = computeMD5Hash(inputs, outputs, sharedVars, constLits, constants, variables, functions, instances)
}

/** Havocable entities. */
sealed abstract class HavocableEntity extends ASTNode
case class HavocableId(id : Identifier) extends HavocableEntity {
  override def toString = id.toString()
  override val hashId = 2900
  override val md5hashCode = computeMD5Hash(id)
}
case class HavocableNextId(id : Identifier) extends HavocableEntity {
  override def toString = id.toString()
  override val hashId = 2901
  override val md5hashCode = computeMD5Hash(id)
}
case class HavocableFreshLit(f : FreshLit) extends HavocableEntity {
  override def toString = f.toString()
  override val hashId = 2902
  override val md5hashCode = computeMD5Hash(f)
}

/* Introduced as an intermediate representation to denote havoc'ing 
 * specific state variables within an instance.
 */
case class HavocableInstanceId(opapp : OperatorApplication) extends HavocableEntity {
  override def toString = opapp.toString()
  override val hashId = 2903
  override val md5hashCode = computeMD5Hash(opapp)
}

/** Statements **/
sealed abstract class Statement extends ASTNode {
  override def toString = Utils.join(toLines, "\n") + "\n"
  def dumpC = Utils.join(toCLines, "\n")+"\n"
  def hasStmtBlock = false
  val isLoop = false
  val hasLoop = false
  val hasCall : Boolean
  val hasInternalCall : Boolean
  def toLines : List[String]
  def toCLines = toLines
}
case class SkipStmt() extends Statement {
  override def toLines = List("skip; // " + position.toString)
  override def toCLines = List("// skip;")
  override val hasCall = false
  override val hasInternalCall = false
  override val hashId = 3000
  override val md5hashCode = computeMD5Hash
}
case class AssertStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assert " + e + "; // " + position.toString)
  override def toCLines = List("assert( " + e + "); // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false
  override val hashId = 3001
  override val md5hashCode = computeMD5Hash(e, id)
}
case class AssumeStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assume " + e + "; // " + position.toString)
  override def toCLines = List("assume (" + e + "); // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false
  override val hashId = 3002
  override val md5hashCode = computeMD5Hash(e, id)
}
case class HavocStmt(havocable : HavocableEntity) extends Statement {
  override def toLines = List("havoc " + havocable.toString() + "; // " + position.toString)
  override def toCLines = List("havoc (" + havocable.toString() + "); // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false;
  override val hashId = 3003
  override val md5hashCode = computeMD5Hash(havocable)
}
case class AssignStmt(lhss: List[Lhs], rhss: List[Expr]) extends Statement {
  override def toLines =
    List(Utils.join(lhss.map (_.toString), ", ") + " = " + Utils.join(rhss.map(_.toString), ", ") + "; // " + position.toString)
  override def toCLines  =
    List(Utils.join(lhss.map (_.dumpC), ", ") + " = " + Utils.join(rhss.map(_.dumpC), ", ") + "; // " + position.toString)  
  override val hasCall = false
  override val hasInternalCall = false
  override val hashId = 3004
  override val md5hashCode = computeMD5Hash(lhss, rhss)
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
  override def toCLines  = {
      vars.map(PrettyPrinter.indent(1) + _.dumpC) ++
      stmts.flatMap(_.toCLines).map(PrettyPrinter.indent(1) + _)
  }

  override val hasCall = stmts.exists(st => st.hasCall)
  override val hasInternalCall = stmts.exists(st => st.hasInternalCall)
  override val hashId = 3005
  override val md5hashCode = computeMD5Hash(vars, stmts)
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
  lazy val clines : List[String] = {
    List("if(%s)".format(cond.toString())) ++
    ifblock.toCLines.map(PrettyPrinter.indent(1) + _) ++
    List("else") ++
    elseblock.toCLines.map(PrettyPrinter.indent(1) + _)
  }
  override def toCLines = clines
  override val hasCall = ifblock.hasCall || elseblock.hasCall
  override val hasInternalCall = ifblock.hasInternalCall || elseblock.hasInternalCall
  override val hashId = 3006
  override val md5hashCode = computeMD5Hash(cond, ifblock, elseblock)
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
    override def toCLines = {
    val forLine = "for " + typ.toString() + id + " in range(" + range._1 +"," + range._2 + ") {  // " + position.toString
    List(forLine) ++ body.toCLines.map(PrettyPrinter.indent(1) + _) ++ List("}")
  }

  override val hasCall = body.hasCall
  override val hasInternalCall = body.hasInternalCall
  override val hashId = 3007
  override val md5hashCode = computeMD5Hash(id, typ, range, body)
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
  override val hasInternalCall = body.hasInternalCall
  override val hashId = 3008
  override val md5hashCode = computeMD5Hash(cond, body, invariants)
}
case class CaseStmt(body: List[(Expr,Statement)]) extends Statement {
  override def hasStmtBlock = true
  override def toLines = List("case") ++
    body.flatMap{ (i) => List(PrettyPrinter.indent(1) + i._1.toString + " : ") ++ i._2.toLines } ++
    List("esac")
  override val hasCall = body.exists(b => b._2.hasCall)
  override val hasInternalCall = body.exists(b => b._2.hasInternalCall)
  override val hashId = 3009
  override val md5hashCode = computeMD5Hash(body)
}
case class ProcedureCallStmt(id: Identifier, callLhss: List[Lhs], args: List[Expr], instanceId : Option[Identifier], moduleId : Option[Identifier]=None)  extends Statement {
  override def toLines = List("call (" +
    Utils.join(callLhss.map(_.toString), ", ") + ") = " + (if (instanceId.isEmpty) "" else (instanceId.get.name + ".")) +  id + "(" +
    Utils.join(args.map(_.toString), ", ") + ") // " + id.position.toString)
  override val hasCall = true
  override val hasInternalCall = instanceId.isEmpty
  override val hashId = 3010
  override val md5hashCode = computeMD5Hash(id, callLhss, args, instanceId)
}
case class ModuleCallStmt(id: Identifier) extends Statement {
  override def toLines = List("next (" + id.toString +")")
  override val hasCall = false
  override val hasInternalCall = false
  override val hashId = 3011
  override val md5hashCode = computeMD5Hash(id)
}
case class BlockVarsDecl(ids : List[Identifier], typ : Type) extends ASTNode {
  override def toString = "var " + Utils.join(ids.map(id => id.toString()), ", ") +
                          " : " + typ.toString() + "; // " + typ.position.toString()
  def dumpC = typ.dumpC + " "+ Utils.join(ids.map(id => id.toString()), ", ") + "; //" + typ.position.toString()                     
  override val hashId = 3100
  override val md5hashCode = computeMD5Hash(ids, typ)
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
  override val hashId = 3200
  override val md5hashCode = computeMD5Hash(inParams, outParams)
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
  override val hashId = 3201
  override val md5hashCode = computeMD5Hash(inParams, outParams)
}
/** Function signatures.
 */
case class FunctionSig(args: List[(Identifier,Type)], retType: Type) extends ASTNode {
  type T = (Identifier,Type)
  val typ = MapType(args.map(_._2), retType)
  val printfn = {(a: T) => a._1.toString + ": " + a._2}
  override def toString =
    "(" + Utils.join(args.map(printfn(_)), ", ") + ")" + ": " + retType
  override val hashId = 3202
  override val md5hashCode = computeMD5Hash(args, retType)
}

sealed abstract class Decl extends ASTNode {
  def declNames : List[Identifier]
  val hashId : Int
  def dumpC = toString()
  def dumpC_assumption = toString()
}

case class InstanceDecl(instanceId : Identifier, moduleId : Identifier, arguments: List[(Identifier, Option[Expr])], instType : Option[ModuleInstanceType], modType : Option[ModuleType]) extends Decl
{
  override val hashId = 3901
  override val md5hashCode = computeMD5Hash(instanceId, moduleId, arguments, instType, modType)
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

/* Modifiable entities. */
/* All modifiable entities found by the parser can only be ModifiableId */
sealed abstract class ModifiableEntity extends ASTNode {
  val expr : Expr
}
  
case class ModifiableId(id : Identifier) extends ModifiableEntity {
  override val expr = id
  override def toString = id.toString()
  override val hashId = 3500
  override val md5hashCode = computeMD5Hash(id)
}

/* 
 * Introduced as an intermediate node in the ASTs to track the state 
 * variables that are modified within an instance.
 */
case class ModifiableInstanceId(opapp : OperatorApplication) extends ModifiableEntity {
  override val expr = opapp
  override def toString = opapp.toString()
  override val hashId = 3501
  override val md5hashCode = computeMD5Hash(opapp)
}

sealed abstract class ProcedureVerificationExpr extends ASTNode {
  val expr : Expr
  def dumpC = toString
}
case class ProcedureRequiresExpr(e : Expr) extends ProcedureVerificationExpr {
  override val expr = e
  override val toString = "requires " + e.toString()
  override val hashId = 3400
  override val md5hashCode = computeMD5Hash(e)
  override val dumpC = "__CPROVER_assume(" + e.toString() + ");\n"
}
case class ProcedureEnsuresExpr(e : Expr) extends ProcedureVerificationExpr {
  override val expr = e
  override val toString = "ensures " + e.toString()
  override val hashId = 3401
  override val md5hashCode = computeMD5Hash(e)
  override val dumpC = "assert(" + e.toString() + ");\n"
}
case class ProcedureModifiesExpr(modifiable : ModifiableEntity) extends ProcedureVerificationExpr {
  override val expr = modifiable.expr
  override val toString = "modifies " + modifiable.toString
  override val hashId = 3402
  override val md5hashCode = computeMD5Hash(modifiable)
  override val dumpC = ""
}

case class ProcedureAnnotations(ids : Set[Identifier]) extends ASTNode {
  override val toString = {
    if (ids.size > 0) {
      "[" + Utils.join(ids.map(id => id.toString()).toList, ", ") + "] "
    } else {
      ""
    }
  }
  override val hashId = 3403
  override val md5hashCode = computeMD5Hash(ids.toList)
}

case class ProcedureDecl(
    id: Identifier, sig: ProcedureSig, body: Statement,
    requires: List[Expr], ensures: List[Expr], modifies: Set[ModifiableEntity],
    annotations : ProcedureAnnotations) extends Decl
{
  override val hashId = 3902
  override val md5hashCode = computeMD5Hash(id, sig, body, requires, ensures, modifies.toList, annotations)
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
  override def dumpC = {
    val declareVars = sig.inParams.foldLeft("")
    {case (acc,i) => acc + PrettyPrinter.indent(1)+ i._2.dumpC + " " + i._1.dumpC + ";\n" + PrettyPrinter.indent(1) + "havoc(" + i._1 + ");\n" }
    val declareOutputVars = sig.outParams.foldLeft("")
        {case (acc,i) => acc + PrettyPrinter.indent(1)+ i._2.dumpC + " " + i._1.dumpC + ";\n" + PrettyPrinter.indent(1) + "havoc(" + i._1 + ");\n" }

    "void " + "verify_"+id + "() {\n" + declareVars + declareOutputVars +
    Utils.join(requires.map(PrettyPrinter.indent(2) + "__CPROVER_assume(" + _.dumpC + ");\n"), "") +
    Utils.join(body.toCLines.map(PrettyPrinter.indent(2) + _), "\n") + "\n" + 
    Utils.join(ensures.map(PrettyPrinter.indent(2) + "assert(" + _.dumpC + "); \n"), "") +
    "}\n"
  }
  override def declNames = List(id)
  def hasPrePost = requires.size > 0 || ensures.size > 0
  val shouldInline =
    (annotations.ids.contains(Identifier("inline")) && !annotations.ids.contains(Identifier("noinline"))) ||
    (ensures.size == 0)
}
case class TypeDecl(id: Identifier, typ: Type) extends Decl {
  override val hashId = 3903
  override val md5hashCode = computeMD5Hash(id, typ)
  override def toString = "type " + id + " = " + typ + "; // " + position.toString
  override def declNames = List(id)
}
case class ModuleTypesImportDecl(id : Identifier) extends Decl {
  override val hashId = 3904
  override val md5hashCode = computeMD5Hash(id)
  override def toString = "type * = %s.*; // %s".format(id.toString(), position.toString())
  override def declNames = List.empty
}
case class StateVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 3905
  override val md5hashCode = computeMD5Hash(ids, typ)
  override def toString = "var " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def dumpC = typ.dumpC +" "+ Utils.join(ids.map(_.toString), ", ") + "; // " + position.toString
  override def declNames = ids
}
case class InputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 3906
  override val md5hashCode = computeMD5Hash(ids, typ)
  override def toString = "input " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class OutputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 3907
  override val md5hashCode = computeMD5Hash(ids, typ)
  override def toString = "output " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class SharedVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override val hashId = 3908
  override val md5hashCode = computeMD5Hash(ids, typ)
  override def toString = "sharedvar " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString()
  override def declNames = ids
}
/** This is base trait for all entities that are exported from a module. */
sealed abstract trait ModuleExternal {
  def extNames : List[Identifier]
  def extType : Type
}
case class ConstantLitDecl(id : Identifier, lit : NumericLit) extends Decl {
  override val hashId = 3909
  override val md5hashCode = computeMD5Hash(id, lit)
  override def toString = "const %s = %s; // %s".format(id.toString(), lit.toString(), position.toString())
  override def declNames = List(id)
}
case class ConstantsDecl(ids: List[Identifier], typ: Type) extends Decl with ModuleExternal {
  override val hashId = 3910
  override val md5hashCode = computeMD5Hash(ids, typ)
  override def toString = "const " + Utils.join(ids.map(_.toString), ", ") + ": " + typ + "; // " + position.toString
  override def declNames = ids
  override def extNames = ids
  override def extType = typ
}
case class ModuleConstantsImportDecl(id: Identifier) extends Decl {
  override val hashId = 3919 
  override val md5hashCode = computeMD5Hash(id)
  override def toString = "const * = %s.*; // %s".format(id.toString, position.toString)
  override def declNames = List.empty
}
case class FunctionDecl(id: Identifier, sig: FunctionSig) extends Decl with ModuleExternal {
  override val hashId = 3911
  override val md5hashCode = computeMD5Hash(id, sig)
  override def toString = "function " + id + sig + ";  // " + position.toString
  override def declNames = List(id)
  override def extNames = List(id)
  override def extType = sig.typ
}
case class ModuleFunctionsImportDecl(id: Identifier) extends Decl {
  override val hashId = 3920
  override val md5hashCode = computeMD5Hash(id)
  override def toString = "function * = %s.*; // %s".format(id.toString, position.toString)
  override def declNames = List.empty
}
case class DefineDecl(id: Identifier, sig: FunctionSig, expr: Expr) extends Decl {
  override val hashId = 3912
  override val md5hashCode = computeMD5Hash(id, sig, expr)
  override def toString = "define %s %s = %s;".format(id.toString, sig.toString, expr.toString)
  override def declNames = List(id)
}
case class ModuleDefinesImportDecl(id: Identifier) extends Decl {
  override val hashId = 3921
  override val md5hashCode = computeMD5Hash(id)
  override def toString = "define * = $s.*; // %s".format(id.toString)
  override def declNames = List.empty
}

sealed abstract class GrammarTerm extends ASTNode
case class FuncAppTerm(id: Identifier, args: List[GrammarTerm]) extends GrammarTerm {
  override def toString = {
    val argString = Utils.join(args.map(_.toString), ", ")
    "%s(%s)".format(id.toString, argString)
  }
  override val hashId = 4000
  override val md5hashCode = computeMD5Hash(id, args)
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
  override val hashId = 4001
  override val md5hashCode = computeMD5Hash(op)
}

case class LiteralTerm(lit: Literal) extends GrammarTerm {
  override def toString = lit.toString()
  override val hashId = 4002
  override val md5hashCode = computeMD5Hash(lit)
}
case class SymbolTerm(id: Identifier) extends GrammarTerm {
  override def toString = id.toString()
  override val hashId = 4003
  override val md5hashCode = computeMD5Hash(id)
}
case class ConstantTerm(typ: Type) extends GrammarTerm {
  override def toString = "const " + typ.toString()
  override val hashId = 4004
  override val md5hashCode = computeMD5Hash(typ)
}
case class ParameterTerm(typ: Type) extends GrammarTerm {
  override def toString = "function input " + typ.toString()
  override val hashId = 4005
  override val md5hashCode = computeMD5Hash(typ)
}
// These three terms aren't supported yet.
case class LetVariableTerm(typ: Type) extends GrammarTerm {
  override def toString = "function var " + typ.toString()
  override val hashId = 4006
  override val md5hashCode = computeMD5Hash(typ)
}
case class VariableTerm(typ: Type) extends GrammarTerm {
  override def toString = "var " + typ.toString()
  def dumpC = typ.dumpC + " "
  override val hashId = 4007
  override val md5hashCode = computeMD5Hash(typ)
}
case class LetTerm(assigns: List[(Identifier, Type, GrammarTerm)], expr: GrammarTerm) extends GrammarTerm {
  override def toString = {
    "let (%s) = (%s) in %s".format(
      Utils.join(assigns.map(a => "(" + a._1.toString + ": " + a._2.toString + ")"), ", "),
      Utils.join(assigns.map(_._3.toString), ", "),
      expr.toString)
  }
  override val hashId = 4008
  override val md5hashCode = computeMD5Hash(assigns, expr)
}

case class NonTerminal(id: Identifier, typ: Type, terms: List[GrammarTerm]) extends ASTNode {
  override def toString = {
    "(%s : %s) ::= %s;".format(id.toString, typ.toString, Utils.join(terms.map(_.toString), " | "))
  }
  override val hashId = 4100
  override val md5hashCode = computeMD5Hash(id, typ, terms)
}

case class GrammarDecl(id: Identifier, sig: FunctionSig, nonterminals: List[NonTerminal]) extends Decl {
  override val hashId = 3913
  override val md5hashCode = computeMD5Hash(id, sig, nonterminals)
  override def toString = {
    val argTypes = Utils.join(sig.args.map(a => a._1.toString + ": " + a._2.toString), ", ")
    val header :String = "grammar %s %s = { // %s".format(id.toString, sig.toString(), position.toString)
    val lines = nonterminals.map(PrettyPrinter.indent(2) + _.toString)
    header + "\n" + Utils.join(lines, "\n") + "\n" + PrettyPrinter.indent(1) + "}"
  }
  override def declNames = List(id)
}

case class SynthesisFunctionDecl(id: Identifier, sig: FunctionSig, grammarId : Option[Identifier], grammarArgs: List[Identifier], conditions: List[Expr]) extends Decl {
  override val hashId = 3914
  override val md5hashCode = computeMD5Hash(id, sig, grammarId, grammarArgs, conditions)
  override def toString = "synthesis function " + id + sig + "; //" + position.toString()
  override def declNames = List(id)
}

case class InitDecl(body: Statement) extends Decl {
  override val hashId = 3915
  override val md5hashCode = computeMD5Hash(body)
  override def toString =
    "init // " + position.toString + "\n" +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  override def dumpC =
    Utils.join(body.toCLines.map(PrettyPrinter.indent(2) + _), "\n")  
  override def declNames = List.empty
}
case class NextDecl(body: Statement) extends Decl {
  override val hashId = 3916
  override val md5hashCode = computeMD5Hash(body)
  override def toString =
    "next // " + position.toString + "\n" +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  override def dumpC =  
    Utils.join(body.toCLines.map(PrettyPrinter.indent(2) + _), "\n") 
    

  override def declNames = List.empty
}
case class SpecDecl(id: Identifier, expr: Expr, params: List[ExprDecorator]) extends Decl {
  override val hashId = 3917
  override val md5hashCode = computeMD5Hash(id, expr, params)
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
  override def dumpC = "assert("+ expr.dumpC + ");\n"
  override def dumpC_assumption = "__CPROVER_assume("+expr.dumpC +");\n"
  override def declNames = List(id)
  def name = "%s %s".format(propertyKeyword, id.toString())
}


case class AxiomDecl(id : Option[Identifier], expr: Expr, params: List[ExprDecorator]) extends Decl {
  override val hashId = 3918
  override val md5hashCode = computeMD5Hash(id, expr, params)
  override def toString = {
    id match {
      case Some(id) => "axiom " + id.toString + " : " + expr.toString()
      case None => "axiom " + expr.toString
    }
  }
  override def dumpC = {
     id match {
      case Some(id) => "__CPROVER_assume(" + id.dumpC + " : " + expr.dumpC +");\n"
      case None => "__CPROVER_assume( " + expr.dumpC + ");\n"
     }
  }
  override def declNames = id match {
    case Some(i) => List(i)
    case _ => List.empty
  }
}

sealed abstract class ProofCommand extends ASTNode
case class CommandParams(name: Identifier, values: List[Expr]) extends ASTNode
{
  val hashId = 4201
  override val md5hashCode = computeMD5Hash(name, values)
  override def toString = {
    name.toString + " = (" + Utils.join(values.map(_.toString()), ", ") + "); "
  }
}

case class GenericProofCommand(
    name : Identifier, params: List[CommandParams], args : List[(Expr, String)], 
    resultVar: Option[Identifier], argObj: Option[Identifier]) 
  extends ProofCommand {

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

  def dumpC = {
    name match{
      case Identifier("verify") => ""// do nothing here. 
      case Identifier("induction") => 
      "void induction(void){\nhavoc_all();\n" + 
      PrettyPrinter.indent(1) + "init();\n" + 
      PrettyPrinter.indent(1) + "assert_properties();\n" +
      PrettyPrinter.indent(1) + "havoc_all();\nassume_properties();\n" + 
      PrettyPrinter.indent(1) + "next();\n" + 
      PrettyPrinter.indent(1) + "assert_properties();\n" +
      "}\n"; 
      case Identifier("unroll")=>
      val iterations=args(0)._2;
      "void unroll(void){\nhavoc_all();\n" +
      PrettyPrinter.indent(1) + "init();\n" + 
      PrettyPrinter.indent(1) + "assert_properties();\n" +
      PrettyPrinter.indent(1) + "for(int i=0; i<" + iterations+ " ;i++){\n" +
      PrettyPrinter.indent(2) + "next();\n" + 
      PrettyPrinter.indent(2) + "assert_properties();\n" +
      PrettyPrinter.indent(1) + "}\n" +
      "}\n"
      case Identifier("bmc")=>"unroll: not able to dump C for LTL properties"
      case Identifier("check") | Identifier("print_results") |Identifier("print_cex") | Identifier("dump_c") | Identifier("print_module")  =>""
      case _ => "not able to dump C for this property"
    }
  }
  override val hashId = 4200
  override val md5hashCode = computeMD5Hash(name, params, args, resultVar, argObj)
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
  override val hashId = 4300
  override val md5hashCode = computeMD5Hash(iMap.toList)
}

case class InstanceProcMapAnnotation(iMap: Map[List[Identifier], ProcedureDecl]) extends Annotation {
  override def toString : String = {
    val start = PrettyPrinter.indent(1) + "// instance_proc_map { "
    val lines = iMap.map(p => PrettyPrinter.indent(1) + "//   " + Utils.join(p._1.map(_.toString), ".") + " ::==> " + p._2.toString)
    val end = PrettyPrinter.indent(1) + "// } end_instance_proc_map"
    Utils.join(List(start) ++ lines ++ List(end), "\n") +"\n"
  }
  override val hashId = 4302
  override val md5hashCode = computeMD5Hash(iMap.toList)
}

case class ExprRenameMapAnnotation(renameMap_ : MutableMap[Expr, BigInt], enumVarTypeMap_ : MutableMap[Identifier, Type], enumTypeRangeMap_ : MutableMap[Type, (BigInt, BigInt)]) extends Annotation {
  lazy val enumVarTypeMap : MutableMap[Identifier, Type] = enumVarTypeMap_
  lazy val enumTypeRangeMap : MutableMap[Type, (BigInt, BigInt)] = enumTypeRangeMap_
  lazy val renameMap : MutableMap[Expr, BigInt] = renameMap_
  lazy val bvSize : Int = math.ceil(math.log(renameMap_.size)/math.log(2.0)).toInt + 1

  override def toString : String = {
    val start = PrettyPrinter.indent(1) + "// expr_rename_map { "
    val lines = renameMap_.map(p => PrettyPrinter.indent(1) + "//   " + (p._1.toString + " => " + p._2.toString))
    val end = PrettyPrinter.indent(1) + "// } end_expr_rename_map"
    Utils.join(List(start) ++ lines ++ List(end), "\n") +"\n"
  }
  override val hashId = 4301
  override val md5hashCode = computeMD5Hash(renameMap_.toList, enumVarTypeMap_.toList)
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
  lazy val constImportDecls : List[ModuleConstantsImportDecl]  = decls.collect { case imp : ModuleConstantsImportDecl => imp }

  lazy val constants : List[(Identifier, Type)] =
    constantDecls.flatMap(cnst => cnst.ids.map(id => (id, cnst.typ)))
  
  lazy val funcImportDecls : List[ModuleFunctionsImportDecl] = decls.collect {
  case imp : ModuleFunctionsImportDecl => imp }
  
  // module functions.
  lazy val functions : List[FunctionDecl] =
    decls.filter(_.isInstanceOf[FunctionDecl]).map(_.asInstanceOf[FunctionDecl])
  
  // module macros
  lazy val defines : List[DefineDecl] = decls.collect{ case d : DefineDecl => d }
  lazy val synthFunctions: List[SynthesisFunctionDecl] =
    decls.filter(_.isInstanceOf[SynthesisFunctionDecl]).map(_.asInstanceOf[SynthesisFunctionDecl])
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
      instances.map(inst => (inst.instanceId, inst.moduleType)))

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
    val oldNoteOption = getAnnotation[T]
    val newNotes : List[Annotation] = oldNoteOption match {
      case None => notes :+ note
      case Some(oldNote) => notes.map {
        n => {
          n match {
            case nt : T => note
            case _ => n
          }
        }
      }
    }
    Module(id, decls, cmds, newNotes)
  }



  def dumpC = 
  {
    lazy val varDecls = decls.filter(_.isInstanceOf[StateVarsDecl])
    lazy val initDecl = decls.filter(_.isInstanceOf[InitDecl])
    lazy val nextDecl = decls.filter(_.isInstanceOf[NextDecl])
    lazy val procedureDecls = decls.filter(_.isInstanceOf[ProcedureDecl])
    lazy val propertyDecls = decls.filter(_.isInstanceOf[SpecDecl])
    var cmdCalls : String  = ""

    val havoc = 
    "void havoc_all(){\n" +
    varDecls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + 
      i.declNames.foldLeft("") {case (acc, i) => acc + PrettyPrinter.indent(1) + "__CPROVER_havoc(" + i.dumpC + ");\n" }} +
    "}\n"
    val assert_property = 
    "void assert_properties(){\n"+
    propertyDecls.foldLeft(""){case (acc,i) => acc + PrettyPrinter.indent(1) + i.dumpC + "\n" } + "}\n"

    val assume_property = 
    "void assume_properties(){\n"+
    propertyDecls.foldLeft(""){case (acc,i) => acc + PrettyPrinter.indent(1) + i.dumpC_assumption + "\n" } + "}\n"

    def getCmdString(cmd: GenericProofCommand):String = {
      cmd.name match {
         case Identifier("verify") => cmdCalls += "verify_"+cmd.args(0)._2 + "();\n"
         case Identifier("unroll") => cmdCalls += "unroll();\n";
         case Identifier("induction") => cmdCalls += "induction();\n"
         case _ => // do nothing
      }
      cmd.dumpC
    }


  "// C code generated by UCLID5 \n"+
  "// global variables \n" + 
  varDecls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i.dumpC + "\n" } + "\n"+
  havoc + assert_property + assume_property + 
  "void init()" + "{\n" +
  initDecl.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i.dumpC + "\n" } + 
  "}\n\nvoid next()"+"{\n" +
  nextDecl.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i.dumpC + "\n" } + 
  "}\n" +
  procedureDecls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i.dumpC + "\n" } +
  PrettyPrinter.indent(1) + "\n" + 
  cmds.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + getCmdString(i) } + 
  "\nvoid main() {\n" +  
  PrettyPrinter.indent(1) + cmdCalls + "\n}\n"
  }


  override def toString =
    "\nmodule " + id + " {\n" +
      decls.foldLeft("") { case (acc,i) => acc + PrettyPrinter.indent(1) + i + "\n" } +
      PrettyPrinter.indent(1) + "control {" + "\n" +
      cmds.foldLeft("")  { case (acc,i) => acc + PrettyPrinter.indent(2) + i + "\n" } +
      PrettyPrinter.indent(1) + "}\n" +
      notes.foldLeft("")((acc, i) => acc + i) +
    "}\n"
  override val hashId = 5000
  override val md5hashCode = computeMD5Hash(id, decls, cmds, notes)
}
