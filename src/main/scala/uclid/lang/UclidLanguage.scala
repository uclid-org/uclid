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
import uclid.smt.SynonymMap
import uclid.smt.Converter

object PrettyPrinter
{
  val indentSeq = "  "
  def indent(n : Int) = indentSeq * n
}

/**
 * UclidLang type synonyms map mirroring the typeMap in SMTLIB2Base
 */
case class UclidSynonymMap(fwdMap: Map[String, Type], val revMap: Map[Type, SynonymType]) {
  def addSynonym(name: String, typ: Type) = {
    UclidSynonymMap(fwdMap + (name -> typ), revMap + (typ -> SynonymType(Identifier(name))))
  }
  def get(name: String) : Option[Type] = fwdMap.get(name)
  def get(typ: Type) : Option[SynonymType] = revMap.get(typ)
  def contains(name: String) : Boolean = fwdMap.contains(name)
  def contains(typ: Type) : Boolean = revMap.contains(typ)
}
object UclidSynonymMap {
  def empty = UclidSynonymMap(Map.empty, Map.empty)
}
/** 
 * This is allows types/other contextual information to be propagated
 * to UclidLang from sources such as counterexamples
 */
object ULContext {
  /** Original synonym map from the input ucl file */
  var origTypeMap = UclidSynonymMap.empty
  // * Has side effects, updates origTypeMap
  def addSynonym(name: String, typ: Type) = {
    origTypeMap = origTypeMap.addSynonym(name, typ)
  }
  /** Post-SMT typeMap reconstructed from SMT query/counterexample */
  var postTypeMap = UclidSynonymMap.empty
  // * Has side effects, updates postTypeMap
  def extractPostTypeMap(typeMap_ : SynonymMap) : Unit = {
    postTypeMap = UclidSynonymMap(
      typeMap_.fwdMap.map({
        case (s, typ) => (s, Converter.smtToType(typ))
      }),
      typeMap_.revMap.map({
        case (typ, s) => (Converter.smtToType(typ), SynonymType(Identifier(s.name)))
      })
    )
  }
  def checkEnum(id : Identifier) : Boolean = {
    val enumTypes = origTypeMap.fwdMap.map(_._2) flatMap {
      case e : EnumType => Some(e)
      case _ => None
    }
    enumTypes.exists(e => e.ids.contains(id))
  }
  def checkField(id : Identifier) : Boolean = {
    val recordTypes = origTypeMap.fwdMap.map(_._2) flatMap {
      case r : RecordType => Some(r)
      case _ => None
    }
    recordTypes.exists(r => r.fields.map(_._1).contains(id))
  }
  def checkUninterpretedField(id : Identifier) : Boolean = {
    val uninterpretedTypes = origTypeMap.fwdMap.map(_._2) flatMap {
      case r : UninterpretedType => Some(r)
      case _ => None
    }
    val identifierName = id.toString() // utype!val!0
    val index = identifierName.indexOf("!") // 6
    val typeName = identifierName.substring(0,index) //utype
    val tempIdentifier = Identifier(typeName) // identifer named "utype"
    uninterpretedTypes.exists(r => r.name.equals(tempIdentifier))
   }

  // Performs smt_synonym_name -> lang.Type -> uclid_synonym_name conversion
  def smtToLangSynonym(name : String) : Option[Type] = {
    postTypeMap.get(name) match {
      case Some(t) => origTypeMap.get(t)
      case None => None
    }
  }
  def stripMkTupleFunction(id: String) : Option[String] = {
    id.startsWith("_make_") match {
      case true => Some(id.drop(6))
      case false => None
    }
  }
  def stripFieldName(field: String) : Option[String] = {
    field.startsWith("_field_") match {
      case true => Some(field.drop(7))
      case false => None
    }
  }
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

sealed trait PositionedNode extends Positional {
  var filename : Option[String] = None
  def position = ASTPosition(filename, pos)
}

object ASTNode {
  def introducePos[T <: PositionedNode](setPosition : Boolean, setFilename : Boolean, node : T, pos : ASTPosition) : T = {
    if (setPosition || node.pos.line == 0) {
      val nodeP = node
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
          val nP = n
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
        val nP = n
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
sealed trait ASTNode extends PositionedNode {
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
  def isPolymorphic = false
  def isTemporal = false

  def codegenUclidLang : Option[Operator] = None
}
// This is the polymorphic operator type. Typerchecker.rewrite converts these operators
// to either the integer or bitvector versions.
sealed abstract class PolymorphicOperator extends Operator {
  override def isPolymorphic = true
  override def fixity = Operator.INFIX
}
case class LTOp() extends PolymorphicOperator {
  override def toString = "<"
}
case class LEOp() extends PolymorphicOperator {
  override def toString = "<="
}
case class GTOp() extends PolymorphicOperator {
  override def toString = ">"
}
case class GEOp() extends PolymorphicOperator {
  override def toString = ">="
}
case class AddOp() extends PolymorphicOperator {
  override def toString = "+"
}
case class SubOp() extends PolymorphicOperator {
  override def toString = "-"
}
case class MulOp() extends PolymorphicOperator {
  override def toString = "*"
}
case class UnaryMinusOp() extends PolymorphicOperator {
  override def toString = "-"
  override def fixity = Operator.PREFIX
}
case class DivOp() extends PolymorphicOperator {
  override def toString = "/"
}

// These are operators with integer operators.
sealed abstract class IntArgOperator extends Operator {
  override def fixity = Operator.INFIX
  override def codegenUclidLang: Option[Operator] = Some(this)
}
case class IntLTOp() extends IntArgOperator {
  override def toString = "<"
}
case class IntLEOp() extends IntArgOperator {
  override def toString = "<="
}
case class IntGTOp() extends IntArgOperator {
  override def toString = ">"
}
case class IntGEOp() extends IntArgOperator {
  override def toString = ">="
}
case class IntAddOp() extends IntArgOperator {
  override def toString ="+"
}
case class IntSubOp() extends IntArgOperator {
  override def toString = "-"
}
case class IntMulOp() extends IntArgOperator {
  override def toString = "*"
}
case class IntUnaryMinusOp() extends IntArgOperator {
  override def toString = "-"
  override def fixity = Operator.PREFIX
}
case class IntDivOp() extends IntArgOperator {
  override def toString = "/"
}

// These are operators with real operators.
sealed abstract class RealArgOperator extends Operator {
  override def fixity = Operator.INFIX
  override def codegenUclidLang: Option[Operator] = Some(this)
}
case class RealLTOp() extends RealArgOperator {
  override def toString = "<"
}
case class RealLEOp() extends RealArgOperator {
  override def toString = "<="
}
case class RealGTOp() extends RealArgOperator {
  override def toString = ">"
}
case class RealGEOp() extends RealArgOperator {
  override def toString = ">="
}
case class RealAddOp() extends RealArgOperator {
  override def toString ="+"
}
case class RealSubOp() extends RealArgOperator {
  override def toString = "-"
}
case class RealMulOp() extends RealArgOperator {
  override def toString = "*"
}
case class RealUnaryMinusOp() extends RealArgOperator {
  override def toString = "-"
  override def fixity = Operator.PREFIX
}
case class RealDivOp() extends RealArgOperator {
  override def toString = "/"
}

// These operators take float operands and return float results.
sealed abstract class FloatArgOperator(val e : Int, val s: Int) extends Operator {
  override def fixity = Operator.INFIX
  // default rounding is roundNearestTiesToEven. If we want to support more rounding, we add it here
  val arity = 2
}
case class FPLTOp(override val e: Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = "<"
}
case class FPGTOp(override val e: Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = ">"
}
case class FPLEOp(override val e: Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = "<="
}
case class FPGEOp(override val e : Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = ">="
}
case class FPSubOp(override val e : Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = "-"
}
case class FPAddOp(override val e : Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = "+"
}
case class FPMulOp(override val e : Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = "*"
}
case class FPDivOp(override val e : Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = "/"
}
case class FPIsNanOp(override val e : Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def toString = "isNaN"
  override val arity = 1
}
case class FPUnaryMinusOp(override val e : Int, override val s: Int) extends FloatArgOperator(e,s) {
  override def fixity = Operator.PREFIX
  override def toString = "-"
  override val arity = 1
}

// These operators take bitvector operands and return bitvector results.
sealed abstract class BVArgOperator(val w : Int) extends Operator {
  override def fixity = Operator.INFIX
  val arity = 2
  override def codegenUclidLang: Option[Operator] = Some(this)
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
case class BVLTUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<_u"
}
case class BVLEUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "<=_u"
}
case class BVGTUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">_u"
}
case class BVGEUOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = ">=_u"
}
case class BVAddOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "+"
}
case class BVSubOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "-"
}
case class BVMulOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "*"
}
case class BVDivOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "/"
}
case class BVUDivOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "/_u"
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

case class BVLeftShiftBVOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_left_shift"
}
case class BVLRightShiftBVOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_l_right_shift"
}
case class BVARightShiftBVOp(override val w : Int) extends BVArgOperator(w) {
  override def fixity = Operator.PREFIX
  override def toString = "bv_a_right_shift"
}
case class BVUremOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "%_u"
}
case class BVSremOp(override val w : Int) extends BVArgOperator(w) {
  override def toString = "%"
}
// Boolean operators.
sealed abstract class BooleanOperator extends Operator {
  override def fixity = Operator.INFIX
  def isQuantified = false
  override def codegenUclidLang: Option[Operator] = Some(this)
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
  override def codegenUclidLang: Option[Operator] = None
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
}
case class ExistsOp(vs: List[(Identifier, Type)], patterns: List[List[Expr]]) extends QuantifiedBooleanOperator {
  override def toString = QuantifiedBooleanOperator.toString("exists", vs, patterns)
  override def variables = vs
}

case class FiniteForallOp(id : (Identifier, Type), groupId : Identifier) extends QuantifiedBooleanOperator {
  override def variables = List.empty
  override def toString = "finite_forall %s : %s in %s".format(id._1, id._2, groupId)
}
case class FiniteExistsOp(id : (Identifier, Type), groupId : Identifier) extends QuantifiedBooleanOperator {
  override def toString = "finite_exists %s : %s in %s".format(id._1, id._2, groupId)
  override def variables = List.empty
}

// (In-)equality operators.
sealed abstract class ComparisonOperator() extends Operator {
  override def fixity = Operator.INFIX
}
case class EqualityOp() extends ComparisonOperator {
  override def toString = "=="
  override def codegenUclidLang: Option[Operator] = Some(this)
}
case class InequalityOp() extends ComparisonOperator {
  override def toString = "!="
}
// BV2Int and Int2BV
case class BV2SignedIntOp() extends Operator {
  override def toString() = "bv_to_signed_int"
  override def fixity = Operator.PREFIX
}
case class BV2UnsignedIntOp() extends Operator {
  override def toString() = "bv_to_unsigned_int"
  override def fixity = Operator.PREFIX
}
// Int2BV
case class Int2BVOp(val w: Int) extends Operator {
  override def toString() = "int_to_bv"
  override def fixity = Operator.PREFIX
}
// LTL Operators
sealed abstract class TemporalOperator() extends Operator {
  override def fixity = Operator.PREFIX
  override def isTemporal = true
}
case class GloballyTemporalOp() extends TemporalOperator {
  override def toString = "G"
}
case class NextTemporalOp() extends TemporalOperator {
  override def toString = "X"
}
case class UntilTemporalOp() extends TemporalOperator {
  override def toString = "U"
}
case class FinallyTemporalOp() extends TemporalOperator {
  override def toString = "F"
}
case class ReleaseTemporalOp() extends TemporalOperator {
  override def toString = "R"
}
case class WUntilTemporalOp() extends TemporalOperator {
  override def toString = "W"
}

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
  override def codegenUclidLang: Option[Operator] = Some(this)
}
sealed abstract class SelectorOperator extends Operator {
  val ident : Identifier
}
case class PolymorphicSelect(id : Identifier) extends SelectorOperator {
  override val ident = id
  override def toString = "." + id
  override def fixity = Operator.POSTFIX
}
case class RecordSelect(id: Identifier) extends SelectorOperator {
  override val ident = id
  override def toString = "." + id
  override def fixity = Operator.POSTFIX
}
case class SelectFromInstance(varId : Identifier) extends SelectorOperator {
  override val ident = varId
  override def toString = "." + varId
  override def fixity = Operator.INFIX
}
case class HyperSelect(i: Int) extends Operator {
  override def toString: String = "." + i.toString
  override def fixity = Operator.POSTFIX
}
case class ArraySelect(indices: List[Expr]) extends Operator {
  override def toString = {
    val indexStr = Utils.join(indices.map(_.toString()), ", ")
    "[" + indexStr + "]"
  }
  override def fixity = Operator.POSTFIX
  override def codegenUclidLang: Option[Operator] = {
    indices.forall(_.codegenUclidLang.isDefined) match {
      case true => Some(ArraySelect(indices.map(_.codegenUclidLang).flatten))
      case false => None
    }
  }
}
case class ArrayUpdate(indices: List[Expr], value: Expr) extends Operator {
  override def toString: String = {
    val indexStr = Utils.join(indices.map(_.toString()), ", ")
    "[" + indexStr + " -> " + value.toString() + "]"
  }
  override def fixity = Operator.POSTFIX
  override def codegenUclidLang: Option[Operator] = {
    indices.forall(_.codegenUclidLang.isDefined) match {
      case true => value.codegenUclidLang match {
        case Some(e) => Some(ArrayUpdate(indices.map(_.codegenUclidLang).flatten, e))
        case None => None
      }
      case false => None
    }
  }
}
case class RecordUpdate(fieldid: Identifier, value: Expr) extends Operator {
  override def toString: String = {
    "[" + fieldid.name + " := " + value.toString() + "]"
  }
  override def fixity: Int = Operator.POSTFIX

  override def codegenUclidLang: Option[Operator] = fieldid.codegenUclidLang match {
    case Some(f) => value.codegenUclidLang match {
      case Some(e) => Some(RecordUpdate(fieldid, e))
      case _ => None
    }
    case None => None
  }
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

  def codegenUclidLang : Option[Expr] = None
}

/**
 *  Type refinements:
 *  QIdentifier :> QualifiedIdentifier
 *      v  
 *  UIdentifier :> Identifier, ExternalIdentifier, IndexedIdentifier
 * 
 *  This type-hierarchy emulates SMTLIB
 *    and makes SMTLIB -> UclidLang parsing more natural
 */
sealed abstract class QIdentifier extends Expr
sealed abstract class UIdentifier extends QIdentifier
case class Identifier(name : String) extends UIdentifier {
  override def toString = name.toString

  /**
    * Checks whether the identifier matches either an
    * Enum element name or a Record field name
    *
    * @return
    */
  override def codegenUclidLang: Option[Expr] =
    ULContext.checkEnum(this) match {
      case true => Some(this)
      case false => ULContext.stripFieldName(name) match {
        case Some(s) => ULContext.checkField(Identifier(s)) match {
          case true => Some(Identifier(s))
          case false => None
        }
        case None =>ULContext.checkUninterpretedField(this) match{
          case true => Some(UninterpretedTypeLiteral(this.toString))
          case false => None
        }
      }
    }
}
case class ExternalIdentifier(moduleId : Identifier, id : Identifier) extends UIdentifier {
  override def toString = moduleId.toString + "::" + id.toString
}
case class IndexedIdentifier (name : String, indices : List[Either[IntLit, Identifier]]) extends UIdentifier {
  override def toString = "(_ " + name.toString + " " + indices.map(a => a.toString).mkString(" ") + ")"
}
case class QualifiedIdentifier (f : UIdentifier, typs : Type) extends QIdentifier {
  override def toString = "(as " + f.toString + " " + typs.toString + ")"
}
case class QualifiedIdentifierApplication (qid : QIdentifier, exprs : List[Expr]) extends Expr {
  override def toString = "(" + qid.toString + " " + exprs.map(a => a.toString).mkString(" ") + " )"

  // ! This is hardcoded for the ((as const [ArrayType]) [Expr]) syntax seen in  Z3, CVC5 cexes
  override def codegenUclidLang : Option[Expr] = qid match {
    case QualifiedIdentifier(f, typs) => 
      if (f.toString == "const" && exprs.size == 1) typs match {
        case at : ArrayType => at.codegenUclidLang match {
          case Some(a) => exprs(0).codegenUclidLang match {
            case Some(e) => Some(ConstArray(e, a))
            case None => None
          }
          case None => None
        }
        case _ => None
      } else None 
    case Identifier(name) => ULContext.stripMkTupleFunction(name) match {
      case Some(s) => {
        val rawtype = ULContext.postTypeMap.get(s).get.asInstanceOf[ProductType]
        val exprsOrNone = exprs.map(_.codegenUclidLang)
        if (exprsOrNone.forall(_.isDefined) && exprsOrNone.size == rawtype.fields.size) {
          Some(ConstRecord(rawtype.fields.map(_._1) zip exprsOrNone.flatten))
        } else None
      }
      case None => None
    }
    case _ => None
  }
}

sealed abstract class Literal extends Expr {
  /** All literals are constants. */
  override def isConstant = true
  def isNumeric = false
  def typeOf: Type
}
/** A non-deterministic new constant. */
case class FreshLit(typ : Type) extends Literal {
  override def toString = "*"
  // override val hashId = 2200
  override def typeOf: Type = typ
  // override val md5hashCode = computeMD5Hash(typ)
}
sealed abstract class NumericLit extends Literal {
  override def isNumeric = true
  override def typeOf : NumericType
  def to (n : NumericLit) : Seq[NumericLit]
  def negate: NumericLit
}
case class BoolLit(value: Boolean) extends Literal {
  override def toString = value.toString
  // override val hashId = 2201
  override def typeOf: Type = BooleanType()
  // override val md5hashCode = computeMD5Hash(value)

  override def codegenUclidLang : Option[Expr] = Some(this)
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

  override def codegenUclidLang : Option[Expr] = Some(this)
}

case class RealLit(integral: BigInt, fractional: String) extends NumericLit {
  override def toString = integral.toString + "." + fractional
  override def typeOf : NumericType = RealType()
  override def to (n : NumericLit) : Seq[NumericLit]  = {
    n match {
      case _ => throw new Utils.RuntimeError("Cannot create range for real literals")
    }
  }
  override def negate = RealLit(-integral, fractional)
}

case class FloatLit(integral: BigInt, fractional: String, exp: Int, sig: Int) extends NumericLit {
  override def toString = integral.toString + "." + fractional
  override def typeOf : NumericType = FloatType(exp, sig)
  override def to (n : NumericLit) : Seq[NumericLit]  = {
    n match {
      case _ => throw new Utils.RuntimeError("Cannot create range for float literals")
    }
  }
  override def negate = FloatLit(-integral, fractional, exp, sig)
}

case class BitVectorLit(value: BigInt, width: Int) extends NumericLit {
  override def toString = value.toString + "bv" + width.toString
  override def typeOf : NumericType = BitVectorType(width)
  override def to (n : NumericLit) : Seq[NumericLit] = {
    n match {
      case bv : BitVectorLit => (value to bv.value).map(BitVectorLit(_, width))
      case _ => throw new Utils.RuntimeError("Cannot create range for differing types of numeric literals.")
    }
  }
  override def negate = BitVectorLit(-value, width)

  override def codegenUclidLang : Option[Expr] = Some(this)
}

case class StringLit(value: String) extends Literal {
  override def toString = "\"" + value + "\""
  // override val hashId = 2202
  override def typeOf: Type = StringType()
  // override val md5hashCode = computeMD5Hash(value)
}

case class ConstArray(exp: Expr, typ: Type) extends Expr {
  override def toString = "const(%s, %s)".format(exp.toString(), typ.toString())
}

case class UninterpretedTypeLiteral(value : String) extends Expr{
  override def toString = value
  def toIdentifier = Identifier(value)
  def typeOf: UninterpretedType = {
    val index = value.indexOf("!") // 6
    val typeName = value.substring(0,index) //utype
    return UninterpretedType(Identifier(typeName))     // identifer named "utype"
  }
}

case class ConstRecord(fieldvalues: List[(Identifier, Expr)]) extends Expr {
  override def toString = "const_record(%s)".format(
    fieldvalues.map(a => "%s := %s".format(a._1.toString, a._2.toString)).mkString(", ")
  )
}

case class Tuple(values: List[Expr]) extends Expr {
  override def toString = "{" + Utils.join(values.map(_.toString), ", ") + "}"
  // FIXME: We should not have temporal values inside of a tuple.
  override def isTemporal = false
}

sealed abstract class PossiblyTemporalExpr extends Expr
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
      case ITEOp() =>
        "if(" + operands(0).toString + ") then {" + operands(1).toString + "} else {" + operands(2).toString + "}"
      case ForallOp(_, _) | ExistsOp(_, _) | FiniteForallOp(_, _) | FiniteExistsOp(_, _) =>
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

  override def codegenUclidLang : Option[Expr] = op match {
    case PolymorphicSelect(_) | RecordSelect(_) | HyperSelect(_) | SelectFromInstance(_) | 
      ForallOp(_, _) | ExistsOp(_, _) | FiniteForallOp(_, _) | FiniteExistsOp(_, _) => None
    case _ => op.codegenUclidLang match {
      case Some(o) =>
        val opsOrNone = operands.map(_.codegenUclidLang)
        if (opsOrNone.forall(_.isDefined)) Some(OperatorApplication(o, opsOrNone.flatten))
        else None
      case None => None
    }
  }
  override def isTemporal = op.isTemporal || operands.exists(_.isTemporal)
}
//for uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class FuncApplication(e: Expr, args: List[Expr]) extends Expr {
  override def toString = e + "(" + Utils.join(args.map(_.toString), ", ") + ")"
}
case class Lambda(ids: List[(Identifier,Type)], e: Expr) extends Expr {
  override def toString = "Lambda(" + ids + "). " + e
}

case class LetExpr (ids: List[(UIdentifier, Expr)], e : Expr) extends Expr {
  override def toString = "(let (" + 
    ids.map(a => "(" + a._1.toString + " " + a._2.toString + ")").mkString(" ") + ") " +
    e.toString + ")"
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
  def isFloat = false
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

  def codegenUclidLang : Option[Type] = None
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
  override def codegenUclidLang: Option[Type] = Some(this)
}
case class IntegerType() extends NumericType {
  override def toString = "integer"
  override def isInt = true
  override def defaultValue = Some(IntLit(0))
  override def codegenUclidLang: Option[Type] = Some(this)
}
case class RealType() extends NumericType {
  override def toString = "real"
  def isReal = true
  override def defaultValue = Some(RealLit(0, 0.toString))
  override def codegenUclidLang: Option[Type] = Some(this)
}
case class FloatType(exp: Int, sig: Int) extends NumericType {
  override def toString = "float"
  override def isFloat = true
  override def defaultValue = Some(FloatLit(0, 0.toString, exp, sig))
}
case class BitVectorType(width: Int) extends NumericType {
  override def toString = "bv" + width.toString
  override def isBitVector = true
  def isValidSlice(slice : ConstBitVectorSlice) : Boolean = {
    return (slice.lo >= 0 && slice.hi < width)
  }
  override def defaultValue = Some(BitVectorLit(0, width))
  override def codegenUclidLang: Option[Type] = Some(this)
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
      case hd :: _ => Some(hd)
      case _ => None
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
      case _ => 
      this == t2
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
  override def codegenUclidLang: Option[Type] = {
    val inTypesOrNone = inTypes.map(_.codegenUclidLang)
    if (inTypesOrNone.forall(_.isDefined)) outType.codegenUclidLang match {
      case Some(ot) => Some(ArrayType(inTypesOrNone.flatten, ot))
      case None => None 
    } else { None }
  }
}
case class SynonymType(id: Identifier) extends Type {
  override def toString = id.toString
  override def equals(other: Any) = other match {
    case that: SynonymType => that.id.name == this.id.name
    case _ => false
  }
  override def codegenUclidLang: Option[Type] = ULContext.smtToLangSynonym(id.name)
}

case class GroupType(typ : Type) extends Type {
  override def toString = "group (" + typ.toString + ")"
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
    functions: List[(Identifier, FunctionSig)], synthFunctions : List[(Identifier, FunctionSig)], instances: List[(Identifier, Type)]) extends Type {

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
  lazy val synthFuncMap : Map[Identifier, FunctionSig] = synthFunctions.map(a => (a._1 -> a._2)).toMap
  lazy val instanceMap : Map[Identifier, Type] = instances.map(a => (a._1 -> a._2)).toMap
  lazy val typeMap : Map[Identifier, Type] = inputMap ++ outputMap ++ constantMap ++ varMap ++ funcMap.map(f => (f._1 -> f._2.typ))  ++ instanceMap
  lazy val externalTypeMap : Map[Identifier, Type] = constantMap ++ funcMap.map(f => (f._1 -> f._2.typ)) ++ constLitMap.map(f => (f._1 -> f._2.typeOf)) ++ synthFuncMap.map(sf => (sf._1 -> sf._2.typ))
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

/* Introduced as an intermediate representation to denote havoc'ing 
 * specific state variables within an instance.
 */
case class HavocableInstanceId(opapp : OperatorApplication) extends HavocableEntity {
  override def toString = opapp.toString()
}

/** Statements **/
sealed abstract class Statement extends ASTNode {

  override def toString = 
  {
      Utils.join(toLines, "\n")
  }
  // TODO: these should be moved to annotations?
  def hasStmtBlock = false
  val isLoop = false
  val hasLoop = false
  val hasCall : Boolean
  val hasInternalCall : Boolean
  def toLines : List[String]
}
case class SkipStmt() extends Statement {
  override def toLines = List("skip; // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false
}
case class AssertStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assert " + e + "; // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false
}
case class AssumeStmt(e: Expr, id : Option[Identifier]) extends Statement {
  override def toLines = List("assume " + e + "; // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false
}
case class HavocStmt(havocable : HavocableEntity) extends Statement {
  override def toLines = List("havoc " + havocable.toString() + "; // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false;
}
case class AssignStmt(lhss: List[Lhs], rhss: List[Expr]) extends Statement {
  override def toLines =
    List(Utils.join(lhss.map (_.toString), ", ") + " = " + Utils.join(rhss.map(_.toString), ", ") + "; // " + position.toString)
  override val hasCall = false
  override val hasInternalCall = false
}
case class BlockStmt(vars: List[BlockVarsDecl], stmts: List[Statement]) extends Statement {
  override def hasStmtBlock = true
  override val hasLoop = stmts.exists(st => st.hasLoop)
  override def toLines = { 
      List("{ //" ) ++
      vars.map(PrettyPrinter.indent(1) + _.toString()) ++
      stmts.flatMap(_.toLines).map(PrettyPrinter.indent(1) + _) ++
      List("}")
  }
  override val hasCall = stmts.exists(st => st.hasCall)
  override val hasInternalCall = stmts.exists(st => st.hasInternalCall)
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
  override val hasInternalCall = ifblock.hasInternalCall || elseblock.hasInternalCall
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
  override val hasInternalCall = body.hasInternalCall
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
}
case class CaseStmt(body: List[(Expr,Statement)]) extends Statement {
  override def hasStmtBlock = true
  override def toLines = List("case") ++
    body.flatMap{ (i) => List(PrettyPrinter.indent(1) + i._1.toString + " : ") ++ i._2.toLines } ++
    List("esac")
  override val hasCall = body.exists(b => b._2.hasCall)
  override val hasInternalCall = body.exists(b => b._2.hasInternalCall)
}
case class ProcedureCallStmt(id: Identifier, callLhss: List[Lhs], args: List[Expr], instanceId : Option[Identifier], moduleId : Option[Identifier]=None)  extends Statement {
  override def toLines = List("call (" +
    Utils.join(callLhss.map(_.toString), ", ") + ") = " + (if (instanceId.isEmpty) "" else (instanceId.get.name + ".")) +  id + "(" +
    Utils.join(args.map(_.toString), ", ") + ") // " + id.position.toString)
  override val hasCall = true
  override val hasInternalCall = instanceId.isEmpty
}
case class MacroCallStmt(id: Identifier) extends Statement {
  override def toLines = List(id + "; // " + id.position.toString())
  override val hasCall = false
  override val hasInternalCall = false
}
case class ModuleCallStmt(id: Identifier) extends Statement {
  override def toLines = List("next (" + id.toString +")")
  override val hasCall = false
  override val hasInternalCall = false
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
}

case class InstanceDecl(instanceId : Identifier, moduleId : Identifier, arguments: List[(Identifier, Option[Expr])], instType : Option[ModuleInstanceType], modType : Option[ModuleType]) extends Decl
{
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
}

/* 
 * Introduced as an intermediate node in the ASTs to track the state 
 * variables that are modified within an instance.
 */
case class ModifiableInstanceId(opapp : OperatorApplication) extends ModifiableEntity {
  override val expr = opapp
  override def toString = opapp.toString()
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
case class ProcedureModifiesExpr(modifiable : ModifiableEntity) extends ProcedureVerificationExpr {
  override val expr = modifiable.expr
  override val toString = "modifies " + modifiable.toString
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
    requires: List[Expr], ensures: List[Expr], modifies: Set[ModifiableEntity],
    annotations : ProcedureAnnotations) extends Decl
{
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

  lazy val shouldInline = {
    if(annotations.ids.contains(Identifier("noinline")))
    {
      if(ensures.size == 0)
        UclidMain.printStatus("Warning: noinlining procedure "+ id + " even though it has no ensures statement")
      if(annotations.ids.contains(Identifier("inline")))
        throw new Utils.RuntimeError("Procedure " + id + " has both inline and noinline annotations.")
      false;  
    }
    else
      true;
  }
}
case class TypeDecl(id: Identifier, typ: Type) extends Decl {
  override def toString = "type " + id + " = " + typ + "; // " + position.toString
  override def declNames = List(id)
  ULContext.addSynonym(id.name, typ)
}
case class ModuleImportDecl(modId: Identifier) extends Decl {
  override def toString = "import %s;".format(modId.toString())
  override def declNames = List.empty
}
case class ModuleTypesImportDecl(id : Identifier) extends Decl {
  override def toString = "type * = %s.*; // %s".format(id.toString(), position.toString())
  override def declNames = List.empty
}
case class StateVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override def toString = "var " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class InputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override def toString = "input " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class OutputVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override def toString = "output " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString
  override def declNames = ids
}
case class SharedVarsDecl(ids: List[Identifier], typ: Type) extends Decl {
  override def toString = "sharedvar " + Utils.join(ids.map(_.toString), ", ") + " : " + typ + "; // " + position.toString()
  override def declNames = ids
}
/** This is base trait for all entities that are exported from a module. */
sealed abstract trait ModuleExternal {
  def extNames : List[Identifier]
  def extType : Type
}
case class ConstantLitDecl(id : Identifier, lit : NumericLit) extends Decl {
  override def toString = "const %s = %s; // %s".format(id.toString(), lit.toString(), position.toString())
  override def declNames = List(id)
}
case class ConstantsDecl(ids: List[Identifier], typ: Type) extends Decl with ModuleExternal {
  override def toString = "const " + Utils.join(ids.map(_.toString), ", ") + ": " + typ + "; // " + position.toString
  override def declNames = ids
  override def extNames = ids
  override def extType = typ
}
case class ModuleConstantsImportDecl(id: Identifier) extends Decl {
  override def toString = "const * = %s.*; // %s".format(id.toString, position.toString)
  override def declNames = List.empty
}
case class FunctionDecl(id: Identifier, sig: FunctionSig) extends Decl with ModuleExternal {
  override def toString = "function " + id + sig + ";  // " + position.toString
  override def declNames = List(id)
  override def extNames = List(id)
  override def extType = sig.typ
}
case class ModuleFunctionsImportDecl(id: Identifier) extends Decl {
  override def toString = "function * = %s.*; // %s".format(id.toString, position.toString)
  override def declNames = List.empty
}
case class ModuleSynthFunctionsImportDecl(id : Identifier) extends Decl {
  override def toString = "synthesis function * = %s.*; // %s".format(id.toString, position.toString)
  override def declNames = List.empty
}
case class DefineDecl(id: Identifier, sig: FunctionSig, expr: Expr) extends Decl {
  override def toString = "define %s %s = %s;".format(id.toString, sig.toString, expr.toString)
  override def declNames = List(id)
}
case class MacroDecl(id: Identifier, sig: FunctionSig, body: BlockStmt) extends Decl {
  override def toString =
    "macro " + id + "// " + position.toString + "\n" +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  override def declNames = List(id)
}

case class AssignmentModel(functions: List[(DefineDecl, String)]) {
  override def toString = 
    "assignment-model %s;".format(functions.map(a => a._1.toString).mkString("\n"))
}

case class ModuleDefinesImportDecl(id: Identifier) extends Decl {
  override def toString = "define * = $s.*; // %s".format(id.toString)
  override def declNames = List.empty
}
case class GroupDecl(id: Identifier, typ : GroupType, members: List[Expr]) extends Decl {
  override def toString = "define %s : %s = %s;".format(id.toString, typ.toString, members.toString)
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

case class DefineAppTerm(id: Identifier, args: List[GrammarTerm]) extends GrammarTerm {
  override def toString = {
    val argStr = args.map(_.toString)
    val str = id.toString + "(" + Utils.join(argStr, ", ") + ")"
    "(" + str + ")"
  }
}

case class NonTerminal(id: Identifier, typ: Type, terms: List[GrammarTerm]) extends ASTNode {
  override def toString = {
    "(%s : %s) ::= %s;".format(id.toString, typ.toString, Utils.join(terms.map(_.toString), " | "))
  }
}

case class GrammarDecl(id: Identifier, sig: FunctionSig, nonterminals: List[NonTerminal]) extends Decl {
  override def toString = {
    val header :String = "grammar %s %s = { // %s".format(id.toString, sig.toString(), position.toString)
    val lines = nonterminals.map(PrettyPrinter.indent(2) + _.toString)
    header + "\n" + Utils.join(lines, "\n") + "\n" + PrettyPrinter.indent(1) + "}"
  }
  override def declNames = List(id)
}

case class SynthesisFunctionDecl(id: Identifier, sig: FunctionSig, grammarId : Option[Identifier], grammarArgs: List[Identifier], conditions: List[Expr]) extends Decl with ModuleExternal {
  override def toString = "synthesis function " + id + sig + "; //" + position.toString()
  override def declNames = List(id)
  override def extNames = List(id)
  override def extType = sig.typ
}

case class OracleFunctionDecl(id: Identifier, sig: FunctionSig, binary: String) extends Decl {
  override def toString = "oracle function [" + binary + "]" + id + sig + "; //" + position.toString()
  override def declNames = List(id)
}

case class InitDecl(body: Statement) extends Decl {
  override def toString =
    "init // " + position.toString + "\n" +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  override def declNames = List.empty
}
case class NextDecl(body: Statement) extends Decl {
  override def toString =
    "next // " + position.toString + "\n" +
    Utils.join(body.toLines.map(PrettyPrinter.indent(2) + _), "\n")
  override def declNames = List.empty
}
case class SpecDecl(id: Identifier, expr: Expr, params: List[ExprDecorator]) extends Decl {
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


case class AxiomDecl(id : Option[Identifier], expr: Expr, params: List[ExprDecorator]) extends Decl {
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
case class CommandParams(name: Identifier, values: List[Expr]) extends ASTNode
{
  override def toString = {
    name.toString + " = (" + Utils.join(values.map(_.toString()), ", ") + "); "
  }
}

case class GenericProofCommand(
    name : Identifier, params: List[CommandParams], args : List[(Expr, String)], 
    resultVar: Option[Identifier], argObj: Option[Identifier], macroBody: Option[BlockStmt]) 
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
          case _ : java.util.NoSuchElementException => context
          case _ : scala.ClassCastException => context
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
  def isPrintCEX : Boolean = { name == Identifier("print_cex") || name == Identifier("print_cex_json") }

  def modifiesModule : Boolean = { name == Identifier("assign_macro") }
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

case class MacroAnnotation(macroMap: Map[Identifier, List[ASTPosition]]) extends Annotation{
  override def toString : String = {
    val start = PrettyPrinter.indent(1) + "// macro_annotation_map { "
    val lines = macroMap.map(p => PrettyPrinter.indent(1) + "//   " + p._1.toString + " ::===>" + Utils.join(p._2.map(_.toString), " + ") )
    val end = PrettyPrinter.indent(1) + "// } end_macro_annotation_map"
    Utils.join(List(start) ++ lines ++ List(end), "\n") +"\n"
  }
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
}

object Annotation {
  val default = List(InstanceVarMapAnnotation(Map.empty))
}

case class Module(id: Identifier, decls: List[Decl], var cmds : List[GenericProofCommand], notes: List[Annotation]) extends ASTNode {
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
  
  // module imports.
  lazy val moduleImportDecls : List[ModuleImportDecl] = decls.collect { case decl : ModuleImportDecl => decl }
  
  // module function imports.
  lazy val funcImportDecls : List[ModuleFunctionsImportDecl] = decls.collect {
  case imp : ModuleFunctionsImportDecl => imp }
  
  // module functions.
  lazy val functions : List[FunctionDecl] =
    decls.filter(_.isInstanceOf[FunctionDecl]).map(_.asInstanceOf[FunctionDecl])
  
  // module synthesis function imports.
  lazy val synthFuncImportDecls : List[ModuleSynthFunctionsImportDecl] = decls.collect {
    case imp : ModuleSynthFunctionsImportDecl => imp }

  // module macros
  lazy val defines : List[DefineDecl] = decls.collect{ case d : DefineDecl => d }

  // module statement macros
  lazy val macroDecls : List[MacroDecl] = decls.collect{ case d : MacroDecl => d }

  lazy val synthFunctions: List[SynthesisFunctionDecl] =
    decls.filter(_.isInstanceOf[SynthesisFunctionDecl]).map(_.asInstanceOf[SynthesisFunctionDecl])
  
  lazy val grammarDecls: List[GrammarDecl] = decls.collect { case gDecl: GrammarDecl => gDecl }

  // module properties.
  lazy val properties : List[SpecDecl] = decls.collect{ case spec : SpecDecl => spec }

  lazy val externalMap : Map[Identifier, ModuleExternal] =
    (functions.map(f => (f.id -> f))  ++ synthFunctions.map(sf => (sf.id -> sf)) ++ (constantDecls.flatMap(c => c.ids.map(id => (id, c))).map(p => p._1 -> p._2))).toMap

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
      synthFunctions.map(sf => (sf.id, sf.sig)),
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
      case Some(_) => notes.map {
        n => {
          n match {
            case _ : T => note
            case _ => n
          }
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

//below is used for Syntax Error
sealed abstract class ErrorNode extends ASTNode{
  val name : String
}
case class SingleKw(N: String) extends ErrorNode{
  override val name = N
}
case class ErrorMessage(N: String) extends ErrorNode{
  override val name = N
}
