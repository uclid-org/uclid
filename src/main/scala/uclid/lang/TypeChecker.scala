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
 * Authors: Norman Mu, Pramod Subramanyan
 *
 * All sorts of type inference and type checking functionality is in here.
 *
 */

package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}
import scala.util.parsing.input.Position
import com.typesafe.scalalogging.Logger

class TypeSynonymFinderPass extends ReadOnlyPass[Unit]
{
  type TypeMap = MutableMap[Identifier, Type]
  type TypeSet = MutableSet[Identifier]
  var typeDeclMap : TypeMap = MutableMap.empty
  var typeSynonyms : TypeSet = MutableSet.empty

  override def reset () {
    typeDeclMap.clear()
    typeSynonyms.clear()
  }
  override def applyOnModule( d : TraversalDirection.T, module : Module, in : Unit, context : Scope) : Unit = {
    if (d == TraversalDirection.Up) {
      validateSynonyms(module)
      simplifySynonyms(module)
    }
  }
  override def applyOnTypeDecl(d : TraversalDirection.T, typDec : TypeDecl, in : Unit, context : Scope) : Unit = {
    if (d == TraversalDirection.Down) {
      typeDeclMap.put(typDec.id, typDec.typ)
    }
  }
  override def applyOnType( d : TraversalDirection.T, typ : Type, in : Unit, context : Scope) : Unit = {
    if (d == TraversalDirection.Down) {
      typ match {
        case SynonymType(name) => typeSynonyms += name
        case _ => /* skip */
      }
    }
  }

  def validateSynonyms(module : Module) {
    typeSynonyms.foreach {
      (syn) => Utils.checkParsingError(
          typeDeclMap.contains(syn),
          "Type synonym '" + syn.toString + "' used without declaration in module '" + module.id + "'",
          syn.pos, module.filename
      )
    }
  }

  def simplifyType(typ : Type, visited : Set[Identifier], m : Module) : Type = {
    typ match {
      case SynonymType(otherName) =>
        if (visited contains otherName) {
          val msg = "Recursively defined synonym type: %s".format(otherName.toString)
          throw new Utils.TypeError(msg, Some(otherName.pos), m.filename)
        }
        simplifyType(typeDeclMap.get(otherName).get, visited + otherName, m)
      case TupleType(fieldTypes) =>
        TupleType(fieldTypes.map(simplifyType(_, visited, m)))
      case RecordType(fields) =>
        RecordType(fields.map((f) => (f._1, simplifyType(f._2, visited, m))))
      case MapType(inTypes, outType) =>
        MapType(inTypes.map(simplifyType(_, visited, m)), simplifyType(outType, visited, m))
      case ArrayType(inTypes, outType) =>
        ArrayType(inTypes.map(simplifyType(_, visited, m)), simplifyType(outType, visited, m))
      case GroupType(gTyp) =>
        GroupType(simplifyType(gTyp, visited, m))
      case _ =>
        typ
    }
  }

  def simplifySynonyms(m : Module) {
    var simplified = false
    do {
      simplified = false
      typeDeclMap.foreach {
        case (name, typ) => {
          typ match {
            case SynonymType(otherName) =>
                simplified = true
                typeDeclMap.put(name, simplifyType(typeDeclMap.get(otherName).get, Set.empty, m))
            case _ =>
                typeDeclMap.put(name, simplifyType(typ, Set.empty, m))
          }
        }
      }
    } while (simplified)
  }
}

class TypeSynonymFinder extends ASTAnalyzer("TypeSynonymFinder", new TypeSynonymFinderPass())  {
  override def pass = super.pass.asInstanceOf[TypeSynonymFinderPass]
  in = Some(Unit)
}

class TypeSynonymRewriterPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val typeSynonymFinderPass = manager.pass("TypeSynonymFinder").asInstanceOf[TypeSynonymFinder].pass
  override def rewriteType(typ : Type, ctx : Scope) : Option[Type] = {
    val result = typ match {
      case SynonymType(name) => typeSynonymFinderPass.typeDeclMap.get(name)
      case GroupType(SynonymType(name)) =>
        val realName = typeSynonymFinderPass.typeDeclMap.get(name)
        if (realName.isDefined) {
            Some(GroupType(realName.get))
        } else {
            Some(typ) //Undefined synonym types are checked for in validateSynonyms(..).
        }
      case _ => Some(typ)
    }
    return result
  }
}

class TypeSynonymRewriter extends ASTRewriter(
    "TypeSynonymRewriter", new TypeSynonymRewriterPass())

object ReplacePolymorphicOperators {
  def toInt(op : PolymorphicOperator) : IntArgOperator = {
    val intOp = op match {
      case LTOp() => IntLTOp()
      case LEOp() => IntLEOp()
      case GTOp() => IntGTOp()
      case GEOp() => IntGEOp()
      case AddOp() => IntAddOp()
      case SubOp() => IntSubOp()
      case MulOp() => IntMulOp()
      case DivOp() => IntDivOp()
      case UnaryMinusOp() => IntUnaryMinusOp()
    }
    intOp.pos = op.pos
    intOp
  }
  def toBitvector(op : PolymorphicOperator, w : Int) : BVArgOperator = {
    val bvOp = op match {
      case LTOp() => BVLTOp(w)
      case LEOp() => BVLEOp(w)
      case GTOp() => BVGTOp(w)
      case GEOp() => BVGEOp(w)
      case AddOp() => BVAddOp(w)
      case SubOp() => BVSubOp(w)
      case MulOp() => BVMulOp(w)
      case DivOp() => BVDivOp(w)
      case UnaryMinusOp() => BVUnaryMinusOp(w)
    }
    bvOp.pos = op.pos
    bvOp
  }
  def toFloat(op : PolymorphicOperator, e: Int, s: Int) : FloatArgOperator = {
    val fltOp = op match {
      case LTOp() => FPLTOp(e,s)
      case GTOp() => FPGTOp(e,s)
      case LEOp() => FPLEOp(e,s)
      case GEOp() => FPGEOp(e,s)
      case AddOp() => FPAddOp(e,s)
      case SubOp() => FPSubOp(e,s)
      case MulOp() => FPMulOp(e,s)
      case DivOp() => FPDivOp(e,s)
      case UnaryMinusOp() => FPUnaryMinusOp(e,s)
    }
    fltOp.pos = op.pos
    fltOp
  }

  def toType(op : PolymorphicOperator, typ : NumericType) = {
    typ match {
      case _ : IntegerType => toInt(op)
      case bvTyp : BitVectorType => toBitvector(op, bvTyp.width)
      case fltTyp: FloatType => toFloat(op, fltTyp.exp, fltTyp.sig)
    }
  }
  def rewrite(e : Expr, typ : NumericType) : Expr = {
    def r(e : Expr) : Expr = rewrite(e, typ)
    def rs(es : List[Expr])  = es.map(r(_))

    e match {
      case _ : Identifier => e
      case _ : ExternalIdentifier => e
      case _ : Literal => e
      case Tuple(es) => Tuple(es.map(r(_)))
      case OperatorApplication(op, operands) =>
        val opP = op match {
          case p : PolymorphicOperator => toType(p, typ)
          case ArraySelect(es) => ArraySelect(rs(es))
          case ArrayUpdate(es, e) => ArrayUpdate(rs(es), r(e))
          case RecordUpdate(id, e) => RecordUpdate(id, r(e))
          case _ => op
        }
        OperatorApplication(opP, rs(operands))
      case ConstArray(exp, typ) =>
        ConstArray(r(exp), typ)
      case FuncApplication(expr, args) =>
        FuncApplication(r(expr), rs(args))
      case Lambda(args, expr) =>
        Lambda(args, r(expr))
    }
  }
}


class ExpressionTypeCheckerPass extends ReadOnlyPass[Set[Utils.TypeError]]
{
  lazy val logger = Logger(classOf[ExpressionTypeCheckerPass])
  type Memo = MutableMap[IdGenerator.Id, Type]
  var memo : Memo = MutableMap.empty
  type ErrorList = Set[Utils.TypeError]

  var polyOpMap : MutableMap[IdGenerator.Id, Operator] = MutableMap.empty
  var bvOpMap : MutableMap[IdGenerator.Id, Int] = MutableMap.empty
  var fpOpMap : MutableMap[IdGenerator.Id, (Int, Int)] = MutableMap.empty

  override def reset() = {
    memo.clear()
    polyOpMap.clear()
  }

  override def applyOnExpr(d : TraversalDirection.T, e : Expr, in : ErrorList, ctx : Scope) : ErrorList = {
    if (d == TraversalDirection.Up) {
      try {
        typeOf(e, ctx)
      } catch {
        case p : Utils.TypeError => {
          return (in + p)
        }
      }
    }
    return in
  }

  override def applyOnLHS(d : TraversalDirection.T, lhs : Lhs, in : ErrorList, ctx : Scope) : ErrorList = {
    if (d == TraversalDirection.Up) {
      try {
        typeOf(lhs, ctx)
      } catch {
        case p : Utils.TypeError => {
          return (in + p)
        }
      }
    }
    return in
  }

  def raiseTypeError(msg: => String, pos: => Position, filename: => Option[String]) {
      throw new Utils.TypeError(msg, Some(pos), filename)
  }
  def checkTypeError(condition: Boolean, msg: => String, pos: => Position, filename: => Option[String]) {
    if (!condition) {
      raiseTypeError(msg, pos, filename)
    }
  }

  def typeOf(lhs : Lhs, c : Scope) : Type = {
    val cachedType = memo.get(lhs.astNodeId)
    if (cachedType.isDefined) {
      return cachedType.get
    }

    val id = lhs.ident
    val typOpt = c.typeOf(id)
    checkTypeError(typOpt.isDefined, "Unknown variable in LHS: " + id.toString, lhs.pos, c.filename)
    val typ = typOpt.get
    val resultType = lhs match {
      case LhsId(_) | LhsNextId(_) =>
        typ
      case LhsArraySelect(id, indices) =>
        checkTypeError(typ.isArray, "Lhs variable in array index operation must be of type array: " + id.toString, lhs.pos, c.filename)
        val indexTypes = indices.map(typeOf(_, c))
        val arrTyp = typ.asInstanceOf[ArrayType]
        lazy val indexTypString = "(" + Utils.join(indexTypes.map(_.toString), ", ") + ")"
        lazy val inTypString = "(" + Utils.join(arrTyp.inTypes.map(_.toString), ", ") + ")"
        checkTypeError(arrTyp.inTypes == indexTypes, "Invalid index types. Expected: " + inTypString + "; got: " + indexTypString, lhs.pos, c.filename)
        arrTyp.outType
      case LhsRecordSelect(id, fields) =>
        checkTypeError(typ.isProduct, "Lhs variable in record select operation must be a product type: " + id.toString, lhs.pos, c.filename)
        val prodType = typ.asInstanceOf[ProductType]
        val fieldType = prodType.nestedFieldType(fields)
        lazy val fieldTypeString = Utils.join(fields.map(_.toString), ".")
        checkTypeError(fieldType.isDefined, "Field does not exist: " + fieldTypeString, lhs.pos, c.filename)
        fieldType.get
      case LhsSliceSelect(id, slice) =>
        checkTypeError(typ.isBitVector, "Lhs variable in bitvector slice update must be a bitvector: " + id.toString, lhs.pos, c.filename)
        val bvType = typ.asInstanceOf[BitVectorType]
        checkTypeError(bvType.isValidSlice(slice), "Invalid slice: " + slice.toString, slice.pos, c.filename)
        BitVectorType(slice.width.get)
      case LhsVarSliceSelect(_, slice) =>
        checkTypeError(slice.width.isDefined, "Width of bitvector slice is not constant", lhs.pos, c.filename)
        BitVectorType(slice.width.get)
    }
    memo.put(lhs.astNodeId, resultType)
    return resultType
  }
  def typeOf(e : Expr, c : Scope) : Type = {
    logger.debug("e: {}", e.toString())
    logger.debug("c: {}", c.map.keys.toString())
    def polyResultType(op : PolymorphicOperator, argType : Type) : Type = {
      op match {
        case LTOp() | LEOp() | GTOp() | GEOp() => new BooleanType()
        case AddOp() | SubOp() | MulOp() | DivOp() | UnaryMinusOp() => argType
      }
    }
    def opAppType(opapp : OperatorApplication) : Type = {
      val argTypes = opapp.operands.map(typeOf(_, c + opapp))
      logger.debug("opAppType: {}", opapp.toString())
      opapp.op match {
        case polyOp : PolymorphicOperator => {
          def numArgs(op : PolymorphicOperator) : Int = {
            op match {
              case UnaryMinusOp() => 1
              case _ => 2
            }
          }
          val nArgs = numArgs(polyOp)
          checkTypeError(argTypes.size == nArgs, "Operator '" + opapp.op.toString + "' must have two arguments", opapp.pos, c.filename)
          if (nArgs > 1) {
            checkTypeError(argTypes(0) == argTypes(1),
                "Arguments to operator '" + opapp.op.toString + "' must be of the same type. Types of expression '" +
                opapp.toString() + "' are " + opapp.operands(0).toString + ": " + argTypes(0).toString() + " and " + opapp.operands(1).toString + ": " + argTypes(1).toString(),
                opapp.pos, c.filename)
          }
          checkTypeError(argTypes.forall(_.isNumeric), "Arguments to operator '" + opapp.op.toString + "' must be of a numeric type", opapp.pos, c.filename)
          typeOf(opapp.operands(0), c) match {
            case i : IntegerType =>
              polyOpMap.put(polyOp.astNodeId, ReplacePolymorphicOperators.toInt(polyOp))
              polyResultType(polyOp, i)
            case bv : BitVectorType =>
              polyOpMap.put(polyOp.astNodeId, ReplacePolymorphicOperators.toBitvector(polyOp, bv.width))
              polyResultType(polyOp, bv)
            case fp: FloatType => 
              polyOpMap.put(polyOp.astNodeId, ReplacePolymorphicOperators.toFloat(polyOp, fp.exp, fp.sig))
              polyResultType(polyOp, fp)
            case _ => throw new Utils.UnimplementedException("Unknown operand type to polymorphic operator '" + opapp.op.toString + "'")
          }
        }
        case intOp : IntArgOperator => {
          def numArgs(op : IntArgOperator) : Int = {
            op match {
              case IntUnaryMinusOp() => 1
              case _ => 2
            }
          }
          checkTypeError(argTypes.size == numArgs(intOp), "Operator '" + opapp.op.toString + "' must have two arguments", opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isInstanceOf[IntegerType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Integer", opapp.pos, c.filename)
          intOp match {
            case IntLTOp() | IntLEOp() | IntGTOp() | IntGEOp() => new BooleanType()
            case IntAddOp() | IntSubOp() | IntMulOp() | IntDivOp() | IntUnaryMinusOp() => new IntegerType()
          }
        }
        case floatOp: FloatArgOperator => {
          checkTypeError(argTypes.size == floatOp.arity, "Operator '%s' must have exactly %d argument(s)".format(opapp.op.toString, floatOp.arity), opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isInstanceOf[FloatType]), "Argument(s) to operator '" + opapp.op.toString + "' must be of type float", opapp.pos, c.filename)
          floatOp match {
            case FPGTOp(_,_) | FPLTOp(_,_)| FPGEOp(_,_) | FPLEOp(_,_)| FPIsNanOp(_,_) =>
              val e = argTypes(0).asInstanceOf[FloatType].exp
              val s = argTypes(0).asInstanceOf[FloatType].sig
              fpOpMap.put(floatOp.astNodeId, (e,s))
              BooleanType()
            case FPMulOp(_,_) | FPSubOp(_,_)  | FPAddOp(_,_)  | FPDivOp(_,_)  | FPUnaryMinusOp(_,_)   =>
              checkTypeError(floatOp.e != 0, "Invalid exponent width argument to '%s' operator".format(opapp.op.toString()), opapp.pos, c.filename)
              checkTypeError(floatOp.s != 0, "Invalid significand width argument to '%s' operator".format(opapp.op.toString()), opapp.pos, c.filename)
              FloatType(floatOp.e, floatOp.s)
          }
        }

        case bvOp : BVArgOperator => {
          checkTypeError(argTypes.size == bvOp.arity, "Operator '%s' must have exactly %d argument(s)".format(opapp.op.toString, bvOp.arity), opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isInstanceOf[BitVectorType]), "Argument(s) to operator '" + opapp.op.toString + "' must be of type BitVector", opapp.pos, c.filename)
          bvOp match {
            case BVLTOp(_) | BVLEOp(_) | BVGTOp(_) | BVGEOp(_) =>
              BooleanType()
            case BVLTUOp(_) | BVLEUOp(_) | BVGTUOp(_) | BVGEUOp(_) =>
              val w = argTypes(0).asInstanceOf[BitVectorType].width
              bvOpMap.put(bvOp.astNodeId, w)
              BooleanType()
            case BVAddOp(_) | BVSubOp(_) | BVMulOp(_) | BVDivOp(_) | BVUnaryMinusOp(_) =>
              checkTypeError(bvOp.w != 0, "Invalid width argument to '%s' operator".format(opapp.op.toString()), opapp.pos, c.filename)
              BitVectorType(bvOp.w)
            case BVAndOp(_) | BVOrOp(_) | BVXorOp(_) | BVNotOp(_)| BVUremOp(_) | BVSremOp(_) | BVUDivOp(_) =>
              val w = argTypes(0).asInstanceOf[BitVectorType].width
              bvOpMap.put(bvOp.astNodeId, w)
              BitVectorType(w)
            case BVSignExtOp(_, e) =>
              checkTypeError(e > 0, "Invalid width argument to '%s' operator".format(opapp.op.toString()), opapp.pos, c.filename)
              val w = e + argTypes(0).asInstanceOf[BitVectorType].width
              bvOpMap.put(bvOp.astNodeId, w)
              BitVectorType(w)
            case BVZeroExtOp(_, e) =>
              checkTypeError(e > 0, "Invalid width argument to '%s' operator".format(opapp.op.toString()), opapp.pos, c.filename)
              val w = e + argTypes(0).asInstanceOf[BitVectorType].width
              bvOpMap.put(bvOp.astNodeId, w)
              BitVectorType(w)
            case BVLeftShiftBVOp(_) =>
              val w = argTypes(0).asInstanceOf[BitVectorType].width
              bvOpMap.put(bvOp.astNodeId, w)
              BitVectorType(w)
            case BVLRightShiftBVOp(_) =>
              val w = argTypes(0).asInstanceOf[BitVectorType].width
              bvOpMap.put(bvOp.astNodeId, w)
              BitVectorType(w)
            case BVARightShiftBVOp(_) =>
              val w = argTypes(0).asInstanceOf[BitVectorType].width
              bvOpMap.put(bvOp.astNodeId, w)
              BitVectorType(w)
          }
        }
        case qOp : QuantifiedBooleanOperator => {
          checkTypeError(argTypes(0).isInstanceOf[BooleanType], "Operand to the quantifier '" + qOp.toString + "' must be boolean", opapp.pos, c.filename)

          def checkFiniteQuantTypes(id : (Identifier, Type), groupId : Identifier, isForall : Boolean) : Type = {
            val typ = c.typeOf(groupId)
            val idTyp = id._2
            val quantTypeStr = if (isForall) "finite_forall" else "finite_exists"

            checkTypeError(typ.isDefined && typ.get.isInstanceOf[GroupType], "%s must be over a group".format(quantTypeStr), opapp.pos, c.filename)

            val innerTyp = typ.get.asInstanceOf[GroupType].typ

            checkTypeError(idTyp == innerTyp,
              "%s quantification variable %s has a different type than group type %s".format(quantTypeStr, idTyp, innerTyp), opapp.pos, c.filename)
            BooleanType()
          }

          qOp match {
            case FiniteForallOp(id, groupId) =>
              checkFiniteQuantTypes(id, groupId, true)
            case FiniteExistsOp(id, groupId) =>
              checkFiniteQuantTypes(id, groupId, false)
            case _ => BooleanType()
          }
        }
        case boolOp : BooleanOperator => {
          boolOp match {
            case NegationOp() =>
              checkTypeError(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument", opapp.pos, c.filename)
              checkTypeError(argTypes.forall(_.isInstanceOf[BooleanType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool", opapp.pos, c.filename)
            case ConjunctionOp() =>
              checkTypeError(argTypes.size >= 2, "Operator '" + opapp.op.toString + "' must have at least two arguments", opapp.pos, c.filename)
              checkTypeError(argTypes.forall(_.isInstanceOf[BooleanType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool", opapp.pos, c.filename)
            case _ =>
              checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments", opapp.pos, c.filename)
              checkTypeError(argTypes.forall(_.isInstanceOf[BooleanType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool", opapp.pos, c.filename)
          }
          BooleanType()
        }
        case _ : ComparisonOperator => {
          checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments", opapp.pos, c.filename)
          checkTypeError(argTypes(0) == argTypes(1), "Arguments to operator '" + opapp.op.toString + "' must be of the same type", opapp.pos, c.filename)
          BooleanType()
        }
        case BV2SignedIntOp() | BV2UnsignedIntOp() => {
          checkTypeError(argTypes.size == 1, "Operator '" + opapp.op.toString() + "' must have one argument", opapp.pos, c.filename)
          checkTypeError(argTypes(0).isInstanceOf[BitVectorType], "Argument to operator '" + opapp.op.toString() + "' must be a bitvector.", opapp.pos, c.filename)
          IntegerType()
        }
        case Int2BVOp(n) => {
          checkTypeError(argTypes.size == 1, "Operator '" + opapp.op.toString() + "' must have two arguments", opapp.pos, c.filename)
          checkTypeError(argTypes(0).isInstanceOf[IntegerType], "Operator  '" + opapp.op.toString() + "' must have an integer literal as the first argument", opapp.pos, c.filename)
          BitVectorType(n)
        }
        case _ : TemporalOperator => BooleanType()
        case extrOp : ExtractOp => {
          extrOp match {
            case ConstExtractOp(slice) => {
              checkTypeError(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument", opapp.pos, c.filename)
              checkTypeError(argTypes(0).isInstanceOf[BitVectorType], "Operand to operator '" + opapp.op.toString + "' must be of type BitVector", opapp.pos, c.filename)
              checkTypeError(argTypes(0).asInstanceOf[BitVectorType].width > slice.hi, "Operand to operator '" + opapp.op.toString + "' must have width > "  + slice.hi.toString, opapp.pos, c.filename)
              checkTypeError(slice.hi >= slice.lo, "High-operand must be greater than or equal to low operand for operator '" + opapp.op.toString + "'", opapp.pos, c.filename)
              checkTypeError(slice.hi >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative", opapp.pos, c.filename)
              checkTypeError(slice.lo >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative", opapp.pos, c.filename)
              BitVectorType(slice.hi - slice.lo + 1)
            }
            case VarExtractOp(slice) => {
              checkTypeError(slice.width.isDefined, "Slice width is not constant", extrOp.pos, c.filename)
              BitVectorType(slice.width.get)
            }
          }
        }
        case ConcatOp() => {
          checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments", opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector", opapp.pos, c.filename)
          new BitVectorType(argTypes(0).asInstanceOf[BitVectorType].width + argTypes(1).asInstanceOf[BitVectorType].width)
        }
        case PolymorphicSelect(field) =>
          Utils.assert(argTypes.size == 1, "Select operator must have exactly one operand.")
          argTypes(0) match {
            case recType : RecordType =>
              val typOption = recType.fieldType(field)
              checkTypeError(!typOption.isEmpty, "Field '" + field.toString + "' does not exist in " + recType.toString(), opapp.pos, c.filename)
              val recordSelect = RecordSelect(field)
              recordSelect.pos = opapp.op.pos
              polyOpMap.put(opapp.op.astNodeId, recordSelect)
              typOption.get
            case tupType : TupleType =>
              val indexS = field.name.substring(1)
              checkTypeError(indexS.forall(Character.isDigit), "Tuple fields must be integers preceded by an underscore", opapp.pos, c.filename)
              val indexI = indexS.toInt
              checkTypeError(indexI >= 1 && indexI <= tupType.numFields, "Invalid tuple index: " + indexS, opapp.pos, c.filename)
              val recordSelect = RecordSelect(field)
              recordSelect.pos = opapp.op.pos
              polyOpMap.put(opapp.op.astNodeId, recordSelect)
              tupType.fieldTypes(indexI-1)
            case modT : ModuleType =>
              val fldT = modT.typeMap.get(field)
              checkTypeError(fldT.isDefined, "Unknown type for selection: %s".format(field.toString), field.pos, c.filename)
              val selectFromInstance = SelectFromInstance(field)
              selectFromInstance.pos = opapp.op.pos
              polyOpMap.put(opapp.op.astNodeId, selectFromInstance)
              fldT.get
            case _ =>
              checkTypeError(false, "Argument to select operator must be of type record or instance", opapp.pos, c.filename)
              new UndefinedType()
          }
        case RecordSelect(field) =>
          Utils.assert(argTypes.size == 1, "Select operator must have exactly one operand.")
          argTypes(0) match {
            case recType : RecordType =>
              val typOption = recType.fieldType(field)
              checkTypeError(!typOption.isEmpty, "Field '" + field.toString + "' does not exist in " + recType.toString(), opapp.pos, c.filename)
              typOption.get
            case tupType : TupleType =>
              val indexS = field.name.substring(1)
              checkTypeError(indexS.forall(Character.isDigit), "Tuple fields must be integers preceded by an underscore", opapp.pos, c.filename)
              val indexI = indexS.toInt
              checkTypeError(indexI >= 1 && indexI <= tupType.numFields, "Invalid tuple index: " + indexS, opapp.pos, c.filename)
              tupType.fieldTypes(indexI-1)
            case _ =>
              checkTypeError(false, "Argument to select operator must be of type record", opapp.pos, c.filename)
              new UndefinedType()
          }
        case HyperSelect(_) =>
          Utils.assert(argTypes.size == 1, "Trace select operator must have one operand.")
          argTypes(0)
        case ArraySelect(es) =>
          Utils.assert(argTypes.size == 1, "Expected only one argument to array select operator")
          checkTypeError(argTypes(0).isArray, "Expected an array here", opapp.operands(0).pos, c.filename)
          val arrayType = argTypes(0).asInstanceOf[lang.ArrayType]
          val arrayIndexTypes = arrayType.inTypes
          checkTypeError(es.size == arrayIndexTypes.size, "Invalid number of indices", opapp.pos, c.filename)
          (arrayIndexTypes zip es).find(p => p._1 != typeOf(p._2, c)) match {
            case Some(p) => raiseTypeError("Invalid index type", p._2.pos, c.filename)
            case None =>
          }
          arrayType.outType
        case ArrayUpdate(es, e) =>
          Utils.assert(argTypes.size == 1, "Expected only one argument to array update operator")
          checkTypeError(argTypes(0).isArray, "Expected an array here", opapp.operands(0).pos, c.filename)
          val arrayType = argTypes(0).asInstanceOf[lang.ArrayType]
          val arrayIndexTypes = arrayType.inTypes
          checkTypeError(es.size == arrayIndexTypes.size, "Invalid number of indices", opapp.pos, c.filename)
          (arrayIndexTypes zip es).find(p => p._1 != typeOf(p._2, c)) match {
            case Some(p) => raiseTypeError("Invalid index type", p._2.pos, c.filename)
            case None =>
          }
          checkTypeError(typeOf(e, c) == arrayType.outType, "Invalid type of update value", e.pos, c.filename)
          arrayType
        case RecordUpdate(id, e) =>
          Utils.assert(argTypes.size == 1, "Expected only one argument to record update operator")
          checkTypeError(argTypes(0).isRecord, "Expected a record here", opapp.operands(0).pos, c.filename)
          val recordType = argTypes(0).asInstanceOf[lang.RecordType]
          val recordFieldTypes = recordType.fields
          checkTypeError(recordFieldTypes.map(a => a._1) contains id, "Invalid field-name in record update operator", id.pos, c.filename)
          val fieldType = recordFieldTypes.filter(a => (a._1.name == id.name))(0)._2
          checkTypeError(typeOf(e, c) == fieldType, "Invalid value-type in record update operator", id.pos, c.filename)
          recordType
        case SelectFromInstance(field) =>
          Utils.assert(argTypes.size == 1, "Select operator must have exactly one operand.")
          val inst= argTypes(0)
          checkTypeError(inst.isInstanceOf[ModuleType], "Argument to select operator must be module instance", field.pos, c.filename)
          val modT = inst.asInstanceOf[ModuleType]
          val fldT = modT.typeMap.get(field)
          checkTypeError(fldT.isDefined, "Unknown type for selection: %s".format(field.toString), field.pos, c.filename)
          fldT.get
        case GetNextValueOp() =>
          Utils.assert(argTypes.size == 1, "Expected exactly one argument to GetFinalValue")
          argTypes(0)
        case OldOperator() =>
          checkTypeError(argTypes.size == 1, "Expect exactly one argument to 'old'", opapp.pos, c.filename)
          //NOTE (REVISIT): We want to allow polymorphic selects
          if (opapp.operands(0).isInstanceOf[OperatorApplication]) {
            val checkOp = opapp.operands(0).asInstanceOf[OperatorApplication]
            checkTypeError(checkOp.op.isInstanceOf[PolymorphicSelect] || checkOp.op.isInstanceOf[SelectFromInstance], "Argument must be a instance var or an identifier", opapp.pos, c.filename)
            opAppType(checkOp)
          } else {
            checkTypeError(opapp.operands(0).isInstanceOf[Identifier], "Argument to old operator must be an identifier", opapp.pos, c.filename)
            argTypes(0)
          }
          //checkTypeError(opapp.operands(0).isInstanceOf[Identifier], "Argument to old operator must be an identifier", opapp.pos, c.filename)
          //argTypes(0)
        case PastOperator() =>
          checkTypeError(argTypes.size == 1, "Expect exactly on argument to 'past'", opapp.pos, c.filename)
          checkTypeError(opapp.operands(0).isInstanceOf[Identifier], "Argument to past operator must be an identifier", opapp.pos, c.filename)
          argTypes(0)
        case HistoryOperator() =>
          checkTypeError(argTypes.size == 2, "Expect exactly two arguments to 'history'", opapp.pos, c.filename)
          checkTypeError(opapp.operands(0).isInstanceOf[Identifier], "First argument to history operator must be an identifier", opapp.pos, c.filename)
          checkTypeError(opapp.operands(1).isInstanceOf[IntLit], "Second argument to history must be an integer literal", opapp.pos, c.filename)
          val historyIndex = opapp.operands(1).asInstanceOf[IntLit].value
          checkTypeError(historyIndex > 0, "History index must be non-negative", opapp.pos, c.filename)
          checkTypeError(historyIndex.toInt < 65536, "History index is too large", opapp.pos, c.filename)
          argTypes(0)
        case ITEOp() =>
          checkTypeError(argTypes.size == 3, "Expect exactly three arguments to if-then-else expressions", opapp.pos, c.filename)
          checkTypeError(argTypes(0).isBool, "Condition in if-then-else must be boolean", opapp.pos, c.filename)
          checkTypeError(argTypes(1) == argTypes(2), "Then- and else- expressions in an if-then-else must be of the same type", opapp.pos, c.filename)
          argTypes(1)
        case DistinctOp() =>
          checkTypeError(argTypes.size >= 2, "Expect 2 or more arguments to the distinct operator", opapp.pos, c.filename)
          checkTypeError(argTypes.forall(t => t == argTypes(0)), "All arguments to distinct operator must be the same", opapp.pos, c.filename)
          BooleanType()
      }
    }

    def funcAppType(fapp : FuncApplication) : Type = {
      val funcType1 = typeOf(fapp.e, c)
      lazy val typeErrorMsg = "Cannot apply %s, which is of type %s".format(fapp.e.toString, funcType1.toString)
      checkTypeError(funcType1.isInstanceOf[MapType], typeErrorMsg, fapp.pos, c.filename)
      val funcType = funcType1.asInstanceOf[MapType]
      val argTypes = fapp.args.map(typeOf(_, c))
      checkTypeError(funcType.inTypes == argTypes, "Argument type error in application", fapp.pos, c.filename)
      return funcType.outType
    }

    def lambdaType(lambda : Lambda) : Type = {
      return MapType(lambda.ids.map(_._2), typeOf(lambda.e, c))
    }

    val cachedType = memo.get(e.astNodeId)
    if (cachedType.isEmpty) {
      val typ = e match {
        case i : Identifier =>
          val knownId = c.typeOf(i).isDefined
          checkTypeError(knownId, "Unknown identifier: %s".format(i.name), i.pos, c.filename)
          (c.typeOf(i).get)
        case eId : ExternalIdentifier =>
          val mId = eId.moduleId
          val fId = eId.id
          val moduleTypeOption = c.typeOf(mId)
          checkTypeError(moduleTypeOption.isDefined, "Unknown module: %s".format(mId.toString), mId.pos, c.filename)
          val moduleTypeP = moduleTypeOption.get
          checkTypeError(moduleTypeP.isInstanceOf[ModuleType], "Identifier '%s' is not a module".format(mId.toString), mId.pos, c.filename)
          val moduleType = moduleTypeP.asInstanceOf[ModuleType]
          moduleType.externalTypeMap.get(fId) match {
            case None =>
              raiseTypeError("Unknown external '%s' in module '%s'".format(fId.toString, mId.toString), fId.pos, c.filename)
              UndefinedType()
            case Some(typ) => typ
          }
        case f : FreshLit => f.typ
        case _ : BoolLit => BooleanType()
        case _ : IntLit => IntegerType()
        case _ : StringLit => StringType()
        case fp : FloatLit => FloatType(fp.exp, fp.sig)
        case bv : BitVectorLit => BitVectorType(bv.width)
        case a : ConstArray =>
          val valTyp = typeOf(a.exp, c)
          a.typ match {
            case ArrayType(_, outTyp) =>
              checkTypeError(outTyp == valTyp, "Array type does not match literal type", a.exp.pos, c.filename)
              a.typ
            case _ =>
              raiseTypeError("Expected an array type", a.typ.pos, c.filename)
              UndefinedType()
          }
        case r : Tuple => new TupleType(r.values.map(typeOf(_, c)))
        case opapp : OperatorApplication => opAppType(opapp)
        case fapp : FuncApplication => funcAppType(fapp)
        case lambda : Lambda => lambdaType(lambda)
      }
      memo.put(e.astNodeId, typ)
      return typ
    } else {
      return cachedType.get
    }
  }
}

class ExpressionTypeChecker extends ASTAnalyzer("ExpressionTypeChecker", new ExpressionTypeCheckerPass())  {
  override def pass = super.pass.asInstanceOf[ExpressionTypeCheckerPass]
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val errors = visitModule(module, Set.empty[Utils.TypeError], context)
    if (errors.size > 0) {
      throw new Utils.TypeErrorList(errors.toList)
    }
    return Some(module)
  }
}

class PolymorphicTypeRewriterPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val typeCheckerPass = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  override def rewriteOperator(op : Operator, ctx : Scope) : Option[Operator] = {

    lazy val mappedOp = {
      val reifiedOp = typeCheckerPass.polyOpMap.get(op.astNodeId)
      Utils.assert(reifiedOp.isDefined, "No reified operator available for: " + op.toString)
      reifiedOp
    }
    op match {
      case _ : PolymorphicOperator=>
        mappedOp
      case PolymorphicSelect(_) =>
        mappedOp
      case bv : BVArgOperator => {
        if (bv.w == 0) {
          val width = typeCheckerPass.bvOpMap.get(bv.astNodeId)
          Utils.assert(width.isDefined, "No width available for: " + bv.toString)
          val newOp = bv match {
            case BVLTUOp(_) => width.flatMap((w) => Some(BVLTUOp(w)))
            case BVLEUOp(_) => width.flatMap((w) => Some(BVLEUOp(w)))
            case BVGTUOp(_) => width.flatMap((w) => Some(BVGTUOp(w)))
            case BVGEUOp(_) => width.flatMap((w) => Some(BVGEUOp(w)))
            case BVAndOp(_) => width.flatMap((w) => Some(BVAndOp(w)))
            case BVOrOp(_) => width.flatMap((w) => Some(BVOrOp(w)))
            case BVXorOp(_) => width.flatMap((w) => Some(BVXorOp(w)))
            case BVNotOp(_) => width.flatMap((w) => Some(BVNotOp(w)))
            case BVSignExtOp(_, e) => width.flatMap((w) => Some(BVSignExtOp(w, e)))
            case BVZeroExtOp(_, e) => width.flatMap((w) => Some(BVZeroExtOp(w, e)))
            case BVLeftShiftBVOp(_) => width.flatMap((w) => Some(BVLeftShiftBVOp(w)))
            case BVLRightShiftBVOp(_) => width.flatMap((w) => Some(BVLRightShiftBVOp(w)))
            case BVARightShiftBVOp(_) => width.flatMap((w) => Some(BVARightShiftBVOp(w)))
            case BVUremOp(_) => width.flatMap((w) => Some(BVUremOp(w)))
            case BVSremOp(_) => width.flatMap((w) => Some(BVSremOp(w)))
            case BVUDivOp(_) => width.flatMap((w)=> Some(BVUDivOp(w))) 
            case BVDivOp(_) => width.flatMap((w)=> Some(BVUDivOp(w)))  
            case BVMulOp(_) => width.flatMap((w)=> Some(BVMulOp(w)))  
            case _ => Some(bv)
          }
          newOp match {
            case Some(newOp) =>
              val opWithPos = newOp
              opWithPos.pos = bv.pos
              Some(opWithPos)
            case None =>
              // should never get here.
              None
          }
        } else {
          Some(bv)
        }
      }
      case fp : FloatArgOperator => {
        if (fp.e == 0 && fp.s == 0) {
          val width = typeCheckerPass.fpOpMap.get(fp.astNodeId)
          // val e = width._1
          // val s = width._2
          Utils.assert(width.isDefined, "No exponent and significant sizes available for: " + fp.toString)
          val newOp = fp match {
            case FPLTOp(_,_) => width.flatMap((w) => Some(FPLTOp(w._1, w._2)))
            case FPLEOp(_,_) => width.flatMap((w) => Some(FPLEOp(w._1, w._2)))
            case FPGTOp(_,_) => width.flatMap((w) => Some(FPGTOp(w._1, w._2)))
            case FPGEOp(_,_) => width.flatMap((w) => Some(FPGEOp(w._1, w._2)))
            case FPDivOp(_,_) => width.flatMap((w)=> Some(FPDivOp(w._1, w._2)))  
            case FPMulOp(_,_) => width.flatMap((w)=> Some(FPMulOp(w._1, w._2))) 
            case FPIsNanOp(_,_) => width.flatMap((w)=> Some(FPIsNanOp(w._1, w._2))) 
            case FPUnaryMinusOp(_,_) => width.flatMap((w)=> Some(FPUnaryMinusOp(w._1, w._2))) 
            case _ => Some(fp)
          }
          newOp match {
            case Some(newOp) =>
              val opWithPos = newOp
              opWithPos.pos = fp.pos
              Some(opWithPos)
            case None =>
              // should never get here.
              None
          }
        } else {
          Some(fp)
        }
      }
      case _ => Some(op)
    }
  }
}
class PolymorphicTypeRewriter extends ASTRewriter(
    "PolymorphicTypeRewriter", new PolymorphicTypeRewriterPass())


// Polymorphic type rewriter for synthesis grammars
class PolymorphicGrammarTypeRewriterPass extends RewritePass {
  // Map storing the types of the grammar terms
  // TODO(kkmc): Need to implement a renamer pass to rewrite all the grammar terms
  //             so shadowing doesn't occur if multiple grammars are defined with
  //             the same symbol or nonterminal identifiers
  var typeMap: MutableMap[GrammarTerm, Type] = MutableMap.empty

  /** Returns the type for a grammar term
   *  @term The grammar term
   *  @ctx  Context of the current AST visit
   */
  def getTermType(term: GrammarTerm, ctx: Scope): Type = {
    // Try to find type from the memoized type map
    val typOpt = typeMap.get(term)
    if (!typOpt.isEmpty) return typOpt.get

    // Try to find type from grammar non terminals
    term match {
      case st: SymbolTerm => ctx.get(st.id) match {
        case Some(nt) => nt.typ
        case None => throw new Utils.RuntimeError("Should never get here. Could not find non terminal " + st.id + " type.")
      }
      case _ => throw new Utils.RuntimeError("Should never get here. Could not determine grammar term type of " + term.toString + ".")
    }
  }

  /** Infers the type of the operator application term
   *
   *  @opAppTerm The operator application term whose operator is polymorphic
   */
  def getReifiedOpType(opAppTerm: OpAppTerm): Option[Type] = {
    Utils.assert(opAppTerm.op.isPolymorphic, "Cannot get reified op type of a non polymorphic operator " + opAppTerm.op + ".")
    opAppTerm.op match {
      case AddOp() | SubOp() | LEOp() => typeMap.get(opAppTerm.args(0))
      case _ => None
    }
  }

  /** Returns the operator application term type based on the operator and arguments
   *
   *  TODO(kkmc): Add BVSignExtOp and BVZeroExtOp
   *
   *  @opAppTerm The operator application term to infer the type for
   */
  def getOpAppTermType(opAppTerm: OpAppTerm): Type = {
    Utils.assert(!opAppTerm.op.isPolymorphic, "Cannot infer type of polymorphic operator " + opAppTerm.op.toString + ".")
    opAppTerm.op match {
      case IntAddOp() | IntSubOp() | IntMulOp() | IntUnaryMinusOp() | ITEOp() |
           BVAddOp(_) | BVSubOp(_) | BVMulOp(_) | BVAndOp(_) | BVOrOp(_) |
           BVXorOp(_) | BVNotOp(_) | BVUnaryMinusOp(_) | BVLeftShiftBVOp(_) |
           BVLRightShiftBVOp(_) | BVARightShiftBVOp(_) | BVUremOp(_) | BVSremOp(_) => typeMap(opAppTerm.args(0))
      case IntLTOp() | IntLEOp() | IntGTOp() | IntGEOp() | BVLTOp(_) |
           BVLEOp(_) | BVGTOp(_) | BVGEOp(_) | BVLTUOp(_) | BVLEUOp(_) |
           BVGTUOp(_) | BVGEUOp(_) => BooleanType()
      case _ => throw new Utils.UnimplementedException("Unimplemented OpAppTerm type inference for operator " + opAppTerm.op + ".")
    }
  }

  /** Computes the reified operator for the given OpAppTerm
   *
   *  @opAppTerm Operator application term
   */
  def getReifiedOp(opAppTerm: OpAppTerm): Option[Operator] = {
    // Return None if the operator is already reified reifify the operator
    if (!opAppTerm.op.isPolymorphic) return None

    val op = opAppTerm.op.asInstanceOf[PolymorphicOperator]
    getReifiedOpType(opAppTerm).get match {
      case IntegerType() => Some(ReplacePolymorphicOperators.toInt(op))
      case BitVectorType(w) => Some(ReplacePolymorphicOperators.toBitvector(op, w))
      case _ => throw new Utils.UnimplementedException("Unimplemented reified OpAppTerm Operator translation for " + opAppTerm.op + ".")
    }
  }

  /** Update type map with function application type
   *
   *  @funcAppTerm the function application whose type needs to be memoized
   *  @ctx the current context
   */
  override def rewriteFuncAppTerm(funcAppTerm : FuncAppTerm, ctx : Scope) : Option[FuncAppTerm] = {
    val typ = ctx.typeOf(funcAppTerm.id).get
    typeMap += (funcAppTerm -> typ)
    Some(funcAppTerm)
  }

  /** Rewrite the operator application with the reified type and update the type map
   *
   *  @opAppTerm the operator application whose operator needs to be reified
   *  @ctx the current context
   */
  override def rewriteOpAppTerm(opAppTerm : OpAppTerm, ctx : Scope) : Option[OpAppTerm] = {
    val reifiedOpOpt = getReifiedOp(opAppTerm)
    reifiedOpOpt match {
      case Some(op) => {
        val opAppTermP = OpAppTerm(op, opAppTerm.args)
        val opAppType = getOpAppTermType(opAppTermP)
        typeMap += (opAppTermP -> opAppType)
        Some(opAppTermP)
      }
      case None => Some(opAppTerm)
    }
  }

  /** Update type map with function application type
   *
   *  @defineAppTerm the define-macro application whose type needs to be memoized
   *  @ctx the current context
   */
  override def rewriteDefineAppTerm(defineAppTerm : DefineAppTerm, ctx : Scope) : Option[DefineAppTerm] = {
    val typ = ctx.typeOf(defineAppTerm.id).get
    typeMap += (defineAppTerm -> typ)
    Some(defineAppTerm)
  }

  /** Update type map with the literal term type
   *
   *  @litTerm the term whose type needs to be memoized
   *  @ctx the current context
   */
  override def rewriteLiteralTerm(litTerm : LiteralTerm, ctx : Scope) : Option[LiteralTerm] = {
    typeMap += (litTerm -> litTerm.lit.typeOf)
    Some(litTerm)
  }

  /** Update type map with the symbol term type
   *
   *  @symTerm the term whose type needs to be memoized
   *  @ctx the current context
   */
  override def rewriteSymbolTerm(symTerm : SymbolTerm, ctx : Scope) : Option[SymbolTerm] = {
    val typ = getTermType(symTerm, ctx)
    typeMap += (symTerm -> typ)
    Some(symTerm)
  }

  /** Update type map with the constant term type
   *
   *  @constTerm the term whose type needs to be memoized
   *  @ctx the current context
   */
  override def rewriteConstantTerm(constTerm : ConstantTerm, ctx : Scope) : Option[ConstantTerm] = {
    typeMap += (constTerm -> constTerm.typ)
    Some(constTerm)
  }

}

class PolymorphicGrammarTypeRewriter extends ASTRewriter("PolymorphicGrammarTypeRewriter", new PolymorphicGrammarTypeRewriterPass())