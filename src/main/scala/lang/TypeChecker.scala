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
 * Authors: Norman Mu, Pramod Subramanyan

 * All sorts of type inference and type checking functionality is in here.
 *
 */

package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}
import scala.collection.immutable.{Map => ImmutableMap}
import scala.util.parsing.input.Position


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
  override def applyOnModule( d : TraversalDirection.T, module : Module, in : Unit, context : ScopeMap) : Unit = {
    if (d == TraversalDirection.Up) {
      validateSynonyms(module)
      simplifySynonyms()
    }
  }
  override def applyOnTypeDecl(d : TraversalDirection.T, typDec : TypeDecl, in : Unit, context : ScopeMap) : Unit = {
    if (d == TraversalDirection.Down) {
      typeDeclMap.put(typDec.id, typDec.typ)
    }
  }
  override def applyOnType( d : TraversalDirection.T, typ : Type, in : Unit, context : ScopeMap) : Unit = {
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

  def simplifyType(typ : Type) : Type = {
    typ match {
      case SynonymType(otherName) =>
        simplifyType(typeDeclMap.get(otherName).get)
      case TupleType(fieldTypes) =>
        TupleType(fieldTypes.map(simplifyType(_)))
      case RecordType(fields) =>
        RecordType(fields.map((f) => (f._1, simplifyType(f._2))))
      case MapType(inTypes, outType) =>
        MapType(inTypes.map(simplifyType(_)), simplifyType(outType))
      case ArrayType(inTypes, outType) =>
        ArrayType(inTypes.map(simplifyType(_)), simplifyType(outType))
      case _ =>
        typ
    }
  }

  def simplifySynonyms() {
    var simplified = false
    do {
      simplified = false
      typeDeclMap.foreach {
        case (name, typ) => {
          typ match {
            case SynonymType(otherName) =>
                simplified = true
                typeDeclMap.put(name, simplifyType(typeDeclMap.get(otherName).get))
            case _ =>
                typeDeclMap.put(name, simplifyType(typ))
          }
        }
      }
    } while (simplified)
  }

  def printTypeDeclMap() {
    typeDeclMap.foreach {
      case (name, decl) => println (name.toString + " --> " + decl.toString)
    }
    println("synonyms: " + typeSynonyms)
  }
}

class TypeSynonymFinder extends ASTAnalyzer("TypeSynonymFinder", new TypeSynonymFinderPass())  {
  override def pass = super.pass.asInstanceOf[TypeSynonymFinderPass]
  in = Some(Unit)
}

class TypeSynonymRewriterPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val typeSynonymFinderPass = manager.pass("TypeSynonymFinder").asInstanceOf[TypeSynonymFinder].pass
  override def rewriteType(typ : Type, ctx : ScopeMap) : Option[Type] = {
    val result = typ match {
      case SynonymType(name) => typeSynonymFinderPass.typeDeclMap.get(name)
      case _ => Some(typ)
    }
    return result
  }
}

class TypeSynonymRewriter extends ASTRewriter(
    "TypeSynonymRewriter", new TypeSynonymRewriterPass())

class ForLoopIndexRewriterPass extends RewritePass {
  override def rewriteIdentifierBase(id : IdentifierBase, ctx : ScopeMap) : Option[IdentifierBase] = {
    ctx.get(id).flatMap(
      (expr) => {
        expr match {
          case Scope.ForIndexVar(cId, cTyp) =>
            val forVarId = cId
            forVarId.pos = id.pos
            Some(forVarId)
          case _ => Some(id)
        }
      })
  }
}

class ForLoopIndexRewriter extends ASTRewriter(
    "ForLoopIndexRewriter", new ForLoopIndexRewriterPass())

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
    }
    bvOp.pos = op.pos
    bvOp
  }
  def toType(op : PolymorphicOperator, typ : NumericType) = {
    typ match {
      case intTyp : IntType => toInt(op)
      case bvTyp : BitVectorType => toBitvector(op, bvTyp.width)
    }
  }
  def rewrite(e : Expr, typ : NumericType) : Expr = {
    def r(e : Expr) : Expr = rewrite(e, typ)
    def rs(es : List[Expr])  = es.map(r(_))
    
    e match {
      case i : IdentifierBase => e
      case l : Literal => e
      case Tuple(es) => Tuple(es.map(r(_)))
      case OperatorApplication(op, operands) =>
        val opP = op match {
          case p : PolymorphicOperator => toType(p, typ)
          case _ => op
        }
        OperatorApplication(opP, rs(operands))
      case ArraySelectOperation(expr, indices) =>
        ArraySelectOperation(r(expr), rs(indices))
      case ArrayStoreOperation(expr, indices, value) =>
        ArrayStoreOperation(r(expr), rs(indices), r(value)) 
      case FuncApplication(expr, args) =>
        FuncApplication(r(expr), rs(args))
      case ITE(c, t, f) =>
        ITE(r(c), r(t), r(f))
      case Lambda(args, expr) =>
        Lambda(args, r(expr))
    }
  }
}


class ExpressionTypeCheckerPass extends ReadOnlyPass[List[Utils.TypeError]]
{
  type Memo = MutableMap[IdGenerator.Id, Type]
  var memo : Memo = MutableMap.empty
  type ErrorList = List[Utils.TypeError]
  
  var polyOpMap : MutableMap[IdGenerator.Id, Operator] = MutableMap.empty
  var bvOpMap : MutableMap[IdGenerator.Id, Int] = MutableMap.empty
  
  override def reset() = {
    memo.clear()
    polyOpMap.clear()
  }
  
  override def applyOnExpr(d : TraversalDirection.T, e : Expr, in : ErrorList, ctx : ScopeMap) : ErrorList = {
    if (d == TraversalDirection.Down) {
      try {
        typeOf(e, ctx)
      } catch {
        case p : Utils.TypeError => {
          return (p :: in)
        }
      }
    }
    return in
  }
  
  def checkTypeError(condition: Boolean, msg: => String, pos: => Position, filename: => Option[String]) {
    if (!condition) {
      throw new Utils.TypeError(msg, Some(pos), filename)
    }
  }

  def typeOf(lhs : Lhs, c : ScopeMap) : Type = {
    val cachedType = memo.get(lhs.astNodeId)
    if (cachedType.isDefined) {
      return cachedType.get
    }

    val id = lhs.ident
    val typOpt = c.typeOf(id)
    checkTypeError(typOpt.isDefined, "Unknown variable in LHS: " + id.toString, lhs.pos, c.filename)
    val typ = typOpt.get
    val resultType = lhs match {
      case LhsId(id) => 
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
      case LhsVarSliceSelect(id, slice) =>
        checkTypeError(slice.width.isDefined, "Width of bitvector slice is not constant.", lhs.pos, c.filename)
        BitVectorType(slice.width.get)
    }
    memo.put(lhs.astNodeId, resultType)
    return resultType
  }
  def typeOf(e : Expr, c : ScopeMap) : Type = {
    def polyResultType(op : PolymorphicOperator, argType : Type) : Type = {
      op match {
        case LTOp() | LEOp() | GTOp() | GEOp() => new BoolType()
        case AddOp() | SubOp() | MulOp() => argType
      }
    }
    def opAppType(opapp : OperatorApplication) : Type = {
      val argTypes = opapp.operands.map(typeOf(_, c + opapp))
      opapp.op match {
        case polyOp : PolymorphicOperator => {
          checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          checkTypeError(argTypes(0) == argTypes(1), 
              "Arguments to operator '" + opapp.op.toString + "' must be of the same type. Types of expression '" +
              opapp.toString() + "' are " + argTypes(0).toString() + " and " + argTypes(1).toString() + ".",
              opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isNumeric), "Arguments to operator '" + opapp.op.toString + "' must be of a numeric type.", opapp.pos, c.filename)
          typeOf(opapp.operands(0), c) match {
            case i : IntType =>
              polyOpMap.put(polyOp.astNodeId, ReplacePolymorphicOperators.toInt(polyOp))
              polyResultType(polyOp, i)
            case bv : BitVectorType =>
              polyOpMap.put(polyOp.astNodeId, ReplacePolymorphicOperators.toBitvector(polyOp, bv.width))
              polyResultType(polyOp, bv)
            case _ => throw new Utils.UnimplementedException("Unknown operand type to polymorphic operator '" + opapp.op.toString + "'.")
          }
        }
        case intOp : IntArgOperator => {
          checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isInstanceOf[IntType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Integer.", opapp.pos, c.filename)
          intOp match {
            case IntLTOp() | IntLEOp() | IntGTOp() | IntGEOp() => new BoolType()
            case IntAddOp() | IntSubOp() | IntMulOp() => new IntType()
          }
        }
        case bvOp : BVArgOperator => {
          def numArgs(op : BVArgOperator) : Int = {
            op match {
              case BVNotOp(_) => 1
              case _ => 2
            }
          }
          checkTypeError(argTypes.size == numArgs(bvOp), "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.", opapp.pos, c.filename)
          bvOp match {
            case BVLTOp(_) | BVLEOp(_) | BVGTOp(_) | BVGEOp(_) => new BoolType()
            case BVAddOp(_) | BVSubOp(_) | BVMulOp(_) => new BitVectorType(bvOp.w)
            case BVAndOp(_) | BVOrOp(_) | BVXorOp(_) | BVNotOp(_) =>
              val t = new BitVectorType(argTypes(0).asInstanceOf[BitVectorType].width)
              bvOpMap.put(bvOp.astNodeId, t.width)
              t
          }
        }
        case qOp : QuantifiedBooleanOperator => {
          checkTypeError(argTypes(0).isInstanceOf[BoolType], "Operand to the quantifier '" + qOp.toString + "' must be boolean.", opapp.pos, c.filename)
          BoolType()
        }
        case boolOp : BooleanOperator => {
          boolOp match {
            case NegationOp() => 
              checkTypeError(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument.", opapp.pos, c.filename)
              checkTypeError(argTypes.forall(_.isInstanceOf[BoolType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool. (" + opapp.toString() + ").", opapp.pos, c.filename)
            case _ => 
              checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
              checkTypeError(argTypes.forall(_.isInstanceOf[BoolType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool.", opapp.pos, c.filename)
          }
          BoolType()
        }
        case cmpOp : ComparisonOperator => {
          checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          checkTypeError(argTypes(0) == argTypes(1), "Arguments to operator '" + opapp.op.toString + "' must be of the same type.", opapp.pos, c.filename)
          BoolType()
        }
        case tOp : TemporalOperator => new TemporalType()
        case extrOp : ExtractOp => {
          extrOp match {
            case ConstExtractOp(slice) => {
              checkTypeError(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument.", opapp.pos, c.filename)
              checkTypeError(argTypes(0).isInstanceOf[BitVectorType], "Operand to operator '" + opapp.op.toString + "' must be of type BitVector.", opapp.pos, c.filename) 
              checkTypeError(argTypes(0).asInstanceOf[BitVectorType].width > slice.hi, "Operand to operator '" + opapp.op.toString + "' must have width > "  + slice.hi.toString + ".", opapp.pos, c.filename) 
              checkTypeError(slice.hi >= slice.lo, "High-operand must be greater than or equal to low operand for operator '" + opapp.op.toString + "'.", opapp.pos, c.filename) 
              checkTypeError(slice.hi >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.", opapp.pos, c.filename) 
              checkTypeError(slice.lo >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.", opapp.pos, c.filename) 
              BitVectorType(slice.hi - slice.lo + 1)
            }
            case VarExtractOp(slice) => {
              checkTypeError(slice.width.isDefined, "Slice width is not constant", extrOp.pos, c.filename)
              BitVectorType(slice.width.get)
            }
          }
        }
        case ConcatOp() => {
          checkTypeError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          checkTypeError(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.", opapp.pos, c.filename)
          new BitVectorType(argTypes(0).asInstanceOf[BitVectorType].width + argTypes(1).asInstanceOf[BitVectorType].width)
        }
        case RecordSelect(field) => {
          checkTypeError(argTypes.size == 1, "Record select operator must have exactly one operand.", opapp.pos, c.filename)
          argTypes(0) match {
            case recType : RecordType =>
              val typOption = recType.fieldType(field)
              checkTypeError(!typOption.isEmpty, "Field '" + field.toString + "' does not exist in " + recType.toString(), opapp.pos, c.filename)
              typOption.get
            case tupType : TupleType =>
              val indexS = field.name.substring(1)
              checkTypeError(indexS.forall(Character.isDigit), "Tuple fields must be integers preceded by an underscore.", opapp.pos, c.filename)
              val indexI = indexS.toInt
              checkTypeError(indexI >= 1 && indexI <= tupType.numFields, "Invalid tuple index: " + indexS, opapp.pos, c.filename)
              tupType.fieldTypes(indexI-1)
            case _ =>
              checkTypeError(false, "Argument to record select operator must be of type record.", opapp.pos, c.filename)
              new BoolType()
          }
        }
      }
    }
    
    def arraySelectType(arrSel : ArraySelectOperation) : Type = {
      checkTypeError(typeOf(arrSel.e, c).isInstanceOf[ArrayType], "Type error in the array operand of select operation.", arrSel.pos, c.filename)
      val indTypes = arrSel.index.map(typeOf(_, c))
      val arrayType = typeOf(arrSel.e, c).asInstanceOf[ArrayType]
      lazy val message = "Array index type error. Expected: (" + 
                          Utils.join(arrayType.inTypes.map((t) => t.toString), ", ") + "). Got: (" +
                          Utils.join(indTypes.map((t) => t.toString), ", ") + ")."
      checkTypeError(arrayType.inTypes == indTypes, message, arrSel.pos, c.filename)
      return arrayType.outType
    }
    
    def arrayStoreType(arrStore : ArrayStoreOperation) : Type = {
      checkTypeError(typeOf(arrStore.e, c).isInstanceOf[ArrayType], "Type error in the array operand of store operation.", arrStore.pos, c.filename)
      val indTypes = arrStore.index.map(typeOf(_, c))
      val valueType = typeOf(arrStore.value, c)
      val arrayType = typeOf(arrStore.e, c).asInstanceOf[ArrayType]
      checkTypeError(arrayType.inTypes == indTypes, "Array index type error.", arrStore.pos, c.filename)
      checkTypeError(arrayType.outType == valueType, "Array update value type error.", arrStore.pos, c.filename)
      return arrayType
    }
    
    def funcAppType(fapp : FuncApplication) : Type = {
      checkTypeError(typeOf(fapp.e, c).isInstanceOf[MapType], "Type error in function application (not a function).", fapp.pos, c.filename)
      val funcType = typeOf(fapp.e,c ).asInstanceOf[MapType]
      val argTypes = fapp.args.map(typeOf(_, c))
      checkTypeError(funcType.inTypes == argTypes, "Type error in function application (argument type error).", fapp.pos, c.filename)
      return funcType.outType
    }
    
    def iteType(ite : ITE) : Type = {
      checkTypeError(typeOf(ite.e, c).isBool, "Type error in ITE condition operand.", ite.pos, c.filename)
      checkTypeError(typeOf(ite.t, c) == typeOf(ite.f, c), "ITE operand types don't match.", ite.pos, c.filename)
      return typeOf(ite.t, c)
    }
    
    def lambdaType(lambda : Lambda) : Type = {
      return MapType(lambda.ids.map(_._2), typeOf(lambda.e, c))
    }
    
    val cachedType = memo.get(e.astNodeId)
    if (cachedType.isEmpty) {
      val typ = e match {
        case i : IdentifierBase =>
          checkTypeError(c.typeOf(i).isDefined, "Unknown variable: " + i.name, i.pos, c.filename)
          (c.typeOf(i).get)
        case b : BoolLit => new BoolType()
        case i : IntLit => new IntType()
        case bv : BitVectorLit => new BitVectorType(bv.width)
        case r : Tuple => new TupleType(r.values.map(typeOf(_, c)))
        case opapp : OperatorApplication => opAppType(opapp)
        case arrSel : ArraySelectOperation => arraySelectType(arrSel)
        case arrStore : ArrayStoreOperation => arrayStoreType(arrStore)
        case fapp : FuncApplication => funcAppType(fapp)
        case ite : ITE => iteType(ite)
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
  override def visit(module : Module) : Option[Module] = {
    val errors = visitModule(module, List.empty[Utils.TypeError])
    if (errors.size > 0) {
      throw new Utils.TypeErrorList(errors)
    }
    return Some(module)
  }
}

class ModuleTypeCheckerPass extends ReadOnlyPass[List[ModuleError]]
{
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  override def applyOnStatement(d : TraversalDirection.T, st : Statement, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Up) {
      in
    } else {
      st match {
        case AssertStmt(e, id) =>
          val eType = exprTypeChecker.typeOf(e, context)
          if (!(eType.isBool || eType.isTemporal)) {
            ModuleError("Assertion expression must be of Boolean or Temporal type.", st.position) :: in
          } else {
            in
          }
        case AssumeStmt(e, id) =>
          val eType = exprTypeChecker.typeOf(e, context)
          if (!eType.isBool) {
            ModuleError("Assumption must be Boolean.", st.position) :: in
          } else {
            in
          }
        case HavocStmt(id) =>
          if (!context.doesNameExist(id)) {
            ModuleError("Unknown identifier in havoc statement.", st.position) :: in
          } else {
            in
          }
        case AssignStmt(lhss, rhss) =>
          var ret = in

          for ((lh, rh) <- lhss zip rhss) {
            val lhType = exprTypeChecker.typeOf(lh, context)
            val rhType = exprTypeChecker.typeOf(rh, context)
            if (!lhType.matches(rhType)) {
              lh.ident.toString
              ret = ModuleError("%s expected type %s but received type %s.".format(lh.ident.toString, lhType.toString, rhType.toString), st.position) :: ret
            }
          }

          val l1 = lhss.length
          val l2 = rhss.length

          if (l1 != l2) {
            ret = ModuleError("Assignment expected %d expressions but received %d.".format(l1, l2), st.position) :: ret
          }

          ret

        case IfElseStmt(cond, _, _) =>
          val cType = exprTypeChecker.typeOf(cond, context)
          if (!cType.isBool) {
            ModuleError("Condition in if statement must be of type boolean.", st.position) :: in
          } else {
            in
          }
        case ForStmt(_, range, _) =>
          range._1 match {
            case i: IntLit =>
              range._2 match {
                case j: IntLit =>
                  if (i.value > j.value) {
                    ModuleError("Range lower bound must be less than upper bound.", st.position) :: in
                  } else {
                    in
                  }
                case _ =>
                  ModuleError("Range lower and upper bounds must be of same type.", st.position) :: in
              }
            case b: BitVectorLit =>
              range._2 match {
                case c: BitVectorLit =>
                  if (b.value > c.value) {
                    ModuleError("Range lower bound must be less than upper bound.", st.position) :: in
                  } else if (b.width != c.width) {
                    ModuleError("Range lower and upper bounds must be of same width", st.position) :: in
                  } else {
                    in
                  }
                case _ =>
                  ModuleError("Range lower and upper bounds must be of same type.", st.position) :: in
              }
          }
        case CaseStmt(body) =>
          body.foldLeft(in) {
            (acc, c) => {
              var cType = exprTypeChecker.typeOf(c._1, context)
              if (!cType.isBool) {
                ModuleError("Case clause must be of type boolean.", st.position) :: acc
              } else {
                acc
              }
            }
          }
        case ProcedureCallStmt(id, callLhss, args) =>
          var ret = in
          if (context.module.isEmpty) {
            ret = ModuleError("Procedure does not exist.", st.position) :: ret
          }
          val procOption = context.module.get.decls.find((p) => p.isInstanceOf[ProcedureDecl] && p.asInstanceOf[ProcedureDecl].id == id)

          if (procOption.isEmpty) {
            ret = ModuleError("Procedure does not exist.", st.position) :: ret
          }

          val proc = procOption.get.asInstanceOf[ProcedureDecl]
          for ((param, arg) <- proc.sig.inParams zip args) {
            var (pId, pType) = param.asInstanceOf[(Identifier, Type)]
            var aType = exprTypeChecker.typeOf(arg.asInstanceOf[Expr], context)
            if (!pType.matches(aType)) {
              ret = ModuleError("Parameter %s expected argument of type %s but received type %s.".format(pId.nam, pType.toString, aType.toString), st.position) :: ret
            }
          }

          var l1 = proc.sig.inParams.length
          var l2 = args.length

          if (l1 != l2) {
            ret = ModuleError("Procedure expected %d arguments but received %d.".format(l1, l2), st.position) :: ret
          }

          for ((retval, lh) <- proc.sig.outParams zip callLhss) {
            val rType = retval.asInstanceOf[(Identifier, Type)]._2
            val lType = exprTypeChecker.typeOf(lh, context)
            if (!rType.matches(lType)) {
              ret = ModuleError("Left hand variable %s expected return value of type %s but received type %s."
                .format(lh.toString, lType.toString, rType.toString), st.position) :: ret
            }
          }

          l1 = proc.sig.inParams.length
          l2 = args.length

          if (l1 != l2) {
            ret = ModuleError("Left hand side expected %d return values but received %d.".format(l1, l2), st.position) :: ret
          }
          ret
        case SkipStmt() | ModuleCallStmt(_) => in
      }
    }
  }
}

class ModuleTypeChecker extends ASTAnalyzer("ModuleTypeChecker", new ModuleTypeCheckerPass())  {
  override def visit(module : Module) : Option[Module] = {
    val out = visitModule(module, List.empty[ModuleError])
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position))
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}

class PolymorphicTypeRewriterPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val typeCheckerPass = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  override def rewriteOperator(op : Operator, ctx : ScopeMap) : Option[Operator] = {
    
    op match {
      case p : PolymorphicOperator => {
        val reifiedOp = typeCheckerPass.polyOpMap.get(p.astNodeId)
        Utils.assert(reifiedOp.isDefined, "No reified operator available for: " + p.toString)
        assert (reifiedOp.get.pos == p.pos)
        reifiedOp
      }
      case bv : BVArgOperator => {
        if (bv.w == 0) {
          val width = typeCheckerPass.bvOpMap.get(bv.astNodeId)
          Utils.assert(width.isDefined, "No width available for: " + bv.toString)
          val newOp = bv match {
            case BVAndOp(_) => width.flatMap((w) => Some(BVAndOp(w)))
            case BVOrOp(_) => width.flatMap((w) => Some(BVOrOp(w)))
            case BVXorOp(_) => width.flatMap((w) => Some(BVXorOp(w)))
            case BVNotOp(_) => width.flatMap((w) => Some(BVNotOp(w)))
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
      case _ => Some(op)
    }
  }
}
class PolymorphicTypeRewriter extends ASTRewriter(
    "PolymorphicTypeRewriter", new PolymorphicTypeRewriterPass())
  
