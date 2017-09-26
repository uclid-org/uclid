package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}
import scala.collection.immutable.{Map => ImmutableMap}
import uclid.smt.ExpressionAnalyzer

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

class BitVectorIndexRewriterPass extends RewritePass {
  override def rewriteLHS(lhs : Lhs, ctx : ScopeMap) : Option[Lhs] = {
    lhs match {
      case LhsSliceSelect(id, slice) =>
        val hiL = lang.IntLit(slice.hi)
        val loL = lang.IntLit(slice.lo)
        val subL = lang.OperatorApplication(lang.IntSubOp(), List(hiL, loL))
        val width = lang.OperatorApplication(lang.IntAddOp(), List(subL, lang.IntLit(1)))
        val isCnst = ExpressionAnalyzer.isExprConst(width, ctx)
        println("width: " + width.toString + "; isCnst: " + isCnst.toString)
      case _ =>
    }
    Some(lhs)
  }
}

class BitVectorIndexRewriter extends ASTRewriter(
    "BitVectorIndexRewriter", new BitVectorIndexRewriterPass())

class ExpressionTypeCheckerPass extends ReadOnlyPass[Unit]
{
  type Memo = MutableMap[IdGenerator.Id, Type]
  var memo : Memo = MutableMap.empty
  
  var polyOpMap : MutableMap[IdGenerator.Id, Operator] = MutableMap.empty
  var bvOpMap : MutableMap[IdGenerator.Id, Int] = MutableMap.empty
  
  override def reset() = {
    memo.clear()
    polyOpMap.clear()
  }
  
  override def applyOnExpr(d : TraversalDirection.T, e : Expr, in : Unit, ctx : ScopeMap) : Unit = {
    typeOf(e, ctx)
  }
  
  def typeOf(lhs : Lhs, c : ScopeMap) : Type = {
    val cachedType = memo.get(lhs.astNodeId)
    if (cachedType.isDefined) {
      return cachedType.get
    }

    val id = lhs.ident
    val typOpt = c.typeOf(id)
    Utils.checkParsingError(typOpt.isDefined, "Unknown variable in LHS: " + id.toString, lhs.pos, c.filename)
    val typ = typOpt.get
    val resultType = lhs match {
      case LhsId(id) => 
        typ
      case LhsArraySelect(id, indices) =>
        Utils.checkParsingError(typ.isArray, "Lhs variable in array index operation must be of type array: " + id.toString, lhs.pos, c.filename)
        val indexTypes = indices.map(typeOf(_, c))
        val arrTyp = typ.asInstanceOf[ArrayType]
        lazy val indexTypString = "(" + Utils.join(indexTypes.map(_.toString), ", ") + ")"
        lazy val inTypString = "(" + Utils.join(arrTyp.inTypes.map(_.toString), ", ") + ")"
        Utils.checkParsingError(arrTyp.inTypes == indexTypes, "Invalid index types. Expected: " + inTypString + "; got: " + indexTypString, lhs.pos, c.filename)
        arrTyp.outType
      case LhsRecordSelect(id, fields) =>
        Utils.checkParsingError(typ.isProduct, "Lhs variable in record select operation must be a product type: " + id.toString, lhs.pos, c.filename)
        val prodType = typ.asInstanceOf[ProductType]
        val fieldType = prodType.nestedFieldType(fields)
        lazy val fieldTypeString = Utils.join(fields.map(_.toString), ".")
        Utils.checkParsingError(fieldType.isDefined, "Field does not exist: " + fieldTypeString, lhs.pos, c.filename)
        fieldType.get
      case LhsSliceSelect(id, slice) =>
        Utils.checkParsingError(typ.isBitVector, "Lhs variable in bitvector slice update must be a bitvector: " + id.toString, lhs.pos, c.filename)
        val bvType = typ.asInstanceOf[BitVectorType]
        Utils.checkParsingError(bvType.isValidSlice(slice), "Invalid slice: " + slice.toString, slice.pos, c.filename)
        BitVectorType(slice.width)
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
    def polyToInt(op : PolymorphicOperator) : IntArgOperator = {
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
      return intOp
    }
    def polyToBV(op : PolymorphicOperator, w : Int) : BVArgOperator = {
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
      return bvOp
    }
    def opAppType(opapp : OperatorApplication) : Type = {
      val argTypes = opapp.operands.map(typeOf(_, c))
      opapp.op match {
        case polyOp : PolymorphicOperator => {
          Utils.checkParsingError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          Utils.checkParsingError(argTypes(0) == argTypes(1), 
              "Arguments to operator '" + opapp.op.toString + "' must be of the same type. Types of expression '" +
              opapp.toString() + "' are " + argTypes(0).toString() + " and " + argTypes(1).toString() + ".",
              opapp.pos, c.filename)
          Utils.checkParsingError(argTypes.forall(_.isNumeric), "Arguments to operator '" + opapp.op.toString + "' must be of a numeric type.", opapp.pos, c.filename)
          typeOf(opapp.operands(0), c) match {
            case i : IntType =>
              polyOpMap.put(polyOp.astNodeId, polyToInt(polyOp))
              polyResultType(polyOp, i)
            case bv : BitVectorType =>
              polyOpMap.put(polyOp.astNodeId, polyToBV(polyOp, bv.width))
              polyResultType(polyOp, bv)
            case _ => throw new Utils.UnimplementedException("Unknown operand type to polymorphic operator '" + opapp.op.toString + "'.")
          }
        }
        case intOp : IntArgOperator => {
          Utils.checkParsingError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          Utils.checkParsingError(argTypes.forall(_.isInstanceOf[IntType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Integer.", opapp.pos, c.filename)
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
          Utils.checkParsingError(argTypes.size == numArgs(bvOp), "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          Utils.checkParsingError(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.", opapp.pos, c.filename)
          bvOp match {
            case BVLTOp(_) | BVLEOp(_) | BVGTOp(_) | BVGEOp(_) => new BoolType()
            case BVAddOp(_) | BVSubOp(_) | BVMulOp(_) => new BitVectorType(bvOp.w)
            case BVAndOp(_) | BVOrOp(_) | BVXorOp(_) | BVNotOp(_) =>
              val t = new BitVectorType(argTypes(0).asInstanceOf[BitVectorType].width)
              bvOpMap.put(bvOp.astNodeId, t.width)
              t
          }
        }
        case boolOp : BooleanOperator => {
          boolOp match {
            case NegationOp() => 
              Utils.checkParsingError(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument.", opapp.pos, c.filename)
              Utils.checkParsingError(argTypes.forall(_.isInstanceOf[BoolType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool. (" + opapp.toString() + ").", opapp.pos, c.filename)
            case _ => 
              Utils.checkParsingError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
              Utils.checkParsingError(argTypes.forall(_.isInstanceOf[BoolType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool.", opapp.pos, c.filename)
          }
          new BoolType()
        }
        case cmpOp : ComparisonOperator => {
          Utils.checkParsingError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          Utils.checkParsingError(argTypes(0) == argTypes(1), "Arguments to operator '" + opapp.op.toString + "' must be of the same type.", opapp.pos, c.filename)
          new BoolType()
        }
        case tOp : TemporalOperator => new TemporalType()
        case ExtractOp(slice) => {
          Utils.checkParsingError(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument.", opapp.pos, c.filename)
          Utils.checkParsingError(argTypes(0).isInstanceOf[BitVectorType], "Operand to operator '" + opapp.op.toString + "' must be of type BitVector.", opapp.pos, c.filename) 
          Utils.checkParsingError(argTypes(0).asInstanceOf[BitVectorType].width > slice.hi, "Operand to operator '" + opapp.op.toString + "' must have width > "  + slice.hi.toString + ".", opapp.pos, c.filename) 
          Utils.checkParsingError(slice.hi >= slice.lo, "High-operand must be greater than or equal to low operand for operator '" + opapp.op.toString + "'.", opapp.pos, c.filename) 
          Utils.checkParsingError(slice.hi >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.", opapp.pos, c.filename) 
          Utils.checkParsingError(slice.lo >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.", opapp.pos, c.filename) 
          new BitVectorType(slice.hi - slice.lo + 1)
        }
        case ConcatOp() => {
          Utils.checkParsingError(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.", opapp.pos, c.filename)
          Utils.checkParsingError(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.", opapp.pos, c.filename)
          new BitVectorType(argTypes(0).asInstanceOf[BitVectorType].width + argTypes(1).asInstanceOf[BitVectorType].width)
        }
        case RecordSelect(field) => {
          Utils.checkParsingError(argTypes.size == 1, "Record select operator must have exactly one operand.", opapp.pos, c.filename)
          argTypes(0) match {
            case recType : RecordType =>
              val typOption = recType.fieldType(field)
              Utils.checkParsingError(!typOption.isEmpty, "Field '" + field.toString + "' does not exist in " + recType.toString(), opapp.pos, c.filename)
              typOption.get
            case tupType : TupleType =>
              val indexS = field.name.substring(1)
              Utils.checkParsingError(indexS.forall(Character.isDigit), "Tuple fields must be integers preceded by an underscore.", opapp.pos, c.filename)
              val indexI = indexS.toInt
              Utils.checkParsingError(indexI >= 1 && indexI <= tupType.numFields, "Invalid tuple index: " + indexS, opapp.pos, c.filename)
              tupType.fieldTypes(indexI-1)
            case _ =>
              Utils.checkParsingError(false, "Argument to record select operator must be of type record.", opapp.pos, c.filename)
              new BoolType()
          }
        }
      }
    }
    
    def arraySelectType(arrSel : ArraySelectOperation) : Type = {
      Utils.checkParsingError(typeOf(arrSel.e, c).isInstanceOf[ArrayType], "Type error in the array operand of select operation.", arrSel.pos, c.filename)
      val indTypes = arrSel.index.map(typeOf(_, c))
      val arrayType = typeOf(arrSel.e, c).asInstanceOf[ArrayType]
      Utils.checkParsingError(arrayType.inTypes == indTypes, "Array index type error.", arrSel.pos, c.filename)
      return arrayType.outType
    }
    
    def arrayStoreType(arrStore : ArrayStoreOperation) : Type = {
      Utils.checkParsingError(typeOf(arrStore.e, c).isInstanceOf[ArrayType], "Type error in the array operand of store operation.", arrStore.pos, c.filename)
      val indTypes = arrStore.index.map(typeOf(_, c))
      val valueType = typeOf(arrStore.value, c)
      val arrayType = typeOf(arrStore.e, c).asInstanceOf[ArrayType]
      Utils.checkParsingError(arrayType.inTypes == indTypes, "Array index type error.", arrStore.pos, c.filename)
      Utils.checkParsingError(arrayType.outType == valueType, "Array update value type error.", arrStore.pos, c.filename)
      return arrayType
    }
    
    def funcAppType(fapp : FuncApplication) : Type = {
      Utils.checkParsingError(typeOf(fapp.e, c).isInstanceOf[MapType], "Type error in function application (not a function).", fapp.pos, c.filename)
      val funcType = typeOf(fapp.e,c ).asInstanceOf[MapType]
      val argTypes = fapp.args.map(typeOf(_, c))
      Utils.checkParsingError(funcType.inTypes == argTypes, "Type error in function application (argument type error).", fapp.pos, c.filename)
      return funcType.outType
    }
    
    def iteType(ite : ITE) : Type = {
      Utils.checkParsingError(typeOf(ite.e, c).isBool, "Type error in ITE condition operand.", ite.pos, c.filename)
      Utils.checkParsingError(typeOf(ite.t, c) == typeOf(ite.f, c), "ITE operand types don't match.", ite.pos, c.filename)
      return typeOf(ite.t, c)
    }
    
    def lambdaType(lambda : Lambda) : Type = {
      return MapType(lambda.ids.map(_._2), typeOf(lambda.e, c))
    }
    
    val cachedType = memo.get(e.astNodeId)
    if (cachedType.isEmpty) {
      val typ = e match {
        case i : IdentifierBase =>
          Utils.checkParsingError(c.typeOf(i).isDefined, "Unknown variable: " + i.name, i.pos, c.filename)
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
  in = Some(Unit)
}

class ModuleTypeCheckerPass extends ReadOnlyPass[Unit]
{
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  override def applyOnStatement(d : TraversalDirection.T, st : Statement, in : Unit, context : ScopeMap) : Unit = {
    st match {
      case AssertStmt(e) => 
        val eType = exprTypeChecker.typeOf(e, context)
        Utils.checkParsingError(eType.isBool || eType.isTemporal, "Assertion expression must be of Boolean or Temporal type.", st.pos, context.filename)
      case AssumeStmt(e) =>
        val eType = exprTypeChecker.typeOf(e, context)
        Utils.checkParsingError(eType.isBool, "Assumption must be Boolean.", st.pos, context.filename)
      case HavocStmt(id) =>
        Utils.checkParsingError(context.doesNameExist(id), "Unknown identifier in havoc statement.", st.pos, context.filename)
      case AssignStmt(lhss, rhss) =>
        val lhsTypes = lhss.map(exprTypeChecker.typeOf(_, context))
        val rhsTypes = rhss.map(exprTypeChecker.typeOf(_, context))
        val typesMatch = (lhsTypes zip rhsTypes).map((p) => p._1.matches(p._2))
        Utils.checkParsingError(typesMatch.forall((b) => b), "LHS/RHS types do not match.", st.pos, context.filename)
      case _ =>
        // Ignore the rest.
    }
  }
}

class ModuleTypeChecker extends ASTAnalyzer("ModuleTypeChecker", new ModuleTypeCheckerPass())  {
  override def pass = super.pass.asInstanceOf[ModuleTypeCheckerPass]
  in = Some(Unit)
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
  
