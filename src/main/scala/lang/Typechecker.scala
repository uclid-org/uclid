package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.immutable.{Map => ImmutableMap}

class TypecheckPass extends ReadOnlyPass[Unit]
{
  type MemoKey = (Expr, ScopeMap)
  type Memo = MutableMap[MemoKey, Type]
  var memo : Memo = MutableMap.empty
  
  type PolymorphicOpMapKey = (IdGenerator.Id, Operator)
  type PolymorphicOpMap = MutableMap[IdGenerator.Id, Operator]
  var polyOpMap : PolymorphicOpMap = MutableMap.empty
  
  override def reset() = {
    memo.clear()
    polyOpMap.clear()
  }
  
  override def applyOnExpr(d : TraversalDirection.T, e : Expr, in : Unit, ctx : ScopeMap) : Unit = {
    typeOf(e, ctx)
  }
  
  def typeOf(e : Expr, c : ScopeMap) : Type = {
    def polyToInt(op : PolymorphicOperator) : IntArgOperator = {
      op match {
        case LTOp() => IntLTOp()
        case LEOp() => IntLEOp()
        case GTOp() => IntGTOp()
        case GEOp() => IntGEOp()
        case AddOp() => IntAddOp()
        case SubOp() => IntSubOp()
        case MulOp() => IntMulOp()
      }
    }
    def polyToBV(op : PolymorphicOperator, w : Int) : BVArgOperator = {
      op match {
        case LTOp() => BVLTOp(w)
        case LEOp() => BVLEOp(w)
        case GTOp() => BVGTOp(w)
        case GEOp() => BVGEOp(w)
        case AddOp() => BVAddOp(w)
        case SubOp() => BVSubOp(w)
        case MulOp() => BVMulOp(w)
      }
    }
    def opAppType(opapp : UclOperatorApplication) : Type = {
      val argTypes = opapp.operands.map(typeOf(_, c))
      opapp.op match {
        case polyOp : PolymorphicOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes(0) == argTypes(1), "Arguments to operator '" + opapp.op.toString + "' must be of the same type.")
          Utils.assert(argTypes.forall(_.isNumeric), "Arguments to operator '" + opapp.op.toString + "' must be of a numeric type.")
          typeOf(opapp.operands(0), c) match {
            case i : IntType =>
              polyOpMap.put(polyOp.astNodeId, polyToInt(polyOp))
              i
            case bv : BitVectorType =>
              polyOpMap.put(polyOp.astNodeId, polyToBV(polyOp, bv.width))
              bv
            case _ => throw new Utils.UnimplementedException("Unknown operand type to polymorphic operator '" + opapp.op.toString + "'.")
          }
        }
        case intOp : IntArgOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[IntType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Integer.")
          new IntType()
        }
        case bvOp : BVArgOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.")
          typeOf(opapp.operands(0), c)
        }
        case boolOp : BooleanOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[BoolType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool.")
          new BoolType()
        }
        case cmpOp : ComparisonOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes(0) == argTypes(1), "Arguments to operator '" + opapp.op.toString + "' must be of the same type.")
          new BoolType()
        }
        case tOp : TemporalOperator => new TemporalType()
        case ExtractOp(hi, lo) => {
          Utils.assert(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument.")
          Utils.assert(argTypes(0).isInstanceOf[BitVectorType], "Operand to operator '" + opapp.op.toString + "' must be of type BitVector.") 
          Utils.assert(argTypes(0).asInstanceOf[BitVectorType].width > hi.value.toInt, "Operand to operator '" + opapp.op.toString + "' must have width > "  + hi.value.toString + ".") 
          Utils.assert(hi.value >= lo.value , "High-operand must be greater than or equal to low operand for operator '" + opapp.op.toString + "'.") 
          Utils.assert(hi.value.toInt >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.") 
          Utils.assert(lo.value.toInt >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.") 
          new BitVectorType(hi.value.toInt - lo.value.toInt + 1)
        }
        case ConcatOp() => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.")
          new BitVectorType(argTypes(0).asInstanceOf[BitVectorType].width + argTypes(1).asInstanceOf[BitVectorType].width)
        }
        case RecordSelect(field) => {
          Utils.assert(argTypes.size == 1, "Record select operator must have exactly one operand.")
          Utils.assert(argTypes(0).isInstanceOf[RecordType], "Argument to record select operator must be of type record.")
          val recordType = argTypes(0).asInstanceOf[RecordType]
          val typOption = recordType.fieldType(field)
          Utils.assert(!typOption.isEmpty, "Field '" + field.toString + "' does not exist in record.")
          return typOption.get
        }
      }
    }
    
    def arraySelectType(arrSel : UclArraySelectOperation) : Type = {
      Utils.assert(typeOf(arrSel.e, c).isInstanceOf[ArrayType], "Type error in the array operand of select operation.")
      val indTypes = arrSel.index.map(typeOf(_, c))
      val arrayType = typeOf(arrSel.e, c).asInstanceOf[ArrayType]
      Utils.assert(arrayType.inTypes == indTypes, "Array index type error.")
      return arrayType.outType
    }
    
    def arrayStoreType(arrStore : UclArrayStoreOperation) : Type = {
      Utils.assert(typeOf(arrStore.e, c).isInstanceOf[ArrayType], "Type error in the array operand of store operation.")
      val indTypes = arrStore.index.map(typeOf(_, c))
      val valueType = typeOf(arrStore.value, c)
      val arrayType = typeOf(arrStore.e, c).asInstanceOf[ArrayType]
      Utils.assert(arrayType.inTypes == indTypes, "Array index type error.")
      Utils.assert(arrayType.outType == valueType, "Array update value type error.")
      return arrayType
    }
    
    def funcAppType(fapp : UclFuncApplication) : Type = {
      Utils.assert(typeOf(fapp.e, c).isInstanceOf[MapType], "Type error in function application (not a function).")
      val funcType = typeOf(fapp.e,c ).asInstanceOf[MapType]
      val argTypes = fapp.args.map(typeOf(_, c))
      Utils.assert(funcType.inTypes == argTypes, "Type error in function application (argument type error).")
      return funcType.outType
    }
    
    def iteType(ite : UclITE) : Type = {
      Utils.assert(typeOf(ite.e, c).isBool, "Type error in ITE condition operand.")
      Utils.assert(typeOf(ite.t, c) == typeOf(ite.f, c), "ITE operand types don't match.")
      return typeOf(ite.t, c)
    }
    
    def lambdaType(lambda : UclLambda) : Type = {
      return MapType(lambda.ids.map(_._2), typeOf(lambda.e, c))
    }
    
    val cachedType = memo.get((e,c))
    if (cachedType.isEmpty) {
      val typ = e match {
        case i : Identifier => (c.typeOf(i).get)
        case b : BoolLit => new BoolType()
        case i : IntLit => new IntType()
        case bv : BitVectorLit => new BitVectorType(bv.width)
        case r : Record => throw new Utils.UnimplementedException("Need to implement anonymous record types.")
        case opapp : UclOperatorApplication => opAppType(opapp)
        case arrSel : UclArraySelectOperation => arraySelectType(arrSel)
        case arrStore : UclArrayStoreOperation => arrayStoreType(arrStore)
        case fapp : UclFuncApplication => funcAppType(fapp)
        case ite : UclITE => iteType(ite)
        case lambda : UclLambda => lambdaType(lambda)
      }
      memo.put((e,c), typ)
      return typ
    } else {
      return cachedType.get
    }
  }
}

class Typechecker extends ASTAnalyzer("Typechecker", new TypecheckPass())  {
  override def pass = super.pass.asInstanceOf[TypecheckPass]
  in = Some(Unit)
}

class PolymorphicTypeRewriterPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val typeCheckerPass = manager.pass("Typechecker").asInstanceOf[Typechecker].pass
  override def rewriteOperator(op : Operator, ctx : ScopeMap) : Option[Operator] = {
    
    op match {
      case p : PolymorphicOperator => {
        val reifiedOp = typeCheckerPass.polyOpMap.get(p.astNodeId)
        Utils.assert(!reifiedOp.isEmpty, "No reified operator available!")
        println("replacing " + p.toString + " with " + reifiedOp.toString)
        reifiedOp
      }
      case _ => Some(op)
    }
  }
}
class PolymorphicTypeRewriter extends ASTRewriter(
    "PolymorphicTypeRewriter", new PolymorphicTypeRewriterPass())
