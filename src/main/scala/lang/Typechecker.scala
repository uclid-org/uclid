package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.immutable.{Map => ImmutableMap}

class TypecheckingVisitor extends FoldingASTVisitor[Unit]
{
  type Context = ImmutableMap[Identifier, Type]
  type MemoKey = (Expr, Context)
  type Memo = MutableMap[MemoKey, Type]
  var memo : Memo = MutableMap.empty
  var context : Context = ImmutableMap.empty
  
  var moduleProcedures : List[UclProcedureDecl] = List.empty
  var moduleTypes : List[UclTypeDecl] = List.empty
  var moduleStateVars : List[UclStateVarDecl] = List.empty
  var moduleInputVars : List[UclInputVarDecl] = List.empty
  var moduleOutputVars : List[UclOutputVarDecl] = List.empty
  var moduleConstants : List[UclConstantDecl] = List.empty
  var moduleFunctions : List[UclFunctionDecl] = List.empty
  
  override def applyOnModule(d : TraversalDirection.T, m : Module, in : Unit) : Unit = {
    if (d == TraversalDirection.Down) {
      // FIXME: Make sure identifiers are not repeated in procedures, types, state vars, etc.
      moduleProcedures = moduleProcedures ++ (m.decls.collect({ case p : UclProcedureDecl => p }))
      moduleTypes = moduleTypes ++ (m.decls.collect({case t : UclTypeDecl => t }))
      moduleStateVars = moduleStateVars ++ (m.decls.collect({case s : UclStateVarDecl => s }))
      moduleInputVars = moduleInputVars ++ (m.decls.collect({case i : UclInputVarDecl => i }))
      moduleOutputVars = moduleOutputVars ++ (m.decls.collect({case o : UclOutputVarDecl => o}))
      moduleFunctions = moduleFunctions ++ (m.decls.collect({case f : UclFunctionDecl => f}))
      
      context = ImmutableMap.empty
      context = moduleStateVars.foldRight(context)((sv, ctx) => ctx + (sv.id -> sv.typ))
      context = moduleInputVars.foldRight(context)((iv, ctx) => ctx + (iv.id -> iv.typ))
      context = moduleOutputVars.foldRight(context)((ov, ctx) => ctx + (ov.id -> ov.typ))
      context = moduleConstants.foldRight(context)((c, ctx) => ctx + (c.id -> c.typ))
      context = moduleFunctions.foldRight(context)((f, ctx) => ctx + (f.id -> f.sig.typ))
    } else {
      moduleProcedures = List.empty
      moduleTypes = List.empty
      moduleStateVars = List.empty
      moduleInputVars = List.empty
      moduleOutputVars = List.empty
      moduleConstants = List.empty
      moduleFunctions = List.empty
      context = ImmutableMap.empty
    }
  }
  
  override def applyOnProcedure(d : TraversalDirection.T, p : UclProcedureDecl, in : Unit) : Unit = {
    if (d == TraversalDirection.Down) {
      context = p.sig.inParams.foldRight(context)((arg, ctx) => ctx + (arg._1 -> arg._2))
      context = p.sig.outParams.foldRight(context)((arg, ctx) => ctx + (arg._1 -> arg._2))
      context = p.decls.foldRight(context)((v, ctx) => ctx + (v.id -> v.typ))
    } else {
      context = p.sig.inParams.foldRight(context)((arg, ctx) => ctx - arg._1)
      context = p.sig.outParams.foldRight(context)((arg, ctx) => ctx - arg._1)
      context = p.decls.foldRight(context)((v, ctx) => ctx - v.id)
    }
  }
  override def applyOnExpr(d : TraversalDirection.T, e : Expr, in : Unit) : Unit = {
    typeOf(e, context)
  }
  
  def typeOf(e : Expr, c : Context) : Type = {
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
              polyOp.reifiedOp = Some(polyToInt(polyOp))
              i
            case bv : BitVectorType =>
              polyOp.reifiedOp = Some(polyToBV(polyOp, bv.width))
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
      val lambdaCtx = lambda.ids.foldRight(c)((arg, ctx) => ctx + (arg._1 -> arg._2))
      return MapType(lambda.ids.map(_._2), typeOf(lambda.e, lambdaCtx))
    }
    
    val cachedType = memo.get((e,c))
    if (cachedType.isEmpty) {
      val typ = e match {
        case i : Identifier => (c.get(i).get)
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

class Typechecker () {
  val visitor = new FoldingVisitor(new TypecheckingVisitor())
  def check(m : Module) = {
    visitor.visitModule(m, Unit)
  }
  def rewrite(m : Module) : Module = {
    return (new RewritingVisitor(new RewritingASTVisitor {
      override def rewriteOperator(op : Operator) : Option[Operator] = { 
        op match {
          case p : PolymorphicOperator => {
            Utils.assert(!p.reifiedOp.isEmpty, "No reified operator available.")
            println("replacing " + p.toString + " with " + p.reifiedOp.toString)
            p.reifiedOp
          }
          case _ => Some(op)
        }
      }
    })).visitModule(m).get
  }
}

object Typechecker {
  def checkAndRewrite(m : Module) : Module = {
    val tc = new Typechecker()
    tc.check(m)
    return tc.rewrite(m)
  }
}
