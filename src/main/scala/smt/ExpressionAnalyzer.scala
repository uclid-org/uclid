package uclid
package smt

import scala.collection.mutable.Map
import scala.collection.immutable.Set

object ExpressionAnalyzer {
  type SymbolTable = Map[lang.Identifier, smt.Symbol]
  
  def typeToSMT(typ : lang.Type) : smt.Type = {
    typ match {
      case lang.IntType() => return smt.IntType()
      case lang.BoolType() => return smt.BoolType()
      case lang.BitVectorType(w) => return smt.BitVectorType(w)
      case lang.MapType(inTypes,outType) => 
        Utils.assert(inTypes.forall(_.isPrimitive) && outType.isPrimitive, 
            "Only maps with primitive types are implemented.")
        return smt.MapType(inTypes.map(typeToSMT(_)), typeToSMT(outType)) 
      case lang.ArrayType(inTypes,outType) => 
        Utils.assert(inTypes.forall(_.isPrimitive) && outType.isPrimitive, 
            "Only arrays with primitive types are implemented.")
        return smt.ArrayType(inTypes.map(typeToSMT(_)), typeToSMT(outType)) 
      case lang.TupleType(argTypes) => 
        return smt.TupleType(argTypes.map(typeToSMT(_)))
      case lang.RecordType(fields) =>
        return smt.RecordType(fields.map((f) => (f._1.toString, typeToSMT(f._2))))
      case _ => throw new Utils.UnimplementedException("Unimplemented type: " + typ.toString)
    }
  }
  
  def operatorToSMT(op : lang.Operator) : smt.Operator = {
    op match {
      // Integer operators.
      case lang.IntLTOp() => return smt.IntLTOp
      case lang.IntLEOp() => return smt.IntLEOp
      case lang.IntGTOp() => return smt.IntGTOp
      case lang.IntGEOp() => return smt.IntGEOp
      case lang.IntAddOp() => return smt.IntAddOp
      case lang.IntSubOp() => return smt.IntSubOp
      case lang.IntMulOp() => return smt.IntMulOp
      // Bitvector operators.
      case lang.BVLTOp(w) => return smt.BVLTOp(w)
      case lang.BVLEOp(w) => return smt.BVLEOp(w)
      case lang.BVGTOp(w) => return smt.BVGTOp(w)
      case lang.BVGEOp(w) => return smt.BVGEOp(w)
      case lang.BVAddOp(w) => return smt.BVAddOp(w)
      case lang.BVSubOp(w) => return smt.BVSubOp(w)
      case lang.BVMulOp(w) => return smt.BVMulOp(w)
      case lang.BVAndOp(w) => return smt.BVAndOp(w)
      case lang.BVOrOp(w) => return smt.BVOrOp(w)
      case lang.BVXorOp(w) => return smt.BVXorOp(w)
      case lang.BVNotOp(w) => return smt.BVNotOp(w)
      case lang.ExtractOp(slice) => return smt.BVExtractOp(slice.hi, slice.lo)
      // Boolean operators.
      case lang.ConjunctionOp() => return smt.ConjunctionOp
      case lang.DisjunctionOp() => return smt.DisjunctionOp
      case lang.IffOp() => return smt.IffOp
      case lang.ImplicationOp() => return smt.ImplicationOp
      case lang.NegationOp() => return smt.NegationOp
      // Comparison operators.
      case lang.EqualityOp() => return smt.EqualityOp
      case lang.InequalityOp() => return smt.InequalityOp
      // Record select.
      case lang.RecordSelect(r) => return smt.RecordSelectOp(r.name)
      // Polymorphic operators are not allowed.
      case p : lang.PolymorphicOperator => 
        throw new Utils.RuntimeError("Polymorphic operators must have been eliminated by now.")
      case _ => 
        throw new Utils.UnimplementedException("Operator not supported yet: " + op.toString)
    }
    
  }
  
  def exprToSMT(expr : lang.Expr, scope : lang.ScopeMap) : smt.Expr = {
    def toSMT(e : lang.Expr) : smt.Expr = exprToSMT(e, scope)
    def toSMTs(es : List[lang.Expr]) : List[smt.Expr] = es.map(toSMT(_))
    
     expr match {
       case lang.Identifier(id) => 
         val typ = scope.typeOf(expr.asInstanceOf[lang.Identifier]).get
         smt.Symbol(id, typeToSMT(typ))
       case lang.IntLit(n) => smt.IntLit(n)
       case lang.BoolLit(b) => smt.BooleanLit(b)
       case lang.BitVectorLit(bv, w) => smt.BitVectorLit(bv, w)
       case lang.Tuple(args) => smt.MakeTuple(toSMTs(args))
       case lang.OperatorApplication(op,args) =>
         return smt.OperatorApplication(operatorToSMT(op), toSMTs(args))
       case lang.ArraySelectOperation(a,index) => 
         return smt.ArraySelectOperation(toSMT(a), toSMTs(index))
       case lang.ArrayStoreOperation(a,index,value) => 
         return smt.ArrayStoreOperation(toSMT(a), toSMTs(index), toSMT(value)) 
       case lang.FuncApplication(f,args) => f match {
         case lang.Identifier(id) => 
           return smt.FunctionApplication(toSMT(f), toSMTs(args)) 
         case lang.Lambda(idtypes,le) => 
           // FIXME: beta sub
           throw new Utils.UnimplementedException("Beta reduction is not implemented yet.")
         case _ => 
           throw new Utils.RuntimeError("Should never get here.")
       }
       case lang.ITE(cond,t,f) =>
         return smt.ITE(toSMT(cond), toSMT(t), toSMT(f))
       case lang.Lambda(ids,le) => 
         throw new Utils.UnimplementedException("Lambda's are not yet implemented.")
       case _ => 
         throw new Utils.UnimplementedException("Unimplemented expression: " + expr.toString)
    }
  }
  
  def renameSymbols(expr : smt.Expr, renamerFn : ((String, smt.Type) => String)) : smt.Expr = {
    def rename(e : smt.Expr) = renameSymbols(e, renamerFn)
    expr match {
      case Symbol(name,typ) =>
        return Symbol(renamerFn(name, typ), typ) 
      case OperatorApplication(op,operands) =>
        return OperatorApplication(op, operands.map(rename(_)))
      case ArraySelectOperation(e, index) =>
        return ArraySelectOperation(rename(e), index.map(rename(_)))
      case ArrayStoreOperation(e, index, value) =>
        return ArrayStoreOperation(rename(e), index.map(rename(_)), rename(value))
      case FunctionApplication(e, args) =>
        return FunctionApplication(rename(e), args.map(rename(_)))
      case ITE(e,t,f) =>
        return ITE(rename(e), rename(t), rename(f))
      case Lambda(syms,e) =>
        return Lambda(syms.map((sym) => Symbol(renamerFn(sym.id, sym.typ), sym.typ)), rename(e))
      case IntLit(_) | BitVectorLit(_,_) | BooleanLit(_) =>  
        return expr
    }
  }
  
  def isExprConst(expr : lang.Expr, scope : lang.ScopeMap) : Boolean = {
    val smtExpr = exprToSMT(expr, scope)
    val smtExpr1 = renameSymbols(smtExpr, (s, t) => s + "$1")
    val smtExpr2 = renameSymbols(smtExpr, (s, t) => s + "$2")
    println("expr1: " + smtExpr1.toString)
    println("expr2: " + smtExpr2.toString)
    return smtExpr1 == smtExpr2
  }
}
