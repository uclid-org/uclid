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
 * Author: Pramod Subramanyan
 *
 * UCLID AST to SMT AST converter.
 *
 */
package uclid
package smt

object Converter {
  type SymbolTable = Map[lang.Identifier, smt.Symbol]
  
  def typeToSMT(typ : lang.Type) : smt.Type = {
    typ match {
      case lang.UninterpretedType(id) =>
        smt.UninterpretedType(id.name)
      case lang.IntType() => 
        smt.IntType()
      case lang.BoolType() => 
        smt.BoolType()
      case lang.BitVectorType(w) => 
        smt.BitVectorType(w)
      case lang.MapType(inTypes,outType) => 
        smt.MapType(inTypes.map(typeToSMT(_)), typeToSMT(outType)) 
      case lang.ArrayType(inTypes,outType) => 
        smt.ArrayType(inTypes.map(typeToSMT(_)), typeToSMT(outType)) 
      case lang.TupleType(argTypes) => 
        smt.TupleType(argTypes.map(typeToSMT(_)))
      case lang.RecordType(fields) =>
        smt.RecordType(fields.map((f) => (f._1.toString, typeToSMT(f._2))))
      case lang.EnumType(ids) =>
        smt.EnumType(ids.map(_.name))
      case lang.SynonymType(typ) =>
        throw new Utils.UnimplementedException("Synonym types must have been eliminated by now.")
      case lang.UndefinedType() | lang.ProcedureType(_, _) | lang.ExternalType(_, _) |
           lang.ModuleInstanceType(_) | lang.ModuleType(_, _, _, _, _) | lang.TemporalType() =>
        throw new AssertionError("Type '" + typ.toString + "' not expected here.")
    }
  }
  
  def opToSMT(op : lang.Operator) : smt.Operator = {
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
      case lang.ConstExtractOp(slice) => return smt.BVExtractOp(slice.hi, slice.lo)
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
      // Quantifiers
      case lang.ForallOp(vs) => return smt.ForallOp(vs.map(v => smt.Symbol(v._1.toString, smt.Converter.typeToSMT(v._2))))
      case lang.ExistsOp(vs) => return smt.ExistsOp(vs.map(v => smt.Symbol(v._1.toString, smt.Converter.typeToSMT(v._2))))
      // Polymorphic operators are not allowed.
      case p : lang.PolymorphicOperator => 
        throw new Utils.RuntimeError("Polymorphic operators must have been eliminated by now.")
      case _ => throw new Utils.UnimplementedException("Operator not supported yet: " + op.toString)
    }
  }

  def exprToSMT(expr : lang.Expr, scope : lang.Scope) : smt.Expr = {
    def toSMT(expr : lang.Expr) : smt.Expr = exprToSMT(expr, scope)
    def toSMTs(es : List[lang.Expr]) : List[smt.Expr] = es.map((e : lang.Expr) => toSMT(e))
    def idToSMT(id : lang.Identifier) : smt.Expr = {
      val typ = scope.typeOf(id).get
      smt.Symbol(id.name, typeToSMT(typ))
    }
    
     expr match {
       case id : lang.Identifier => idToSMT(id) 
       case lang.IntLit(n) => smt.IntLit(n)
       case lang.BoolLit(b) => smt.BooleanLit(b)
       case lang.BitVectorLit(bv, w) => smt.BitVectorLit(bv, w)
       case lang.Tuple(args) => smt.MakeTuple(toSMTs(args))
       case lang.OperatorApplication(op,args) =>
         return smt.OperatorApplication(opToSMT(op), args.map((a) => exprToSMT(a, scope + lang.OperatorApplication(op, args))))
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
         throw new Utils.UnimplementedException("Lambdas are not yet implemented.")
    }
  }
  
  def exprToSMT(expr : lang.Expr, symbolTable : Map[lang.Identifier, Expr], scope : lang.Scope) : smt.Expr = {
    def toSMT(expr : lang.Expr) : smt.Expr = exprToSMT(expr, symbolTable, scope)
    def toSMTs(es : List[lang.Expr]) : List[smt.Expr] = es.map((e : lang.Expr) => toSMT(e))
     expr match {
       case id : lang.Identifier =>
         if (scope.typeOf(id).isEmpty) {
           println("Trouble for id: " + id.toString)
         }
         val typ = scope.typeOf(id).get
         if (scope.isQuantifierVar(id)) {
           Symbol(id.name, typeToSMT(typ))
         } else {
           symbolTable(id)
         }
       case lang.IntLit(n) => smt.IntLit(n)
       case lang.BoolLit(b) => smt.BooleanLit(b)
       case lang.BitVectorLit(bv, w) => smt.BitVectorLit(bv, w)
       case lang.Tuple(args) => smt.MakeTuple(toSMTs(args))
       case opapp : lang.OperatorApplication =>
         return smt.OperatorApplication(
             opToSMT(opapp.op), opapp.operands.map((a) => exprToSMT(a, symbolTable, scope + opapp)))
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
         throw new Utils.UnimplementedException("Lambdas are not yet implemented.")
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
}
