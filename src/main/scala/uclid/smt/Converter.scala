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
 * Author: Pramod Subramanyan
 *
 * UCLID AST to SMT AST converter.
 *
 */
package uclid
package smt

object Converter {
  type SymbolTable = SymbolicSimulator.SymbolTable
  type FrameTable = SymbolicSimulator.FrameTable

  def typeToSMT(typ : lang.Type) : smt.Type = {
    typ match {
      case lang.UninterpretedType(id) =>
        smt.UninterpretedType(id.name)
      case lang.IntegerType() =>
        smt.IntType
      case lang.FloatType(e,s) =>
        smt.FltType(e,s)
      case lang.RealType() =>
        smt.RealType
      case lang.BooleanType() =>
        smt.BoolType
      case lang.StringType() =>
        throw new Utils.RuntimeError("String types cannot be converted.")
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
      case dt : lang.DataType =>
        smt.DataType(dt.id.name, dt.constructors.map(c => ConstructorType(c._1.name, c._2.map(s => {
          s._2 match {
            case lang.SynonymType(id2) if id2 == dt.id => (s._1.name, smt.SelfReferenceType(id2.name))
            case _ => (s._1.name, typeToSMT(s._2))
          }
        }), smt.SelfReferenceType(dt.id.name))))
      case lang.ConstructorType(id, inTypes, outTyp) =>
        smt.ConstructorType(id.name, inTypes.map(t => (t._1.name, typeToSMT(t._2))), typeToSMT(outTyp))
      case lang.TesterType(id, inType) =>
        smt.TesterType(id.name, typeToSMT(inType))
      case t : lang.SynonymType =>
        throw new Utils.UnimplementedException("Synonym types must have been eliminated by now. " + t + " from " + t.pos + " was not!")
      case lang.UndefinedType() | lang.ProcedureType(_, _) | lang.ExternalType(_, _) |
           lang.ModuleInstanceType(_) | lang.ModuleType(_, _, _, _, _, _, _, _, _) | lang.GroupType(_) =>
        throw new AssertionError("Type '" + typ.toString + "' not expected here.")
    }
  }

  def smtToType(typ : smt.Type) : lang.Type = {
    typ match {
      case smt.UninterpretedType(name) =>
        lang.UninterpretedType(lang.Identifier(name))
      case smt.IntType =>
        lang.IntegerType()
      case smt.RealType =>
        lang.RealType()
      case smt.BoolType =>
        lang.BooleanType()
      case smt.BitVectorType(w) =>
        lang.BitVectorType(w)
      case smt.MapType(inTypes, outType) =>
        lang.MapType(inTypes.map(smtToType(_)), smtToType(outType))
      case smt.ArrayType(inTypes,outType) =>
        lang.ArrayType(inTypes.map(smtToType(_)), smtToType(outType))
      case smt.TupleType(argTypes) =>
        lang.TupleType(argTypes.map(smtToType(_)))
      case smt.RecordType(fields) =>
        lang.RecordType(fields.map((f) => (lang.Identifier(f._1), smtToType(f._2))))
      case smt.EnumType(ids) =>
        lang.EnumType(ids.map(lang.Identifier(_)))
      case dt: smt.DataType =>
        lang.DataType(lang.Identifier(dt.id), dt.cstors.map(cstor => (lang.Identifier(cstor.id), cstor.inTypes.map(slctor => (lang.Identifier(slctor._1), smtToType(slctor._2))))))
      case _ =>
        throw new AssertionError("Type '" + typ.toString + "' not expected here.")
    }
  }

  def opToSMT(op : lang.Operator, ctx : lang.Scope, past : Int, idToSMT : ((lang.Identifier, lang.Scope, Int) => smt.Expr)) : smt.Operator = {
    op match {
      // Integer operators.
      case lang.IntLTOp() => smt.IntLTOp
      case lang.IntLEOp() => smt.IntLEOp
      case lang.IntGTOp() => smt.IntGTOp
      case lang.IntGEOp() => smt.IntGEOp
      case lang.IntAddOp() => smt.IntAddOp
      case lang.IntSubOp() => smt.IntSubOp
      case lang.IntMulOp() => smt.IntMulOp
      case lang.IntDivOp() => smt.IntDivOp
      case lang.IntUnaryMinusOp() => smt.IntSubOp
      // Real operators.
      case lang.RealLTOp() => smt.RealLTOp
      case lang.RealLEOp() => smt.RealLEOp
      case lang.RealGTOp() => smt.RealGTOp
      case lang.RealGEOp() => smt.RealGEOp
      case lang.RealAddOp() => smt.RealAddOp
      case lang.RealSubOp() => smt.RealSubOp
      case lang.RealMulOp() => smt.RealMulOp
      case lang.RealDivOp() => smt.RealDivOp
      case lang.RealUnaryMinusOp() => smt.RealSubOp
      // Bitvector operators.
      case lang.BVLTOp(w) => smt.BVLTOp(w)
      case lang.BVLEOp(w) => smt.BVLEOp(w)
      case lang.BVGTOp(w) => smt.BVGTOp(w)
      case lang.BVGEOp(w) => smt.BVGEOp(w)
      case lang.BVLTUOp(w) => smt.BVLTUOp(w)
      case lang.BVLEUOp(w) => smt.BVLEUOp(w)
      case lang.BVGTUOp(w) => smt.BVGTUOp(w)
      case lang.BVGEUOp(w) => smt.BVGEUOp(w)
      case lang.BVAddOp(w) => smt.BVAddOp(w)
      case lang.BVSubOp(w) => smt.BVSubOp(w)
      case lang.BVMulOp(w) => smt.BVMulOp(w)
      case lang.BVDivOp(w) => smt.BVDivOp(w)
      case lang.BVUDivOp(w) => smt.BVUDivOp(w)
      case lang.BVUnaryMinusOp(w) => smt.BVMinusOp(w)
      case lang.BVAndOp(w) => smt.BVAndOp(w)
      case lang.BVOrOp(w) => smt.BVOrOp(w)
      case lang.BVUremOp(w) => smt.BVUremOp(w)
      case lang.BVSremOp(w) => smt.BVSremOp(w)  
      case lang.BVXorOp(w) => smt.BVXorOp(w)
      case lang.BVNotOp(w) => smt.BVNotOp(w)
      case lang.ConstExtractOp(slice) => smt.BVExtractOp(slice.hi, slice.lo)
      case lang.BVSignExtOp(w, e) => smt.BVSignExtOp(w, e)
      case lang.BVZeroExtOp(w, e) => smt.BVZeroExtOp(w, e)
      case lang.BVLeftShiftBVOp(w) => smt.BVLeftShiftBVOp(w)
      case lang.BVLRightShiftBVOp(w) => smt.BVLRightShiftBVOp(w)
      case lang.BVARightShiftBVOp(w) => smt.BVARightShiftBVOp(w)
      // float operators
      case lang.FPAddOp(e,s) => smt.FPAddOp(e,s)
      case lang.FPMulOp(e,s) => smt.FPMulOp(e,s)
      case lang.FPDivOp(e,s) => smt.FPDivOp(e,s)
      case lang.FPSubOp(e,s) => smt.FPSubOp(e,s)
      case lang.FPLTOp(e,s) => smt.FPLTOp(e,s)
      case lang.FPGTOp(e,s) => smt.FPGTOp(e,s)
      case lang.FPLEOp(e,s) => smt.FPLEOp(e,s)
      case lang.FPGEOp(e,s) => smt.FPGEOp(e,s)
      case lang.FPIsNanOp(e,s) => smt.FPIsNanOp(e,s)
      case lang.FPUnaryMinusOp(e,s) => smt.FPMinusOp(e,s)
      // Boolean operators.
      case lang.ConjunctionOp() => smt.ConjunctionOp
      case lang.DisjunctionOp() => smt.DisjunctionOp
      case lang.IffOp() => smt.IffOp
      case lang.ImplicationOp() => smt.ImplicationOp
      case lang.NegationOp() => smt.NegationOp
      // Comparison operators.
      case lang.EqualityOp() => smt.EqualityOp
      case lang.InequalityOp() => smt.InequalityOp
      case lang.DistinctOp() => smt.InequalityOp
      case lang.BV2SignedIntOp() => smt.BV2SignedIntOp()
      case lang.BV2UnsignedIntOp() => smt.BV2UnsignedIntOp()
      case lang.Int2BVOp(w) => smt.Int2BVOp(w)
      // Record select.
      case lang.RecordSelect(r) => smt.RecordSelectOp(r.name)
      // Quantifiers
      case lang.ForallOp(vs, ps) =>
        val args = vs.map(v => smt.Symbol(v._1.toString, smt.Converter.typeToSMT(v._2)))
        val pats = ps.map(qs => qs.map(q => smt.Converter._exprToSMT(q, ctx, past, idToSMT)))
        smt.ForallOp(args, pats)
      case lang.ExistsOp(vs, ps) =>
        val args = vs.map(v => smt.Symbol(v._1.toString, smt.Converter.typeToSMT(v._2)))
        val pats = ps.map(qs => qs.map(q => smt.Converter._exprToSMT(q, ctx, past, idToSMT)))
        smt.ExistsOp(args, pats)
      case lang.ITEOp() => smt.ITEOp
      case lang.HyperSelect(i) => smt.HyperSelectOp(i)
      // Polymorphic operators are not allowed.
      case _ : lang.PolymorphicOperator =>
        throw new Utils.RuntimeError("Polymorphic operators must have been eliminated by now.")
      case _ => throw new Utils.UnimplementedException("Operator not supported yet: " + op.toString)
    }
  }

  def smtToOp(op : smt.Operator, args : List[smt.Expr]) : lang.Operator = {
    op match {
      // Integer operators.
      case smt.IntLTOp => lang.IntLTOp()
      case smt.IntLEOp => lang.IntLEOp()
      case smt.IntGTOp => lang.IntGTOp()
      case smt.IntGEOp => lang.IntGEOp()
      case smt.IntAddOp => lang.IntAddOp()
      case smt.IntSubOp => 
        if (args.size == 1) lang.IntUnaryMinusOp()
        else                lang.IntSubOp()
      case smt.IntMulOp => lang.IntMulOp()
      // Bitvector operators.
      case smt.BVLTOp(w) => lang.BVLTOp(w)
      case smt.BVLEOp(w) => lang.BVLEOp(w)
      case smt.BVGTOp(w) => lang.BVGTOp(w)
      case smt.BVGEOp(w) => lang.BVGEOp(w)
      case smt.BVLTUOp(w) => lang.BVLTUOp(w)
      case smt.BVLEUOp(w) => lang.BVLEUOp(w)
      case smt.BVGTUOp(w) => lang.BVGTUOp(w)
      case smt.BVGEUOp(w) => lang.BVGEUOp(w)
      case smt.BVAddOp(w) => lang.BVAddOp(w)
      case smt.BVSubOp(w) => lang.BVSubOp(w)
      case smt.BVMulOp(w) => lang.BVMulOp(w)
      case smt.BVMinusOp(w) => lang.BVUnaryMinusOp(w)
      case smt.BVAndOp(w) => lang.BVAndOp(w)
      case smt.BVOrOp(w) => lang.BVOrOp(w)
      case smt.BVXorOp(w) => lang.BVXorOp(w)
      case smt.BVNotOp(w) => lang.BVNotOp(w)
      case smt.BVUremOp(w) => lang.BVUremOp(w)
      case smt.BVSremOp(w) => lang.BVSremOp(w)  
      case smt.BVExtractOp(hi, lo) => lang.ConstExtractOp(lang.ConstBitVectorSlice(hi, lo))
      case smt.BVConcatOp(_) => lang.ConcatOp()
      case smt.BVZeroExtOp(w, e) => lang.BVZeroExtOp(w, e)
      case smt.BVLeftShiftBVOp(w) => lang.BVLeftShiftBVOp(w)
      // Boolean operators.
      case smt.ConjunctionOp => lang.ConjunctionOp()
      case smt.DisjunctionOp => lang.DisjunctionOp()
      case smt.IffOp => lang.IffOp()
      case smt.ImplicationOp => lang.ImplicationOp()
      case smt.NegationOp => lang.NegationOp()
      // Comparison operators.
      case smt.EqualityOp => lang.EqualityOp()
      case smt.InequalityOp => lang.InequalityOp()
      // Record select.
      case smt.RecordSelectOp(name) => lang.RecordSelect(lang.Identifier(name))
      // if then else
      case smt.ITEOp => lang.ITEOp()
      // Quantifiers
      case smt.ForallOp(vs, ps) =>
        val varsP = vs.map(v => (lang.Identifier(v.id), smt.Converter.smtToType(v.symbolTyp)))
        val patternsP = ps.map(qs => qs.map(q => smt.Converter.smtToExpr(q)))
        lang.ForallOp(varsP, patternsP)
      case smt.ExistsOp(vs, ps) =>
        val varsP = vs.map(v => (lang.Identifier(v.id), smt.Converter.smtToType(v.symbolTyp)))
        val patternsP = ps.map(qs => qs.map(q => smt.Converter.smtToExpr(q)))
        lang.ExistsOp(varsP, patternsP)
      case _ => throw new Utils.UnimplementedException("Operator not supported yet: " + op.toString)
    }
  }

  // Helper function to read from a record.
  def recordSelect(field : String, rec : smt.Expr) = {
    smt.OperatorApplication(smt.RecordSelectOp(field), List(rec))
  }
  // Helper function to update a record.
  def recordUpdate(field : String, rec : smt.Expr, newVal : smt.Expr) = {
    smt.OperatorApplication(smt.RecordUpdateOp(field), List(rec, newVal))
  }
  
  def _exprToSMT(expr : lang.Expr, scope : lang.Scope, past : Int, idToSMT : ((lang.Identifier, lang.Scope, Int) => smt.Expr)) : smt.Expr = {
    def toSMT(expr : lang.Expr, scope : lang.Scope, past : Int) : smt.Expr = _exprToSMT(expr, scope, past, idToSMT)
    def toSMTs(es : List[lang.Expr], scope : lang.Scope, past : Int) : List[smt.Expr] = es.map((e : lang.Expr) => toSMT(e, scope, past))

    expr match {
      case id : lang.Identifier => idToSMT(id, scope, past)
      case unit : lang.UninterpretedTypeLiteral => idToSMT(unit.toIdentifier, scope, past)
      case lang.IntLit(n) => smt.IntLit(n)
      case lang.BoolLit(b) => smt.BooleanLit(b)
      case lang.BitVectorLit(bv, w) => smt.BitVectorLit(bv, w)
      case lang.FloatLit(i,f,e,s) => 
        smt.FloatLit(i,f,e,s)
      case lang.RealLit(i,f) => smt.RealLit(i,f)
      case lang.ConstArray(value, arrTyp) =>
        smt.ConstArray(toSMT(value, scope, past), typeToSMT(arrTyp).asInstanceOf[ArrayType])
      case lang.ConstRecord(fs) => 
        smt.ConstRecord(fs.map(f => (f._1.toString, toSMT(f._2, scope, past))))
      case lang.StringLit(_) => throw new Utils.RuntimeError("Strings are not supported in smt.Converter")
      case lang.Tuple(args) => smt.MakeTuple(toSMTs(args, scope, past))
      case opapp : lang.OperatorApplication =>
        val op = opapp.op
        val args = opapp.operands
        op match {
          case lang.OldOperator() | lang.PastOperator() =>
            toSMT(args(0), scope, 1)
          case lang.HistoryOperator() =>
            toSMT(args(0), scope, args(1).asInstanceOf[lang.IntLit].value.toInt)
          case lang.GetNextValueOp() =>
            toSMT(args(0), scope, past)
          case lang.ConcatOp() =>
            val scopeWOpApp = scope + opapp
            val argsInSMT = toSMTs(args, scopeWOpApp, past)
            Utils.assert(argsInSMT.length == 2, "Bitvector concat must have two arguments.")
            Utils.assert(argsInSMT.forall(_.typ.isBitVector), "Argument to bitvector concat must be a bitvector.")
            val width = argsInSMT.foldLeft(0)((acc, ai) => ai.typ.asInstanceOf[BitVectorType].width + acc)
            smt.OperatorApplication(smt.BVConcatOp(width), argsInSMT)
          case lang.ArraySelect(index) =>
            val arr = toSMT(args(0), scope, past)
            smt.ArraySelectOperation(arr, toSMTs(index, scope, past))
          case lang.ArrayUpdate(index, value) =>
            val arr = toSMT(args(0), scope, past)
            val data = toSMT(value, scope, past)
            smt.ArrayStoreOperation(arr, toSMTs(index, scope, past), data)
          case lang.RecordUpdate(fieldid, value) =>
            val record = toSMT(args(0), scope, past)
            val data = toSMT(value, scope, past)
            recordUpdate(fieldid.toString, record, data)
          case _ =>
            val scopeWOpApp = scope + opapp
            val argsInSMT = toSMTs(args, scopeWOpApp, past)
            smt.OperatorApplication(opToSMT(op, scope + opapp, past, idToSMT), argsInSMT)
        }
      case lang.FuncApplication(f,args) => f match {
        case lang.Identifier(_) =>
          smt.FunctionApplication(toSMT(f, scope, past), toSMTs(args, scope, past))
        case lang.Lambda(_,_) =>
          // FIXME: beta sub
          throw new Utils.UnimplementedException("Beta reduction is not implemented yet.")
        case _ =>
           throw new Utils.RuntimeError("Should never get here.")
      }
      case lang.QualifiedIdentifierApplication(qid, exprs) => {
        lang.ULContext.stripMkTupleFunction(qid.toString) match {
          case Some(s) => {
            lang.ULContext.postTypeMap.get(s).get match {
              case lang.RecordType(fields) => {
                val exprsInSMT = exprs.map(e => _exprToSMT(e, scope, past, idToSMT))
                val recordFields = fields.map(f => f._1.toString)
                smt.ConstRecord(recordFields zip exprsInSMT)
              }
              case _ => throw new Utils.RuntimeError("Type conversion for " + s + " not supported in QualifiedIdentifierApplication.")
            }
          }
          case None => throw new Utils.RuntimeError(qid.toString + " not found in postTypeMap.")
        }
      }
      // Unimplemented operators.
      case lang.Lambda(_,_) =>
        throw new Utils.UnimplementedException("Lambdas are not yet implemented.")
      // Troublesome operators.
      case lang.FreshLit(_) =>
        throw new Utils.RuntimeError("Should never get here. FreshLits must have been rewritten by this point.")
      case lang.ExternalIdentifier(_, _) =>
        throw new Utils.RuntimeError("Should never get here. ExternalIdentifiers must have been rewritten by this point.")
      case lang.QualifiedIdentifierApplication(_, _) | lang.QualifiedIdentifier(_, _) | lang.IndexedIdentifier(_, _) => 
        throw new Utils.RuntimeError("ERROR: Qualified and Indexed Identifiers are currently not supported")
      case lang.LetExpr(_, _) =>
        throw new Utils.UnimplementedException("ERROR: SMT expr generation for QualifiedIdentifier and IndexedIdentifier is currently not supported")
    }
  }

  def exprToSMT(expr : lang.Expr, scope : lang.Scope) : smt.Expr = {
    def idToSMT(id : lang.Identifier, scope : lang.Scope, past : Int) : smt.Expr = {
      val typ = scope.typeOf(id).get
      smt.Symbol(id.name, typeToSMT(typ))
    }
    _exprToSMT(expr, scope, 0, idToSMT)
  }

  def exprToSMT(expr : lang.Expr, idToSMT : (lang.Identifier, lang.Scope, Int) => smt.Expr, scope : lang.Scope) : smt.Expr = {
    _exprToSMT(expr, scope, 0, idToSMT)
  }

  def smtToExpr(expr : smt.Expr) : lang.Expr = {
    def toExpr(expr : smt.Expr) : lang.Expr = smtToExpr(expr)
    def toExprs(es : List[smt.Expr]) : List[lang.Expr] = es.map((e : smt.Expr) => toExpr(e))

    expr match {
      case smt.Symbol(id, _) => lang.Identifier(id)
      case smt.IntLit(n) => lang.IntLit(n)
      case smt.BooleanLit(b) => lang.BoolLit(b)
      case smt.BitVectorLit(bv, w) => lang.BitVectorLit(bv, w)
      case opapp : smt.OperatorApplication =>
        val op = opapp.op
        val args = opapp.operands
        lang.OperatorApplication(smtToOp(op, args), toExprs(args))
      case smt.ArraySelectOperation(a,index) =>
        lang.OperatorApplication(lang.ArraySelect(toExprs(index)), List(toExpr(a)))
      case smt.ArrayStoreOperation(a,index,value) =>
        lang.OperatorApplication(lang.ArrayUpdate(toExprs(index), toExpr(value)), List(toExpr(a)))
      case smt.FunctionApplication(f, args) =>
        f match {
          case smt.Symbol(id, _) =>
            UclidMain.printVerbose("Function application of f == " + f.toString)
            lang.FuncApplication(lang.Identifier(id), toExprs(args))
          case _ =>
            throw new Utils.RuntimeError("Should never get here.")
        }
      case _ =>
        throw new Utils.UnimplementedException("'" + expr + "' is not yet supported.")
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
      case Lambda(syms,e) =>
        return Lambda(syms.map((sym) => Symbol(renamerFn(sym.id, sym.typ), sym.typ)), rename(e))
      case IntLit(_) | BitVectorLit(_,_) | BooleanLit(_) =>
        return expr
    }
  }

  /** Convert a Uclid NonTerminal to SMT/SyGuS Nonterminal
   *
   *  @param nt Uclid Nonterminal to convert
   *  @param scope context used for type information
   */
  def nonTerminalToSyGuS2(nt: lang.NonTerminal, fTyp : lang.FunctionSig,  ntsIds : List[(lang.Identifier, lang.Type)], scope: lang.Scope): smt.NonTerminal = {
    smt.NonTerminal(nt.id.name, typeToSMT(nt.typ), nt.terms.map(grammarTermToSyGuS2(_, fTyp, ntsIds, scope)))
  }

  /** Convert a Uclid GrammarTerm to SMT/SyGuS GrammarTerm
   *
   *  @param gt Uclid GrammarTerm to convert
   *  @param scope context used for type information
   */
  def grammarTermToSyGuS2(gt: lang.GrammarTerm, fTyp : lang.FunctionSig, ntsIds : List[(lang.Identifier, lang.Type)],  scope: lang.Scope): smt.GrammarTerm = {
    def idToSMT(id : lang.Identifier, scope : lang.Scope, past : Int) : smt.Expr = {
      val typ = scope.typeOf(id) match {
        case Some(typ) => typeToSMT(typ)
        case None => smt.UndefinedType
      }
      smt.Symbol(id.name, typ)
    }
    val expr = gt match {
      case lang.FuncAppTerm(id, args) => {
        val argsP = args.foldLeft(List.empty[GrammarTerm])((acc, arg) => acc :+ grammarTermToSyGuS2(arg, fTyp, ntsIds, scope))
        smt.FunctionApplication(smt.Symbol(id.name, typeToSMT(scope.typeOf(id).get)), argsP)
      }
      case lang.OpAppTerm(op, args) => {
        val opP = opToSMT(op, scope, 0, idToSMT)
        val argsP = args.foldLeft(List.empty[GrammarTerm])((acc, arg) => acc :+ grammarTermToSyGuS2(arg, fTyp, ntsIds, scope))
        smt.OperatorApplication(opP, argsP)
      }
      case lang.DefineAppTerm(id, args) => {
        val argsP = args.foldLeft(List.empty[GrammarTerm])((acc, arg) => acc :+ grammarTermToSyGuS2(arg, fTyp, ntsIds, scope))
        smt.DefineApplication(smt.Symbol(id.name, typeToSMT(scope.typeOf(id).get)), defineDeclToSyGuS2(scope.get(id).get.asInstanceOf[lang.Scope.Define], scope), argsP)
      }
      case lang.LiteralTerm(lit: lang.Literal) => _exprToSMT(lit, scope, 0, idToSMT)
      case lang.SymbolTerm(id: lang.Identifier) => 
        {
          val grammarArgs : List[(lang.Identifier, lang.Type)] = fTyp.args
          val typeMap = grammarArgs.toMap.++(ntsIds.toMap)
          typeMap.get(id) match {
            case Some(value) => _exprToSMT(id, scope, 0, idToSMT)
            case None => val smtType = scope.typeOf(id) match {
              case Some(t) => smt.Converter.typeToSMT(t)
              case None => throw new Utils.RuntimeError("Id not found in global scope for Grammar: for id " + id.name)
            }
            if (!smtType.isEnum) throw new Utils.RuntimeError("Id " + id.name + " in SymbolTerm from global scope is not an Enum type. Note that all symbols in the grammar must be inputs arguments or constants (Enums) (ref. SyGuS standard).");
            _exprToSMT(id, scope, 0, idToSMT);
          }
        }
      case _ => throw new Utils.UnimplementedException("grammar translation of " + gt.toString() + " is not yet supported.")
    }
    GrammarTerm(expr)
  }
 
  def defineDeclToSyGuS2 (defdecl : lang.Scope.Define, scope : lang.Scope) : smt.DefineSymbol = {
    val langDefineDecl : List[(lang.Identifier, lang.Type)] = defdecl.defDecl.sig.args
    def declIdToSMT(id : lang.Identifier, scope : lang.Scope, past : Int) : smt.Expr = {
      val typeMap = langDefineDecl.toMap
      typeMap.get(id) match {
        case Some(t) => smt.Symbol(id.name, typeToSMT(t))
        case None => {
          val smtType = scope.typeOf(id) match {
            case Some(t) => smt.Converter.typeToSMT(t)
            case None => throw new Utils.RuntimeError("Id not found in global scope for DefineDecl: for id " + id.name + " for DefineDecl " + defdecl.dId.name)
          }
          // Check if the external symbol is an enum (only constants are allowed: ref. SyGuS standard)
          if (!smtType.isEnum) throw new Utils.RuntimeError("Id " + id.name + " in DefineDecl from global scope is not an Enum type: in DefineDecl " + defdecl.dId.name + ". Note that all symbols in the grammar must be inputs arguments or constants (Enums) (ref. SyGuS standard).")
          smt.Symbol(id.name, smtType)
        }
      }
    }
    smt.DefineSymbol(defdecl.defDecl.id.name, scope.get(defdecl.dId).get.asInstanceOf[lang.Scope.Define].defDecl.sig, exprToSMT(defdecl.defDecl.expr, declIdToSMT, scope))
  }
}
