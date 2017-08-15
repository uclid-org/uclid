 /* Created by Rohit Sinha on 5/28/15.
 */
package uclid {
  import uclid.lang._
  
  class Context {
    var procedures: Map[UclIdentifier, UclProcedureDecl] = _
    var functions: Map[UclIdentifier, UclFunctionSig] = _
    var variables: Map[UclIdentifier, UclType] = _
    var inputs: Map[UclIdentifier, UclType] = _
    var outputs: Map[UclIdentifier, UclType] = _
    var constants: Map[UclIdentifier, UclType] = _
    var specifications: Map[UclIdentifier, UclExpr] = _
    var types : Map[UclIdentifier, UclType] = _
    var next: List[UclStatement] = _
    var init: List[UclStatement] = _
    
    def extractContext(m: UclModule) = {
      type T1 = UclProcedureDecl
      val m_procs = m.decls.filter { x => x.isInstanceOf[T1] }
      Utils.assert(Utils.allUnique(m_procs.map(i => i.asInstanceOf[T1].id)), 
          "Multiple procedures with identical names")
      procedures = m_procs.map(x => x.asInstanceOf[T1].id -> x.asInstanceOf[T1]).toMap
      
      type T2 = UclFunctionDecl
      val m_funcs = m.decls.filter { x => x.isInstanceOf[T2] }
      Utils.assert(Utils.allUnique(m_funcs.map(i => i.asInstanceOf[T2].id)),
          "Multiple functions with identical names")
      functions = m_funcs.map(x => x.asInstanceOf[T2].id -> x.asInstanceOf[T2].sig).toMap
      
      type T3 = UclStateVarDecl
      val m_vars = m.decls.filter { x => x.isInstanceOf[T3] }
      Utils.assert(Utils.allUnique(m_vars.map(i => i.asInstanceOf[T3].id)), 
          "Multiple variables with identical names")
      variables = m_vars.map(x => x.asInstanceOf[T3].id -> x.asInstanceOf[T3].typ).toMap
      
      type T4 = UclInputVarDecl
      val m_inputs = m.decls.filter { x => x.isInstanceOf[T4] }
      Utils.assert(Utils.allUnique(m_inputs.map(i => i.asInstanceOf[T4].id)), 
          "Multiple inputs with identical names")
      inputs = m_inputs.map(x => x.asInstanceOf[T4].id -> x.asInstanceOf[T4].typ).toMap
      
      type T5 = UclOutputVarDecl
      val m_outputs = m.decls.filter { x => x.isInstanceOf[T5] }
      Utils.assert(Utils.allUnique(m_outputs.map(i => i.asInstanceOf[T5].id)), 
          "Multiple outputs with identical names")
      outputs = m_outputs.map(x => x.asInstanceOf[T5].id -> x.asInstanceOf[T5].typ).toMap
      
      type T6 = UclConstantDecl
      val m_consts = m.decls.filter { x => x.isInstanceOf[T6] }
      Utils.assert(Utils.allUnique(m_consts.map(i => i.asInstanceOf[T6].id)), 
          "Multiple constants with identical names")
      constants = m_consts.map(x => x.asInstanceOf[T6].id -> x.asInstanceOf[T6].typ).toMap
  
      type TSpec = UclSpecDecl
      lazy val m_specs = m.decls.filter { x => x.isInstanceOf[TSpec] }
      Utils.assert(Utils.allUnique(m_consts.map(i => i.asInstanceOf[TSpec].id)), 
          "Multiple constants with identical names")
      specifications = m_specs.map { x => x.asInstanceOf[TSpec].id -> x.asInstanceOf[TSpec].expr } .toMap
      
      type T7 = UclTypeDecl
      val m_typedecls = m.decls.filter { x => x.isInstanceOf[T7] }
      Utils.assert(Utils.allUnique(m_typedecls.map(i => i.asInstanceOf[T7].id)), 
          "Multiple typedecls with identical names")
      types = m_typedecls.map(x => x.asInstanceOf[T7].id -> x.asInstanceOf[T7].typ).toMap
      
      val m_nextdecl = m.decls.filter { x => x.isInstanceOf[UclNextDecl] }
      Utils.assert(m_nextdecl.size == 1, "Need exactly one next decl");
      next = (m_nextdecl(0)).asInstanceOf[UclNextDecl].body
      
      val m_initdecl = m.decls.filter { x => x.isInstanceOf[UclInitDecl] }
      Utils.assert(m_initdecl.size == 1, "Need exactly one init decl");
      init = (m_initdecl(0)).asInstanceOf[UclInitDecl].body
    }
    
    def copyContext() : Context = {
      var copy: Context = new Context()
      copy.constants = this.constants
      copy.functions = this.functions
      copy.inputs = this.inputs
      copy.outputs = this.outputs
      copy.procedures = this.procedures
      copy.specifications = this.specifications
      copy.types = this.types
      copy.variables = this.variables
      copy.init = this.init
      copy.next = this.next
      return copy
    }
    
    def externalDecls() : List[UclIdentifier] = {
      return this.constants.keys.toList ++ this.functions.keys.toList ++ this.inputs.keys.toList ++ 
        this.outputs.keys.toList ++ this.types.keys.toList ++ this.variables.keys.toList ++ 
        this.procedures.keys.toList ++ this.specifications.keys.toList
    }
  }
  
  object UclidSemanticAnalyzer {
    def checkSemantics(m: UclModule) : Unit = {
      var c: Context = new Context()
      c.extractContext(m)
      checkModule(m,c)
    }
    
    def checkModule(m: UclModule, c: Context) : Unit = {
      //check module level stuff
      def checkRedeclarationAndTypes(decls: Map[UclIdentifier, Any]) : Unit = {
        decls.foreach(i => { Utils.assert(Utils.existsOnce(c.externalDecls(), i._1), 
            "Declaration " + i + " has conflicting name.") })
      }
      checkRedeclarationAndTypes(c.constants)
      checkRedeclarationAndTypes(c.inputs)
      checkRedeclarationAndTypes(c.outputs)
      checkRedeclarationAndTypes(c.variables)
      checkRedeclarationAndTypes(c.types)
      checkRedeclarationAndTypes(c.specifications)
      
      m.decls.foreach { x => checkDecl(x,c) }
    }
    
    def checkDecl(d: UclDecl, c: Context) : Unit = {
      val externalDecls : List[UclIdentifier] = c.externalDecls()
      d match {
        case UclProcedureDecl(id,sig,decls,body) =>
          Utils.assert(Utils.allUnique(sig.inParams.map(i => i._1) ++ sig.outParams.map(i => i._1)),
            "Signature of procedure " + id + " contains arguments of the same name")
          (sig.inParams ++ sig.outParams).foreach(i => { 
            Utils.assert(Utils.existsOnce(
                (externalDecls ++ sig.inParams.map(j => j._1) ++ sig.outParams.map(j => j._1)), i._1),
                "Signature of procedure " + id + " contains redeclaration: " + i);
            checkType(i._2, c)
          })
       
          decls.foreach { i => {
            //check that name is not reused
            Utils.assert(Utils.existsNone(
                externalDecls ++ sig.inParams.map(x => x._1) ++ sig.outParams.map(x => x._1), i.id), 
                "Local variable " + i + " redeclared")
            c.procedures.keys.
              filter{j => id.value != j.value}.
              foreach{ j => Utils.assert(Utils.existsNone(c.procedures(j).decls.map(k => k.id), i.id), 
                  "Local variable " + i + " redeclared as a local variable of procedure " + j ) }
            checkType(i.typ,c)
          } }
          
          var c2: Context = c.copyContext()
          c2.inputs = c.inputs ++ (sig.inParams.map(i => i._1 -> i._2).toMap)
          c2.variables = c.variables ++ (sig.outParams.map(i => i._1 -> i._2).toMap)
          c2.variables = c2.variables ++ (decls.map(i => i.id -> i.typ).toMap)
          body.foreach { x => checkStmt(x,c2) }
          
        case UclFunctionDecl(id,sig) =>
          Utils.assert(Utils.allUnique(sig.args.map(i => i._1)), 
              "Signature of function " + id + " contains arguments of the same name")
          sig.args.foreach(i => { 
            //check that name is not reused
            Utils.assert(Utils.existsNone(externalDecls, i._1), 
                "Signature of function " + id + " contains redeclaration: " + i)
            checkType(i._2, c)
          })
        case UclTypeDecl(id,typ)       => checkType(typ, c)
        case UclStateVarDecl(id, typ)  => checkType(typ, c)
        case UclInputVarDecl(id,typ)   => checkType(typ, c)
        case UclOutputVarDecl(id, typ) => checkType(typ, c)
        case UclConstantDecl(id, typ)  => checkType(typ, c)
        case UclSpecDecl(id, expr)     => 
          checkExpr(expr, c)
          Utils.assert(transitiveType(typeOf(expr, c)._1, c).isInstanceOf[UclBoolType], 
              "Expressions in specification declarations must have Boolean type.")
        case UclInitDecl(body)         => body.foreach{x => checkStmt(x,c)}
        case UclNextDecl(body)         => body.foreach{x => checkStmt(x,c)}
      }
    }
    
    /* 
     * Replaces type synonyms until only base types appear
     */
    def transitiveType(typ: UclType, c: Context) : UclType = {
      val externalDecls : List[UclIdentifier] = c.externalDecls()
      if (typ.isInstanceOf[UclEnumType]) {
        return typ
      } else if (typ.isInstanceOf[UclRecordType]) {
        val t = typ.asInstanceOf[UclRecordType]
        return UclRecordType(t.fields.map(i => (i._1, transitiveType(i._2,c))))
      } else if (typ.isInstanceOf[UclMapType]) {
        val t = typ.asInstanceOf[UclMapType]
        return UclMapType(t.inTypes.map(i => transitiveType(i,c)), transitiveType(t.outType,c))
      } else if (typ.isInstanceOf[UclArrayType]) {
        val t = typ.asInstanceOf[UclArrayType]
        return UclArrayType(t.inTypes.map(i => transitiveType(i,c)), 
            transitiveType(t.outType,c))
      } else if (typ.isInstanceOf[UclSynonymType]) {
        val t = typ.asInstanceOf[UclSynonymType]
        return transitiveType(c.types(t.id),c)
      } else { return typ }
    }
    
    def checkType(typ: UclType, c: Context) : Unit = {
      val externalDecls : List[UclIdentifier] = c.externalDecls()
      if (typ.isInstanceOf[UclEnumType]) {
        typ.asInstanceOf[UclEnumType].ids.foreach { i => 
          Utils.assert(Utils.existsNone(externalDecls, i), "Enum " + typ + " has a redeclaration")
        }
      } else if (typ.isInstanceOf[UclRecordType]) {
        val t = typ.asInstanceOf[UclRecordType]
        t.fields.foreach { i => 
          //assert no maps
          Utils.assert(!(transitiveType(i._2,c).isInstanceOf[UclMapType] || 
              transitiveType(i._2,c).isInstanceOf[UclArrayType]), 
              "Records cannot contain maps or arrays")
          checkType(i._2, c)
        }
      } else if (typ.isInstanceOf[UclMapType]) {
        typ.asInstanceOf[UclMapType].inTypes.foreach { i => 
          Utils.assert(!(transitiveType(i,c).isInstanceOf[UclMapType]), 
              "Map types cannot be indexed by maps: " + typ);
          checkType(i,c) 
          }
        Utils.assert(!(transitiveType(typ.asInstanceOf[UclMapType].outType,c).isInstanceOf[UclMapType]), 
            "Map types cannot produce maps: " + typ)
        checkType(typ.asInstanceOf[UclMapType].outType, c)
      } else if (typ.isInstanceOf[UclArrayType]) {
        typ.asInstanceOf[UclArrayType].inTypes.foreach { i => 
          Utils.assert(!(transitiveType(i,c).isInstanceOf[UclArrayType]), 
              "Array types cannot be indexed by arrays: " + typ);
          checkType(i,c) 
          }
        Utils.assert(!(transitiveType(typ.asInstanceOf[UclArrayType].outType,c).isInstanceOf[UclArrayType]), 
            "Array types cannot produce arrays: " + typ)
        checkType(typ.asInstanceOf[UclArrayType].outType, c)
      } else if (typ.isInstanceOf[UclSynonymType]) {
        Utils.assert(c.types.keys.exists { x => x.value == typ.asInstanceOf[UclSynonymType].id.value }, 
            "Synonym Type " + typ + " does not exist.")
      }
    }
  
    def typeOfLHS(lhs: UclLhs, c: Context) : UclType = {
      var intermediateType : UclType = (c.outputs ++ c.variables)(lhs.id)
      lhs.arraySelect match {
        case Some(as) => 
          Utils.assert(transitiveType(intermediateType,c).isInstanceOf[UclArrayType],
              "Cannot use select on non-array " + lhs.id)
          intermediateType = transitiveType(intermediateType,c).asInstanceOf[UclArrayType].outType
        case None => ()
      }
      lhs.recordSelect match {
        case Some(rs) => 
          Utils.assert(transitiveType(intermediateType,c).isInstanceOf[UclRecordType], 
              "Expected record type: " + intermediateType)
          rs.foreach { field =>
            transitiveType(intermediateType,c).asInstanceOf[UclRecordType].fields.find(i => i._1.value == field.value) 
                match { case Some(field_type) => intermediateType = field_type._2
                        case None => Utils.assert(false, "Should not get here") }
          }
          return intermediateType
        case None => return intermediateType
      }
    }
    
    def checkLHS(lhs: UclLhs, c: Context) : Unit = {
      Utils.assert((c.outputs.keys ++ c.variables.keys).exists { x => x.value == lhs.id.value }, 
          "LHS variable " + lhs.id + " does not exist")
      var intermediateType = transitiveType((c.outputs ++ c.variables)(lhs.id),c)
      lhs.arraySelect match {
        case Some(index) => 
          //assert that lhs.id is a map or array
          Utils.assert(intermediateType.isInstanceOf[UclArrayType],
              "Cannot use select on non-array " + lhs.id)
          intermediateType = transitiveType(intermediateType.asInstanceOf[UclArrayType].outType,c)
          index.foreach { x => checkExpr(x,c) }
        case None => ()
      }
      lhs.recordSelect match {
        case Some(rs) => 
          Utils.assert(intermediateType.isInstanceOf[UclRecordType], "Expected record type: " + intermediateType)
          rs.foreach { field => 
            Utils.assert(intermediateType.asInstanceOf[UclRecordType].fields.
                exists { i => i._1.value == field.value }, "Field " + field + " not found")
            intermediateType.asInstanceOf[UclRecordType].fields.find(i => i._1.value == field.value) 
                match { case Some(y) => intermediateType = transitiveType(y._2,c)
                        case None => Utils.assert(false, "Should not get here") }
          }
        case None => ()
      }
    }
    
    def assertNoTemporalType(t: (UclType, Boolean), e: UclExpr) : Unit = 
      Utils.assert(!t._2, "No temporal operators allowed in expression " + e)
    
    def checkStmt(s: UclStatement, c: Context) : Unit = {
      val externalDecls : List[UclIdentifier] = c.externalDecls()
      s match {
        case UclAssertStmt(e) => checkExpr(e,c)
        case UclAssumeStmt(e) => checkExpr(e,c)
        case UclHavocStmt(id) => 
          Utils.assert((c.variables.keys ++ c.outputs.keys).exists { x => x.value == id.value }, 
              "Statement " + s + " updates unknown variable")
        case UclAssignStmt(lhss, rhss) => 
          Utils.assert(lhss.size == rhss.size, "LHSS and RHSS of different size: " + s);
          lhss.foreach{ x => checkLHS(x,c) }; rhss.foreach { x => checkExpr(x,c) };
          Utils.assert((lhss zip rhss).forall 
              { i => 
                val rhsType = typeOf(i._2, c)
                typeOfLHS(i._1, c) == rhsType._1 && !rhsType._2}, 
              "LHSS and RHSS have conflicting types: " + s);
          Utils.assert(lhss.distinct.size == lhss.size, "LHSS contains identical variables: " + s)
        case UclIfElseStmt(e, t, f) => 
          checkExpr(e,c); 
          val eType = typeOf(e,c)
          assertNoTemporalType(eType,e)
          Utils.assert(transitiveType(eType._1,c) == UclBoolType(), 
              "Conditionals in if statements must have boolean type.");
          (t ++ f).foreach { x => checkStmt(x,c) };
        case UclForStmt(id,_,body) => 
          Utils.assert(!(externalDecls.exists { x => x.value == id.value }), 
              "For Loop counter " + id + " redeclared");
          var c2: Context = c.copyContext();
          c2.inputs = c.inputs ++ Map(id -> UclIntType());
          body.foreach{x => checkStmt(x,c2)}
        case UclCaseStmt(body) => body.foreach { x =>
          checkExpr(x._1,c);
          val xType = typeOf(x._1,c)
          Utils.assert(transitiveType(xType._1,c) == UclBoolType() && !xType._2, 
              "Expected boolean conditional within case statement guard");
          x._2.foreach { y => checkStmt(y,c) } 
          }
        case UclProcedureCallStmt(id, lhss, args) =>
          Utils.assert(Utils.existsOnce(c.procedures.keys.toList, id), 
              "Calling unknown procedure " + id)
          lhss.foreach{ x => checkLHS(x,c) }
          args.foreach{ x => checkExpr(x,c) }
          Utils.assert(lhss.size == c.procedures(id).sig.outParams.size, 
              "Calling procedure " + id + " with incorrect number of results")
          Utils.assert((lhss zip c.procedures(id).sig.outParams.map(i => i._2)).
              forall { i => typeOfLHS(i._1, c) == i._2 }, 
              "Calling procedure " + id + " with results of incorrect type");
          Utils.assert(args.size == c.procedures(id).sig.inParams.size, 
              "Calling procedure " + id + " with incorrect number of arguments")
          Utils.assert((args zip c.procedures(id).sig.inParams.map(i => i._2)).
              forall { i => typeOf(i._1, c)._1 == i._2 }, 
              "Calling procedure " + id + " with arguments of incorrect type")
      }
    }
    
    /**
     * Returns the type and the fact whether the expression contains a temporal operator.
     */
    def typeOf(e: UclExpr, c: Context) : (UclType, Boolean) = {
      def assertBoolType(t: UclType) : Unit = {
        Utils.assert(transitiveType(t,c) == UclBoolType() || t == UclTemporalType(), 
            "Expected expression " + t + " to have type Bool (or be a temporal formula).")
      }
      def typeOfBinaryBooleanOperator (l: UclExpr, r: UclExpr) : (UclType, Boolean) = {
          val (typeL, tempL) = typeOf(l,c)
          assertBoolType(typeL)
          val (typeR, tempR) = typeOf(r,c)
          assertBoolType(typeR)
          return (UclBoolType(), tempL || tempR)
      }
      def typeOfUnaryBooleanOperator(e: UclExpr) : (UclType, Boolean) = {
        val (typeE, tempE) = typeOf(e,c)
        assertBoolType(typeE)
        return (UclBoolType(), tempE)
      }
      
      e match {
        // Temporal operators
        case UclTemporalOpGlobally(e)  => 
          val t = typeOfUnaryBooleanOperator(e)
          return (t._1, true)
        case UclTemporalOpFinally(e)   => 
          val t = typeOfUnaryBooleanOperator(e)
          return (t._1, true)
        case UclTemporalOpUntil(l,r)   =>
          val t = typeOfBinaryBooleanOperator(l,r)
          return (t._1, true)
        case UclTemporalOpWUntil(l,r)  =>
          val t = typeOfBinaryBooleanOperator(l,r)
          return (t._1, true)
        case UclTemporalOpRelease(l,r) =>
          val t = typeOfBinaryBooleanOperator(l,r)
          return (t._1, true)
        // Boolean operators
        case UclBiImplication(l,r) => return typeOfBinaryBooleanOperator(l,r)
        case UclImplication(l,r)   => return typeOfBinaryBooleanOperator(l,r)
        case UclConjunction(l,r)   => return typeOfBinaryBooleanOperator(l,r)
        case UclDisjunction(l,r)   => return typeOfBinaryBooleanOperator(l,r)
        case UclNegation(e) => 
          return typeOfUnaryBooleanOperator(e)
        case UclEquality(l,r) => 
          val (typeL, tempL) = typeOf(l,c)
          Utils.assert(transitiveType(typeL,c).isInstanceOf[UclIntType], 
              "Equality operator requires Int arguments. Lefthand argument side is of type " + typeL + "instead")
          val (typeR, tempR) = typeOf(r,c)
          Utils.assert(transitiveType(typeR,c).isInstanceOf[UclIntType], 
              "Equality operator requires Int arguments. Righthand argument side is of type " + typeR + "instead")
          Utils.assert(typeL == typeR,
              "Equality operator requires equally typed arguments.")
          return (UclBoolType(), tempL || tempR)
        case UclIFuncApplication(op,es) =>
          lazy val types = es.map { e => typeOf (e,c) }
          /**
           * assert types are equal and comparable
           */
          types.head._1 match { 
            case x : UclIntType => () //TODO: add bitvectors
            case x => Utils.assert(false, "Comparison operator " + op + " requires Int arguments.")
          }
          if (types.tail.exists { x => types.head._1 != x._1}) {
            Utils.assert(false, "Comparison operator " + op + " has arguments with unequal types: " + types.map {x => x._1})
          }
          val temporal = types.exists { x => x._2}
          return (op match {
              case UclLTOperator() | UclLEOperator() | UclGTOperator() | UclGEOperator() => UclBoolType()
              case UclAddOperator() | UclMulOperator() => UclIntType()
              case UclExtractOperator(_,_) => throw new Utils.UnimplementedException("bvextract unimplemented")
              case UclConcatOperator() => throw new Utils.UnimplementedException("bvconcat unimplemented")
            },
            temporal)
        case UclArraySelectOperation(a,index) =>
          val (typ,temporal) = typeOf(a,c)
          Utils.assert(!temporal, "Array types may not have temporal subformulas")
          Utils.assert(transitiveType(typ,c).isInstanceOf[UclArrayType],
              "expected array type: " + e)
          Utils.assert((typ.asInstanceOf[UclArrayType].inTypes zip index).
              forall { x => x._1 == typeOf(x._2,c)._1 }, "Array Select operand type mismatch: " + e)
          return (typ.asInstanceOf[UclArrayType].outType, false) //select returns the range type
        case UclArrayStoreOperation(a,index,value) =>
          val (typ,temporal) = typeOf(a,c)
          Utils.assert(!temporal, "Array types may not have temporal subformulas")
          Utils.assert(transitiveType(typ,c).isInstanceOf[UclArrayType], "expected array type: " + e)
          Utils.assert((typ.asInstanceOf[UclArrayType].inTypes zip index).
              forall { x => x._1 == typeOf(x._2,c)._1 }, "Array Store operand type mismatch: " + e)
          Utils.assert(typ.asInstanceOf[UclArrayType].outType == typeOf(value,c)._1, 
              "Array Store value type mismatch")
          return (typ, false) //store returns the new array
        case UclFuncApplication(f,args) =>
          val (typ,temporal) = typeOf(f,c)
          Utils.assert(!temporal, "Array types may not have temporal subformulas")
          Utils.assert(transitiveType(typ,c).isInstanceOf[UclMapType],"Expected Map Type " + e);
          Utils.assert((typ.asInstanceOf[UclMapType].inTypes.size == args.size), 
            "Function application has bad number of arguments: " + e);
          Utils.assert((typ.asInstanceOf[UclMapType].inTypes zip args).forall{i => i._1 == typeOf(i._2,c)._1}, 
            "Function application has bad types of arguments: " + e)
          return (typ.asInstanceOf[UclMapType].outType, false)
        case UclITE(cond,t,f) =>
          val condType = typeOf (cond,c)
          assertBoolType(condType._1);
          val tType = typeOf (t,c)
          val fType = typeOf (f,c)
          Utils.assert(tType._1 == fType._1, 
              "ITE true and false expressions have different types: " + e)
          return (tType._1, tType._2 || fType._2)
        case UclLambda(ids,le) =>
          var c2: Context = c.copyContext()
          c2.inputs = c.inputs ++ (ids.map(i => i._1 -> i._2).toMap)
          Utils.assert(ids.forall { i => transitiveType(i._2,c) == UclBoolType() || 
            transitiveType(i._2,c) == UclIntType() }, 
              "Cannot construct Lambda expressions of non-primitive types: " + le)
          val t = typeOf(le,c2)
          Utils.assert(!t._2, "What do you need a Lambda expression with temporal type for!?")
          return (UclMapType(ids.map(i => i._2), t._1), false) //Lambda expr returns a map type
        case UclIdentifier(id) => ((c.constants ++ c.variables ++ c.inputs ++ c.outputs)(UclIdentifier(id)), false)
        case UclNumber(n) => (UclIntType(), false)
        case UclBoolean(b) => (UclBoolType(), false)
      }    
    }
    
    def checkExpr(e: UclExpr, c: Context) : Unit = {
      val externalDecls : List[UclIdentifier] = c.externalDecls()
       e match { //check that all identifiers in e have been declared
         case UclBiImplication(l,r) => checkExpr(r,c); checkExpr(l,c);
         case UclImplication(l,r) => checkExpr(r,c); checkExpr(l,c);
         case UclConjunction(l,r) => checkExpr(r,c); checkExpr(l,c);
         case UclDisjunction(l,r) => checkExpr(r,c); checkExpr(l,c);
         case UclNegation(l) => checkExpr(l,c);
         case UclEquality(l,r) => checkExpr(r,c); checkExpr(l,c);
         case UclIFuncApplication(op,args) => args.foreach { x => checkExpr(x,c) }
         case UclArraySelectOperation(a,index) => checkExpr(a,c); index.foreach { x => checkExpr(x,c) }
         case UclArrayStoreOperation(a,index,value) => 
           checkExpr(a,c); index.foreach { x => checkExpr(x,c) }; checkExpr(value, c);
         case UclFuncApplication(f,args) => checkExpr(f,c); args.foreach { x => checkExpr(x,c) }
         case UclITE(cond,t,f) => 
           checkExpr(cond,c) 
           val tTypeCond = transitiveType(typeOf(cond, c)._1, c)
           Utils.assert(tTypeCond.isInstanceOf[UclBoolType], 
               "Conditional must have boolean type in expression " + e + " but has type " + tTypeCond)
           checkExpr(t,c) 
           checkExpr(f,c)
           Utils.assert(transitiveType(typeOf(t, c)._1, c) == transitiveType(typeOf(f, c)._1, c), 
               "The branches in the ITE expression " + e + " have different types.")
         case UclLambda(ids,le) => ids.foreach { 
             x => checkType(x._2,c);
             Utils.assert(transitiveType(x._2,c).isInstanceOf[UclIntType] || 
                 transitiveType(x._2,c).isInstanceOf[UclBoolType],
               "Lambda indexed by non-primitive type in expression " + e);
           }
           ids.foreach{ x => Utils.assert((externalDecls ++ ids.map(i => i._1)).
               count { i => i.value == x._1.value } == 1, "Lambda argument has a redeclaration") }
           var c2: Context = c.copyContext()
           c2.inputs = c.inputs ++ (ids.map(i => i._1 -> i._2).toMap)
           checkExpr(le,c2);
         case UclIdentifier(id) => 
           Utils.assert((c.constants.keys ++ c.inputs.keys ++ c.outputs.keys ++ c.variables.keys).
           exists{i => i.value == id}, "Identifier " + id + " not found");
         case _ => ()
       }
      typeOf(e,c) //do type checking on e
    }
  }
    
}
