 /* Created by Rohit Sinha on 5/28/15.
 */
package uclid;
package lang;

class Context {
  var procedures: Map[Identifier, ProcedureDecl] = _
  var functions: Map[Identifier, FunctionSig] = _
  var variables: Map[Identifier, Type] = _
  var inputs: Map[Identifier, Type] = _
  var outputs: Map[Identifier, Type] = _
  var constants: Map[Identifier, Type] = _
  var forallVars: Map[Identifier, Type] = Map.empty
  var existsVars: Map[Identifier, Type] = Map.empty
  var specifications: Map[Identifier, Expr] = _
  var enumeratedConstants : Map[Identifier, EnumType] = _
  var types : Map[Identifier, Type] = _
  var next: List[Statement] = _
  var init: List[Statement] = _
  
  def extractContext(m: Module) = {
    type T1 = ProcedureDecl
    val m_procs = m.decls.filter { x => x.isInstanceOf[T1] }
    Utils.assert(Utils.allUnique(m_procs.map(i => i.asInstanceOf[T1].id)), 
        "Multiple procedures with identical names")
    procedures = m_procs.map(x => x.asInstanceOf[T1].id -> x.asInstanceOf[T1]).toMap
    
    type T2 = FunctionDecl
    val m_funcs = m.decls.filter { x => x.isInstanceOf[T2] }
    Utils.assert(Utils.allUnique(m_funcs.map(i => i.asInstanceOf[T2].id)),
        "Multiple functions with identical names")
    functions = m_funcs.map(x => x.asInstanceOf[T2].id -> x.asInstanceOf[T2].sig).toMap
    
    type T3 = StateVarDecl
    val m_vars = m.decls.filter { x => x.isInstanceOf[T3] }
    Utils.assert(Utils.allUnique(m_vars.map(i => i.asInstanceOf[T3].id)), 
        "Multiple variables with identical names")
    variables = m_vars.map(x => x.asInstanceOf[T3].id -> x.asInstanceOf[T3].typ).toMap
    
    type T4 = InputVarDecl
    val m_inputs = m.decls.filter { x => x.isInstanceOf[T4] }
    Utils.assert(Utils.allUnique(m_inputs.map(i => i.asInstanceOf[T4].id)), 
        "Multiple inputs with identical names")
    inputs = m_inputs.map(x => x.asInstanceOf[T4].id -> x.asInstanceOf[T4].typ).toMap
    
    type T5 = OutputVarDecl
    val m_outputs = m.decls.filter { x => x.isInstanceOf[T5] }
    Utils.assert(Utils.allUnique(m_outputs.map(i => i.asInstanceOf[T5].id)), 
        "Multiple outputs with identical names")
    outputs = m_outputs.map(x => x.asInstanceOf[T5].id -> x.asInstanceOf[T5].typ).toMap
    
    type T6 = ConstantDecl
    val m_consts = m.decls.filter { x => x.isInstanceOf[T6] }
    Utils.assert(Utils.allUnique(m_consts.map(i => i.asInstanceOf[T6].id)), 
        "Multiple constants with identical names")
    constants = m_consts.map(x => x.asInstanceOf[T6].id -> x.asInstanceOf[T6].typ).toMap

    type TSpec = SpecDecl
    lazy val m_specs = m.decls.filter { x => x.isInstanceOf[TSpec] }
    Utils.assert(Utils.allUnique(m_consts.map(i => i.asInstanceOf[TSpec].id)), 
        "Multiple constants with identical names")
    specifications = m_specs.map { x => x.asInstanceOf[TSpec].id -> x.asInstanceOf[TSpec].expr } .toMap
    
    type T7 = TypeDecl
    val m_typedecls = m.decls.filter { x => x.isInstanceOf[T7] }
    Utils.assert(Utils.allUnique(m_typedecls.map(i => i.asInstanceOf[T7].id)), 
        "Multiple typedecls with identical names")
    types = m_typedecls.map(x => x.asInstanceOf[T7].id -> x.asInstanceOf[T7].typ).toMap

    val scope = ScopeMap.empty + m
    val enums = scope.map.filter((p) => p._2.isInstanceOf[Scope.EnumIdentifier]).map((p) => p._2.asInstanceOf[Scope.EnumIdentifier])
    enumeratedConstants = enums.map((e) => (e.enumId -> e.enumTyp)).toMap
    
    val m_nextdecl = m.decls.filter { x => x.isInstanceOf[NextDecl] }
    Utils.assert(m_nextdecl.size == 1, "Need exactly one next decl.");
    next = (m_nextdecl(0)).asInstanceOf[NextDecl].body
    
    val m_initdecl = m.decls.filter { x => x.isInstanceOf[InitDecl] }
    Utils.assert(m_initdecl.size <= 1, "Can't have more than one init decl.");
    if (m_initdecl.size > 0) {
      init = (m_initdecl(0)).asInstanceOf[InitDecl].body
    } else {
      init = List.empty[Statement]
    }
  }
  
  def copyContext() : Context = {
    var copy: Context = new Context()
    copy.constants = this.constants
    copy.functions = this.functions
    copy.inputs = this.inputs
    copy.outputs = this.outputs
    copy.procedures = this.procedures
    copy.forallVars = this.forallVars
    copy.existsVars = this.existsVars
    copy.specifications = this.specifications
    copy.types = this.types
    copy.enumeratedConstants = this.enumeratedConstants
    copy.variables = this.variables
    copy.init = this.init
    copy.next = this.next
    return copy
  }
  
  def contextWithOperatorApplication(op : Operator) : Context = {
    op match {
     case ForallOp(vs) =>
       val c2 = this.copyContext()
       c2.forallVars = c2.forallVars ++ (vs.map((i) => i._1 -> i._2).toMap)
       c2
     case ExistsOp(vs) =>
       var c2 = this.copyContext()
       c2.existsVars = c2.existsVars ++ (vs.map(i => i._1 -> i._2).toMap)
       c2
     case _ =>
       this
    }
  }
  
  def externalDecls() : List[Identifier] = {
    return this.constants.keys.toList ++ this.functions.keys.toList ++ this.inputs.keys.toList ++ 
      this.outputs.keys.toList ++ this.types.keys.toList ++ this.variables.keys.toList ++ 
      this.procedures.keys.toList ++ this.specifications.keys.toList
  }
}


object UclidSemanticAnalyzer {
  
  def checkSemantics(m: Module) : Unit = {
    var c: Context = new Context()
    c.extractContext(m)
    checkModule(m,c)
  }
  
  def checkModule(m: Module, c: Context) : Unit = {
    //check module level stuff
    def checkRedeclarationAndTypes(decls: Map[Identifier, Any]) : Unit = {
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
  
  def checkDecl(d: Decl, c: Context) : Unit = {
    val externalDecls : List[Identifier] = c.externalDecls()
    d match {
      case ProcedureDecl(id,sig,decls,body) =>
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
            filter{j => id.name != j.name}.
            foreach{ j => Utils.assert(Utils.existsNone(c.procedures(j).decls.map(k => k.id), i.id), 
                "Local variable " + i + " redeclared as a local variable of procedure " + j ) }
          checkType(i.typ,c)
        } }
        
        var c2: Context = c.copyContext()
        c2.inputs = c.inputs ++ (sig.inParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c.variables ++ (sig.outParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c2.variables ++ (decls.map(i => i.id -> i.typ).toMap)
        body.foreach { x => checkStmt(x,c2) }
        
      case FunctionDecl(id,sig) =>
        Utils.assert(Utils.allUnique(sig.args.map(i => i._1)), 
            "Signature of function " + id + " contains arguments of the same name")
        sig.args.foreach(i => { 
          //check that name is not reused
          Utils.assert(Utils.existsNone(externalDecls, i._1), 
              "Signature of function " + id + " contains redeclaration: " + i)
          checkType(i._2, c)
        })
      case TypeDecl(id,typ)       => checkType(typ, c)
      case StateVarDecl(id, typ)  => checkType(typ, c)
      case InputVarDecl(id,typ)   => checkType(typ, c)
      case OutputVarDecl(id, typ) => checkType(typ, c)
      case ConstantDecl(id, typ)  => checkType(typ, c)
      case SpecDecl(id, expr)     => 
        checkExpr(expr, c)
        Utils.assert(transitiveType(typeOf(expr, c)._1, c).isInstanceOf[BoolType], 
            "Expressions in specification declarations must have Boolean type.")
      case InitDecl(body)         => body.foreach{x => checkStmt(x,c)}
      case NextDecl(body)         => body.foreach{x => checkStmt(x,c)}
    }
  }
  
  /* 
   * Replaces type synonyms until only base types appear
   */
  def transitiveType(typ: Type, c: Context) : Type = {
    val externalDecls : List[Identifier] = c.externalDecls()
    if (typ.isInstanceOf[EnumType]) {
      return typ
    } else if (typ.isInstanceOf[RecordType]) {
      val t = typ.asInstanceOf[RecordType]
      return RecordType(t.fields.map(i => (i._1, transitiveType(i._2,c))))
    } else if (typ.isInstanceOf[MapType]) {
      val t = typ.asInstanceOf[MapType]
      return MapType(t.inTypes.map(i => transitiveType(i,c)), transitiveType(t.outType,c))
    } else if (typ.isInstanceOf[ArrayType]) {
      val t = typ.asInstanceOf[ArrayType]
      return ArrayType(t.inTypes.map(i => transitiveType(i,c)), 
          transitiveType(t.outType,c))
    } else if (typ.isInstanceOf[SynonymType]) {
      val t = typ.asInstanceOf[SynonymType]
      return transitiveType(c.types(t.id),c)
    } else { return typ }
  }
  
  def checkType(typ: Type, c: Context) : Unit = {
    val externalDecls : List[Identifier] = c.externalDecls()
    if (typ.isInstanceOf[EnumType]) {
      typ.asInstanceOf[EnumType].ids.foreach { i => 
        Utils.assert(Utils.existsNone(externalDecls, i), "Enum " + typ + " has a redeclaration")
      }
    } else if (typ.isInstanceOf[RecordType]) {
      val t = typ.asInstanceOf[RecordType]
      t.fields.foreach { i => 
        //assert no maps
        Utils.assert(!(transitiveType(i._2,c).isInstanceOf[MapType] || 
            transitiveType(i._2,c).isInstanceOf[ArrayType]), 
            "Records cannot contain maps or arrays")
        checkType(i._2, c)
      }
    } else if (typ.isInstanceOf[MapType]) {
      typ.asInstanceOf[MapType].inTypes.foreach { i => 
        Utils.assert(!(transitiveType(i,c).isInstanceOf[MapType]), 
            "Map types cannot be indexed by maps: " + typ);
        checkType(i,c) 
        }
      Utils.assert(!(transitiveType(typ.asInstanceOf[MapType].outType,c).isInstanceOf[MapType]), 
          "Map types cannot produce maps: " + typ)
      checkType(typ.asInstanceOf[MapType].outType, c)
    } else if (typ.isInstanceOf[ArrayType]) {
      typ.asInstanceOf[ArrayType].inTypes.foreach { i => 
        Utils.assert(!(transitiveType(i,c).isInstanceOf[ArrayType]), "Array types cannot be indexed by arrays: " + typ);
        checkType(i,c) 
        }
      Utils.assert(!(transitiveType(typ.asInstanceOf[ArrayType].outType,c).isInstanceOf[ArrayType]), 
          "Array types cannot produce arrays: " + typ)
      checkType(typ.asInstanceOf[ArrayType].outType, c)
    } else if (typ.isInstanceOf[SynonymType]) {
      Utils.assert(c.types.keys.exists { x => x.name == typ.asInstanceOf[SynonymType].id.name }, 
          "Synonym Type " + typ + " does not exist.")
    }
  }

  def typeOfLHS(lhs: Lhs, c: Context) : Type = {
    var intermediateType : Type = (c.outputs ++ c.variables)(lhs.ident)
    lhs match {
      case LhsId(id) => 
        intermediateType
      case LhsArraySelect(id, indices) =>
        Utils.assert(transitiveType(intermediateType, c).isInstanceOf[ArrayType], 
            "Cannot use select on non-array: " + lhs.ident)
        transitiveType(intermediateType,c).asInstanceOf[ArrayType].outType
      case LhsRecordSelect(id, fields) => 
        Utils.assert(transitiveType(intermediateType,c).isProduct, 
            "Expected product type when assigning to field: " + intermediateType)
        val productType = intermediateType.asInstanceOf[ProductType]
        val fieldType = productType.nestedFieldType(fields)
        Utils.assert(fieldType.isDefined, "Field type could not be computed: " + lhs.toString)
        transitiveType(fieldType.get, c)
      case LhsSliceSelect(id, slice) =>
        Utils.assert(transitiveType(intermediateType, c).isBitVector,
            "Expected bitvector type when assigning to slice: " + intermediateType)
        val bvType = transitiveType(intermediateType, c).asInstanceOf[BitVectorType]
        Utils.assert(slice.hi < bvType.width && slice.lo < bvType.width, 
            "Invalid bitvector slice. ")
        BitVectorType(slice.hi - slice.lo + 1)
    }
  }
  
  def checkLHS(lhs: Lhs, c: Context) : Unit = {
    Utils.assert((c.outputs.keys ++ c.variables.keys).exists { x => x.name == lhs.ident.name }, 
        "LHS variable " + lhs.ident + " does not exist")
    var intermediateType = transitiveType((c.outputs ++ c.variables)(lhs.ident),c)
    lhs match {
      case LhsId(id) => 
        intermediateType
      case LhsArraySelect(id, indices) =>
        Utils.assert(transitiveType(intermediateType, c).isInstanceOf[ArrayType], 
            "Cannot use select on non-array: " + lhs.ident)
        indices.foreach { x => checkExpr(x,c) }
      case LhsRecordSelect(id, fields) => 
        Utils.assert(transitiveType(intermediateType,c).isProduct, 
            "Expected product type when assigning to field: " + intermediateType)
        val productType = intermediateType.asInstanceOf[ProductType]
        val fieldType = productType.nestedFieldType(fields)
        Utils.assert(fieldType.isDefined, "Field type could not be computed: " + lhs.toString)
      case LhsSliceSelect(id, slice) =>
        Utils.assert(transitiveType(intermediateType, c).isBitVector,
            "Expected bitvector type when assigning to slice: " + intermediateType)
        val bvType = transitiveType(intermediateType, c).asInstanceOf[BitVectorType]
        Utils.assert(slice.hi < bvType.width && slice.lo < bvType.width, 
            "Invalid bitvector slice. ")
    }
  }
  
  def assertNoTemporalType(t: (Type, Boolean), e: Expr) : Unit = 
    Utils.assert(!t._2, "No temporal operators allowed in expression " + e)
  
  def checkStmt(s: Statement, c: Context) : Unit = {
    val externalDecls : List[Identifier] = c.externalDecls()
    s match {
      case SkipStmt() => 
      case AssertStmt(e, id) => checkExpr(e, c)
      case AssumeStmt(e, id) => checkExpr(e, c)
      case HavocStmt(id) => 
        Utils.assert((c.variables.keys ++ c.outputs.keys).exists { x => x.name == id.name }, 
            "Statement " + s + " updates unknown variable")
      case AssignStmt(lhss, rhss) => 
        Utils.assert(lhss.size == rhss.size, "LHSS and RHSS of different size: " + s);
        lhss.foreach{ x => checkLHS(x,c) }; rhss.foreach { x => checkExpr(x,c) };
        val lhsTypes = lhss.map(typeOfLHS(_, c))
        val rhsTypes = rhss.map(typeOf(_, c))
        Utils.assert((lhsTypes zip rhsTypes).forall 
            { i =>  (i._1 matches i._2._1) && !i._2._2}, 
            "LHSS and RHSS have conflicting types: " + s + ".\nTypes: " + lhsTypes.toString + "/" + rhsTypes.toString);
        Utils.assert(lhss.distinct.size == lhss.size, "LHSS contains identical variables: " + s)
      case IfElseStmt(e, t, f) => 
        checkExpr(e,c); 
        val eType = typeOf(e,c)
        assertNoTemporalType(eType,e)
        Utils.assert(transitiveType(eType._1,c) == BoolType(), 
            "Conditionals in if statements must have boolean type.");
        (t ++ f).foreach { x => checkStmt(x,c) };
      case ForStmt(id,_,body) => 
        Utils.assert(!(externalDecls.exists { x => x.name == id.name }), 
            "For Loop counter " + id + " redeclared");
        var c2: Context = c.copyContext();
        // FIXME: hack converting ConstIdentifier to Identifier. //
        c2.inputs = c.inputs ++ Map(Identifier(id.name) -> IntType());
        body.foreach{x => checkStmt(x,c2)}
      case CaseStmt(body) => body.foreach { x =>
        checkExpr(x._1,c);
        val xType = typeOf(x._1,c)
        Utils.assert(transitiveType(xType._1,c) == BoolType() && !xType._2, 
            "Expected boolean conditional within case statement guard");
        x._2.foreach { y => checkStmt(y,c) } 
        }
      case ProcedureCallStmt(id, lhss, args) =>
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
  def typeOf(e: Expr, c: Context) : (Type, Boolean) = {
    def assertBoolType(t: Type) : Unit = {
      Utils.assert(transitiveType(t,c) == BoolType() || t == TemporalType(), 
          "Expected expression " + t + " to have type Bool (or be a temporal formula).")
    }
    def typeOfBinaryBooleanOperator (l: Expr, r: Expr) : (Type, Boolean) = {
        val (typeL, tempL) = typeOf(l,c)
        assertBoolType(typeL)
        val (typeR, tempR) = typeOf(r,c)
        assertBoolType(typeR)
        return (BoolType(), tempL || tempR)
    }
    def typeOfUnaryBooleanOperator(e: Expr) : (Type, Boolean) = {
      val (typeE, tempE) = typeOf(e,c)
      assertBoolType(typeE)
      return (BoolType(), tempE)
    }
    
    e match {
      // Temporal operators
      case OperatorApplication(op,es) =>
        lazy val types = es.map { e => typeOf (e,c.contextWithOperatorApplication(op)) }
        lazy val temporalArgs = types.exists { x => x._2}
        return op match {
          case AddOp() | SubOp() | MulOp() | LTOp() | LEOp() | GTOp() | GEOp() => 
            throw new Utils.RuntimeError("Polymorphic operators not expected here.")
          case IntAddOp() | IntSubOp() | IntMulOp() | BVAddOp(_) | BVSubOp(_) | BVMulOp(_) => {
            Utils.assert(types.size == 2, "Expected two arguments to arithmetic operators.")
            Utils.assert(types(0) == types(1), "Operands to arithmetic operators must be of the same type in expression: " + e.toString + ". Types are " + types(0).toString + " and " + types(1).toString + ".")
            (types.head._1, temporalArgs)
          }
          case BVAndOp(_) | BVOrOp(_) | BVXorOp(_) => {
            Utils.assert(types.size == 2, "Expected two arguments to arithmetic operators.")
            Utils.assert(types(0) == types(1), "Operands to arithmetic operators must be of the same type in expression: " + e.toString + ". Types are " + types(0).toString + " and " + types(1).toString + ".")
            (types.head._1, temporalArgs)
          }
          case BVNotOp(_) => {
            Utils.assert(types.size == 1, "Expected two arguments to arithmetic operators.")
            (types.head._1, temporalArgs)
          }
          case ExtractOp(slice) => {
            Utils.assert(types.size == 1, "Expected one argument to bitvector extract operator.")
            Utils.assert(types(0)._1.isBitVector, "Argument to bitvector extract must be of type bitvector.")
            (BitVectorType(slice.hi - slice.lo + 1), temporalArgs)
          }
          case IntLTOp() | IntLEOp() | IntGTOp() | IntGEOp() |
               BVLTOp(_) | BVLEOp(_) | BVGTOp(_) | BVGEOp(_) => {
            Utils.assert(types.size == 2, "Expected two arguments to comparison operators.")
            Utils.assert(types(0) == types(1), "Operands to comparison operators must be of the same type.")
            Utils.assert(types.forall(_._1.isNumeric), "Arguments to comparison operators must be numeric.")
            (BoolType(), temporalArgs)
          }
          case qOp : QuantifiedBooleanOperator =>
            Utils.assert(types.size == 1, "Expected one argument to quantifier.")
            Utils.assert(types(0)._1.isBool, "Argument to quantifier must be a boolean.")
            (BoolType(), temporalArgs)
          case ConjunctionOp() | DisjunctionOp() | IffOp() | ImplicationOp() => {
            Utils.assert(types.size == 2, "Expected two arguments to Boolean operators.")
            Utils.assert(types(0)._1.isBool, "First operand to Boolean operator must be of Boolean type. Instead got: " + types(0).toString + "; expression: " + e.toString)
            Utils.assert(types(1)._1.isBool, "Second operand to Boolean operator must be of Boolean type. Instead got: " + types(0).toString + "; expression: " + e.toString)
            (BoolType(), temporalArgs)
          }
          case NegationOp() => {
            Utils.assert(types.size == 1, "Expected one argument to Boolean negation operator.")
            Utils.assert(types(0)._1.isBool, "Operand to Boolean negation operator must be of Boolean type. Instead got: " + types(0).toString + "; expression: " + e.toString)
            (BoolType(), temporalArgs)
          }
          case EqualityOp() | InequalityOp() => {
            Utils.assert(types.size == 2, "Expected two arguments to comparison operators.")
            Utils.assert(types(0) == types(1), "Operands to equality/inequality must be of the same type.")
            (BoolType(), temporalArgs)
          }
          case UntilTemporalOp() | WUntilTemporalOp() | ReleaseTemporalOp() => {
            Utils.assert(types.size == 2, "Expected two operand to temporal operator: " + op)
            Utils.assert(types.forall((t) => t._1.isTemporal || t._1.isBool), "Operands to temporal operator " + op + " must be Boolean or temporal.")
            (TemporalType(), true)
          }
          case FinallyTemporalOp() | GloballyTemporalOp() | NextTemporalOp() => {
            Utils.assert(types.size == 1, "Expected one operand to temporal operator: " + op)
            Utils.assert(types.forall((t) => t._1.isTemporal || t._1.isBool), "Operand to temporal operator " + op + " must be Boolean or temporal.")
            (TemporalType(), true)
          }
          case RecordSelect(r) => {
            Utils.assert(types.size == 1, "Incorrect number of operands to record select. ")
            Utils.assert(types(0)._1.isProduct, "Operand to record select must be a product type.")
            val recType = (types(0)._1.asInstanceOf[ProductType], types(0)._2)
            Utils.assert(recType._1.hasField(r), "Field '" + r + "' does not exist in product type: " + recType.toString)
            (recType._1.fieldType(r).get, recType._2)
          }
          case _ => {
            throw new Utils.UnimplementedException("Operator not implemented yet: " + op)
          }
        }
      case Tuple(values) => 
        val valTypes = values.map(typeOf(_,c))
        val temporal = valTypes.exists(_._2)
        return (TupleType(valTypes.map(_._1)), temporal)
      case ArraySelectOperation(a,index) =>
        val (typ,temporal) = typeOf(a,c)
        Utils.assert(!temporal, "Array types may not have temporal subformulas")
        Utils.assert(transitiveType(typ,c).isInstanceOf[ArrayType],
            "expected array type: " + e)
        Utils.assert((typ.asInstanceOf[ArrayType].inTypes zip index).
            forall { x => x._1 == typeOf(x._2,c)._1 }, "Array Select operand type mismatch: " + e)
        return (typ.asInstanceOf[ArrayType].outType, false) //select returns the range type
      case ArrayStoreOperation(a,index,value) =>
        val (typ,temporal) = typeOf(a,c)
        Utils.assert(!temporal, "Array types may not have temporal subformulas")
        Utils.assert(transitiveType(typ,c).isInstanceOf[ArrayType], "expected array type: " + e)
        Utils.assert((typ.asInstanceOf[ArrayType].inTypes zip index).
            forall { x => x._1 == typeOf(x._2,c)._1 }, "Array Store operand type mismatch: " + e)
        Utils.assert(typ.asInstanceOf[ArrayType].outType == typeOf(value,c)._1, 
            "Array Store value type mismatch")
        return (typ, false) //store returns the new array
      case FuncApplication(f,args) =>
        val (typ,temporal) = typeOf(f,c)
        Utils.assert(!temporal, "Array types may not have temporal subformulas")
        Utils.assert(transitiveType(typ,c).isInstanceOf[MapType],"Expected Map Type " + e);
        Utils.assert((typ.asInstanceOf[MapType].inTypes.size == args.size), 
          "Function application has bad number of arguments: " + e);
        Utils.assert((typ.asInstanceOf[MapType].inTypes zip args).forall{i => i._1 == typeOf(i._2,c)._1}, 
          "Function application has bad types of arguments: " + e)
        return (typ.asInstanceOf[MapType].outType, false)
      case ITE(cond,t,f) =>
        val condType = typeOf (cond,c)
        assertBoolType(condType._1);
        val tType = typeOf (t,c)
        val fType = typeOf (f,c)
        Utils.assert(tType._1 == fType._1, 
            "ITE true and false expressions have different types: " + e)
        return (tType._1, tType._2 || fType._2)
      case Lambda(ids,le) =>
        var c2: Context = c.copyContext()
        c2.inputs = c.inputs ++ (ids.map(i => i._1 -> i._2).toMap)
        Utils.assert(ids.forall { i => transitiveType(i._2,c) == BoolType() || 
          transitiveType(i._2,c) == IntType() }, 
            "Cannot construct Lambda expressions of non-primitive types: " + le)
        val t = typeOf(le,c2)
        Utils.assert(!t._2, "What do you need a Lambda expression with temporal type for!?")
        return (MapType(ids.map(i => i._2), t._1), false) //Lambda expr returns a map type
      case id : IdentifierBase =>
        val vars = (c.constants ++ c.variables ++ c.inputs ++ c.outputs ++ c.enumeratedConstants ++ c.forallVars ++ c.existsVars)
        var someId = vars.get(Identifier(id.name))
        if (someId.isDefined) {
          (someId.get, false)
        } else {
          val someFType = c.functions.get(Identifier(id.name))
          Utils.assert(someFType.isDefined, "Unable to find identifier in function map: " + id.name)
          (someFType.get.typ, false)
        }
      case IntLit(n) => (IntType(), false)
      case BoolLit(b) => (BoolType(), false)
      case BitVectorLit(bv, w) => (BitVectorType(w), false)
      case _ => throw new Utils.RuntimeError("Unsupported construct: " + e.toString())
    }    
  }
  
  def checkExpr(e: Expr, c: Context) : Unit = {
    val externalDecls : List[Identifier] = c.externalDecls()
     e match { //check that all identifiers in e have been declared
       case OperatorApplication(op,args) =>
         args.foreach(checkExpr(_, c.contextWithOperatorApplication(op)))
       case ArraySelectOperation(a,index) => checkExpr(a,c); index.foreach { x => checkExpr(x,c) }
       case ArrayStoreOperation(a,index,value) => 
         checkExpr(a,c); index.foreach { x => checkExpr(x,c) }; checkExpr(value, c);
       case FuncApplication(f,args) => checkExpr(f,c); args.foreach { x => checkExpr(x,c) }
       case ITE(cond,t,f) => 
         checkExpr(cond,c) 
         val tTypeCond = transitiveType(typeOf(cond, c)._1, c)
         Utils.assert(tTypeCond.isInstanceOf[BoolType], 
             "Conditional must have boolean type in expression " + e + " but has type " + tTypeCond)
         checkExpr(t,c) 
         checkExpr(f,c)
         Utils.assert(transitiveType(typeOf(t, c)._1, c) == transitiveType(typeOf(f, c)._1, c), 
             "The branches in the ITE expression " + e + " have different types.")
       case Lambda(ids,le) => ids.foreach { 
           x => checkType(x._2,c);
           Utils.assert(transitiveType(x._2,c).isInstanceOf[IntType] || 
               transitiveType(x._2,c).isInstanceOf[BoolType],
             "Lambda indexed by non-primitive type in expression " + e);
         }
         ids.foreach{ x => Utils.assert((externalDecls ++ ids.map(i => i._1)).
             count { i => i.name == x._1.name } == 1, "Lambda argument has a redeclaration") }
         var c2: Context = c.copyContext()
         c2.inputs = c.inputs ++ (ids.map(i => i._1 -> i._2).toMap)
         checkExpr(le,c2);
       case Identifier(id) => 
         Utils.assert((c.constants.keys ++ c.functions.keys ++ c.inputs.keys ++ c.outputs.keys ++ c.variables.keys ++ c.enumeratedConstants.keys ++ c.forallVars.keys ++ c.existsVars.keys).
         exists{i => i.name == id}, "Identifier " + id + " not found");
       case _ => ()
     }
    typeOf(e,c) //do type checking on e
  }
}