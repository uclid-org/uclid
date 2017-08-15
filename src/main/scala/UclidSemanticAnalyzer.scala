 /* Created by Rohit Sinha on 5/28/15.
 */

class Context {
  var procedures: Map[UclIdentifier, UclProcedureSig] = _
  var functions: Map[UclIdentifier, UclFunctionSig] = _
  var variables: Map[UclIdentifier, UclType] = _
  var inputs: Map[UclIdentifier, UclType] = _
  var outputs: Map[UclIdentifier, UclType] = _
  var constants: Map[UclIdentifier, UclType] = _
  var types : Map[UclIdentifier, UclType] = _
  
  override def toString = variables.toString
  
  def extractContext(m: UclModule) = {
    type T1 = UclProcedureDecl
    val m_procs = m.decls.filter { x => x.isInstanceOf[T1] }
    UclidUtils.assert(m_procs.map(i => i.asInstanceOf[T1].id).distinct.size == 
      m_procs.map(i => i.asInstanceOf[T1].id).size, "Multiple procedures with identical names")
    procedures = m_procs.map(x => x.asInstanceOf[T1].id -> x.asInstanceOf[T1].sig).toMap
    
    type T2 = UclFunctionDecl
    val m_funcs = m.decls.filter { x => x.isInstanceOf[T2] }
    UclidUtils.assert(m_funcs.map(i => i.asInstanceOf[T2].id).distinct.size == 
      m_funcs.map(i => i.asInstanceOf[T2].id).size, "Multiple functions with identical names")
    functions = m_funcs.map(x => x.asInstanceOf[T2].id -> x.asInstanceOf[T2].sig).toMap
    
    type T3 = UclStateVarDecl
    val m_vars = m.decls.filter { x => x.isInstanceOf[T3] }
    UclidUtils.assert(m_vars.map(i => i.asInstanceOf[T3].id).distinct.size == 
      m_vars.map(i => i.asInstanceOf[T3].id).size, "Multiple variables with identical names")
    variables = m_vars.map(x => x.asInstanceOf[T3].id -> x.asInstanceOf[T3].typ).toMap
    
    type T4 = UclInputVarDecl
    val m_inputs = m.decls.filter { x => x.isInstanceOf[T4] }
    UclidUtils.assert(m_inputs.map(i => i.asInstanceOf[T4].id).distinct.size == 
      m_inputs.map(i => i.asInstanceOf[T4].id).size, "Multiple inputs with identical names")
    inputs = m_inputs.map(x => x.asInstanceOf[T4].id -> x.asInstanceOf[T4].typ).toMap
    
    type T5 = UclOutputVarDecl
    val m_outputs = m.decls.filter { x => x.isInstanceOf[T5] }
    UclidUtils.assert(m_outputs.map(i => i.asInstanceOf[T5].id).distinct.size == 
      m_outputs.map(i => i.asInstanceOf[T5].id).size, "Multiple outputs with identical names")
    outputs = m_outputs.map(x => x.asInstanceOf[T5].id -> x.asInstanceOf[T5].typ).toMap
    
    type T6 = UclConstantDecl
    val m_consts = m.decls.filter { x => x.isInstanceOf[T6] }
    UclidUtils.assert(m_consts.map(i => i.asInstanceOf[T6].id).distinct.size == 
      m_consts.map(i => i.asInstanceOf[T6].id).size, "Multiple constants with identical names")
    constants = m_consts.map(x => x.asInstanceOf[T6].id -> x.asInstanceOf[T6].typ).toMap

    type T7 = UclTypeDecl
    val m_typedecls = m.decls.filter { x => x.isInstanceOf[T7] }
    UclidUtils.assert(m_typedecls.map(i => i.asInstanceOf[T7].id).distinct.size == 
      m_typedecls.map(i => i.asInstanceOf[T7].id).size, "Multiple typedecls with identical names")
    types = m_typedecls.map(x => x.asInstanceOf[T7].id -> x.asInstanceOf[T7].typ).toMap
  }
  
  def copyContext() : Context = {
    var copy: Context = new Context()
    copy.constants = this.constants
    copy.functions = this.functions
    copy.inputs = this.inputs
    copy.outputs = this.outputs
    copy.procedures = this.procedures
    copy.types = this.types
    copy.variables = this.variables
    return copy
  }
  
  def externalDecls() : List[UclIdentifier] = {
    return this.constants.keys.toList ++ this.functions.keys.toList ++ this.inputs.keys.toList ++ 
      this.outputs.keys.toList ++ this.types.keys.toList ++ this.variables.keys.toList ++ 
      this.procedures.keys.toList
  }
}

object UclidSemanticAnalyzer {
  def checkSemantics(m: UclModule) : Unit = {
    var c: Context = new Context()
    c.extractContext(m)
    check(m,c)
    m.decls.foreach { x => check(x,c) }
  }
  
  def check(m: UclModule, c: Context) : Unit = {
    //check module level stuff
    def checkRedeclarationAndTypes(decls: Map[UclIdentifier, UclType]) : Unit = {
      val externalDecls : List[UclIdentifier] = c.externalDecls()
      decls.foreach(i => {
        UclidUtils.assert(externalDecls.count { x => x.value == i._1.value } == 1, 
          "Declaration " + i + " has conflicting name")
      })
    }
    checkRedeclarationAndTypes(c.constants)
    checkRedeclarationAndTypes(c.inputs)
    checkRedeclarationAndTypes(c.outputs)
    checkRedeclarationAndTypes(c.variables)
    checkRedeclarationAndTypes(c.types)
    
    m.decls.foreach { x => check(x,c) }
  }
  
  def check(d: UclDecl, c: Context) : Unit = {
    val externalDecls : List[UclIdentifier] = c.externalDecls()
    d match {
      case UclProcedureDecl(id,sig,decls,body) =>
        UclidUtils.assert((sig.inParams.map(i => i._1) ++ sig.outParams.map(i => i._1)).distinct.size ==
          (sig.inParams.map(i => i._1) ++ sig.outParams.map(i => i._1)).size,
          "Signature of procedure " + id + " contains arguments of the same name")
        (sig.inParams ++ sig.outParams).foreach(i => { 
          //check that name is not reused
          UclidUtils.assert((externalDecls ++ sig.inParams.map(j => j._1) ++ sig.outParams.map(j => j._1)).
              count { x => x.value == i._1.value } == 1, 
              "Signature of procedure " + id + " contains redeclaration: " + i)
          if (i._2.isInstanceOf[UclSynonymType]) { //check that the type are acceptable
            UclidUtils.assert(c.types.keys.exists { j => j.value == i._2.asInstanceOf[UclSynonymType].id.value }, 
                "Signature of procedure " + id + " contains unknown type: " + i)
          }
        })
     
        decls.foreach { i => {
          //check that name is not reused
          UclidUtils.assert((externalDecls ++ decls.map(j => j.id) ++ 
              sig.inParams.map(j => j._1) ++ sig.outParams.map(j => j._1)).
              count { x => x.value == i.id.value } == 1, "Local variable " + i + " redeclared")
          if (i.typ.isInstanceOf[UclSynonymType]) { //check that the type is acceptable
            UclidUtils.assert(c.types.keys.exists { j => j.value == i.typ.asInstanceOf[UclSynonymType].id.value }, 
              "Local variable " + i + " has unknown type")
          }
        } }
                   
        var c2: Context = c.copyContext()
        c2.inputs = c.inputs ++ (sig.inParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c.variables ++ (sig.outParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c2.variables ++ (decls.map(i => i.id -> i.typ).toMap)
        body.foreach { x => check(x,c2) }
        
      case UclFunctionDecl(id,sig) =>
        UclidUtils.assert((sig.args.map(i => i._1)).distinct.size == (sig.args.map(i => i._1)).size, 
            "Signature of function " + id + " contains arguments of the same name")
        sig.args.foreach(i => { 
          //check that name is not reused
          UclidUtils.assert((externalDecls ++ sig.args.map(j => j._1)).
              count { x => x.value == i._1.value } == 1, 
              "Signature of function " + id + " contains redeclaration: " + i)
          if (i._2.isInstanceOf[UclSynonymType]) { //check that the type are acceptable
            UclidUtils.assert(c.types.keys.exists { j => j.value == i._2.asInstanceOf[UclSynonymType].id.value }, 
                "Signature of function " + id + " contains unknown type: " + i)
          }
        })
      case UclTypeDecl(id,typ) => check(typ, c)
      case UclStateVarDecl(id, typ) => check(typ, c)
      case UclInputVarDecl(id,typ) => check(typ, c)
      case UclOutputVarDecl(id, typ) => check(typ, c)
      case UclConstantDecl(id, typ) => check(typ, c)
      case UclInitDecl(body) => body.foreach{x => check(x,c)}
      case UclNextDecl(body) => body.foreach{x => check(x,c)}
    }
  }
  
  def check(typ: UclType, c: Context) : Unit = {
    val externalDecls : List[UclIdentifier] = c.externalDecls()
    if (typ.isInstanceOf[UclEnumType]) {
      typ.asInstanceOf[UclEnumType].ids.foreach { i => 
        UclidUtils.assert((externalDecls ++ typ.asInstanceOf[UclEnumType].ids).
        count{ j => j.value == i.value } == 1, "Enum " + typ + " has a redeclaration")
      }
    } else if (typ.isInstanceOf[UclRecordType]) {
      val t = typ.asInstanceOf[UclRecordType]
      //assert no map type
      t.fields.foreach { i => 
        //UclidUtils.assert((externalDecls ++ t.fields.map(a => a._1)).count { j => j.value == i._1.value } == 1, 
        //    "Record " + typ + " has a redeclaration")
        //assert no maps
        UclidUtils.assert(!(i._2.isInstanceOf[UclMapType] || i._2.isInstanceOf[UclArrayType]), 
            "Records cannot contain maps or arrays")
        check(i._2, c)
      }
    } else if (typ.isInstanceOf[UclMapType]) {
      typ.asInstanceOf[UclMapType].inTypes.foreach { i => check(i,c) }
      check(typ.asInstanceOf[UclMapType].outType, c)
    } else if (typ.isInstanceOf[UclArrayType]) {
      typ.asInstanceOf[UclArrayType].inTypes.foreach { i => check(i,c) }
      check(typ.asInstanceOf[UclArrayType].outType, c)
    } else if (typ.isInstanceOf[UclSynonymType]) {
      UclidUtils.assert(c.types.keys.exists { x => x.value == typ.asInstanceOf[UclSynonymType].id.value }, 
          "Synonym Type " + typ + " does not exist.")
    }
  }
  
  def check(lhs: UclLhs, c: Context) : Unit = {
    UclidUtils.assert((c.outputs.keys ++ c.variables.keys).exists { x => x.value == lhs.id.value }, 
        "LHS variable " + lhs.id + " does not exist")
    var intermediateType = (c.outputs ++ c.variables)(lhs.id)
    lhs.mapSelect match {
      case Some(ms) => 
        //assert that lhs.id is a map or array
        UclidUtils.assert(intermediateType.isInstanceOf[UclArrayType],
            "Cannot use select on non-array " + lhs.id)
        intermediateType = intermediateType.asInstanceOf[UclArrayType].outType
        ms.index.foreach { x => check(x,c) }
      case None => ()
    }
    lhs.recordSelect match {
      case Some(rs) => 
        UclidUtils.assert(intermediateType.isInstanceOf[UclRecordType], "Expected record type")
        rs.foreach { x => 
          UclidUtils.assert(intermediateType.asInstanceOf[UclRecordType].fields.
              exists { i => i._1.value == x.id.value }, "Field " + x + " not found")
          intermediateType.asInstanceOf[UclRecordType].fields.find(i => i._1.value == x.id.value) 
              match { case Some(x) => intermediateType = x._2; 
                      case None => UclidUtils.assert(false, "Should not get here") }
        }
      case None => ()
    }
  }
  
  def check(s: UclStatement, c: Context) : Unit = {
    val externalDecls : List[UclIdentifier] = c.externalDecls()
    s match {
      case UclAssertStmt(e) => check(e,c)
      case UclAssumeStmt(e) => check(e,c)
      case UclHavocStmt(id) => 
        UclidUtils.assert((c.variables.keys ++ c.outputs.keys).exists { x => x.value == id.value }, 
            "Statement " + s + " updates unknown variable")
      case UclAssignStmt(lhss, rhss) => lhss.foreach{ x => check(x,c) }; rhss.foreach { x => check(x,c) }
      case UclIfElseStmt(e, t, f) => check(e,c); (t ++ f).foreach { x => check(x,c) };
      case UclForStmt(id,_,body) => 
         var c2: Context = c.copyContext()
         c2.inputs = c.inputs ++ Map(id -> UclIntType())
        body.foreach{x => check(x,c2)}
      case UclCaseStmt(body) => body.foreach { x => check(x._1,c);  x._2.foreach { y => check(y,c) } }
      case UclProcedureCallStmt(id, lhss, args) =>
        UclidUtils.assert(c.procedures.keys.exists { x => x.value == id.value }, "Calling unknown procedure " + id)
        lhss.foreach{ x => check(x,c) }
        args.foreach{ x => check(x,c) }
    }
  }
  
  def check(e: UclExpr, c: Context) : Unit = {
    val externalDecls : List[UclIdentifier] = c.externalDecls()
     e match {
       case UclEquivalence(l,r) => check(r,c); check(l,c);
       case UclImplication(l,r) => check(r,c); check(l,c);
       case UclConjunction(l,r) => check(r,c); check(l,c);
       case UclDisjunction(l,r) => check(r,c); check(l,c);
       case UclRelationOperation(_,l,r) => check(r,c); check(l,c);
       case UclConcatOperation(l,r) => throw new Exception("Concatenation Unsupported")
       case UclExtractOperation(l,r) => throw new Exception("Extraction Unsupported")
       case UclAddOperation(l,r) => check(r,c); check(l,c);
       case UclMulOperation(l,r) => check(r,c); check(l,c);
       case UclUnaryOperation(_,e) => check(e,c);
       case UclMapSelectOperation(e,op) => check(e,c); op.index.foreach { x => check(x,c) }
       case UclMapStoreOperation(e,op) => 
         check(e,c); op.index.foreach { x => check(x,c) }; check(op.value, c);
       case UclFuncAppOperation(id,op) => 
         UclidUtils.assert(c.functions.keys.exists{x => x.value == id.value}, id + " is not a function");
         op.args.foreach { x => check(x,c) }
       case UclITE(e,t,f) => check(e,c); check(t,c); check(f,c);
       case UclLambda(ids,e) => ids.foreach { 
           x => check(x._2,c);
           UclidUtils.assert(x._2.isInstanceOf[UclIntType] || x._2.isInstanceOf[UclBoolType],
             "Lambda indexed by non-primitive type");
         }
         ids.foreach{ x => UclidUtils.assert((externalDecls ++ ids.map(i => i._1)).
             count { i => i.value == x._1.value } == 1, "Lambda argument has a redeclaration") }
         var c2: Context = c.copyContext()
         c2.inputs = c.inputs ++ (ids.map(i => i._1 -> i._2).toMap)
         check(e,c2);
       case UclIdentifier(id) => 
         UclidUtils.assert((c.constants.keys ++ c.inputs.keys ++ c.outputs.keys ++ c.variables.keys).
         exists{i => i.value == id}, "Identifier " + id + " not found");
       case _ => ()
     } 
  }
}