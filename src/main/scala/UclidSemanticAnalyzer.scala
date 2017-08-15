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
    procedures = m_procs.map(x => x.asInstanceOf[T1].id -> x.asInstanceOf[T1].sig).toMap
    
    type T2 = UclFunctionDecl
    val m_funcs = m.decls.filter { x => x.isInstanceOf[T2] }
    functions = m_funcs.map(x => x.asInstanceOf[T2].id -> x.asInstanceOf[T2].sig).toMap
    
    type T3 = UclStateVarDecl
    val m_vars = m.decls.filter { x => x.isInstanceOf[T3] }
    variables = m_vars.map(x => x.asInstanceOf[T3].id -> x.asInstanceOf[T3].typ).toMap
    
    type T4 = UclInputVarDecl
    val m_inputs = m.decls.filter { x => x.isInstanceOf[T4] }
    inputs = m_inputs.map(x => x.asInstanceOf[T4].id -> x.asInstanceOf[T4].typ).toMap
    
    type T5 = UclOutputVarDecl
    val m_outputs = m.decls.filter { x => x.isInstanceOf[T5] }
    outputs = m_outputs.map(x => x.asInstanceOf[T5].id -> x.asInstanceOf[T5].typ).toMap
    
    type T6 = UclConstantDecl
    val m_consts = m.decls.filter { x => x.isInstanceOf[T6] }
    constants = m_consts.map(x => x.asInstanceOf[T6].id -> x.asInstanceOf[T6].typ).toMap

    type T7 = UclTypeDecl
    val m_typedecls = m.decls.filter { x => x.isInstanceOf[T7] }
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
}

object UclidSemanticAnalyzer {
  
  def assert(b: Boolean, err: String) : Unit = {
    if (!b) { println("ERROR: " + err); System.exit(0); } //throw new Exception(err); }
  }
  
  def checkSemantics(m: UclModule) : Unit = {
    var c: Context = new Context()
    c.extractContext(m)
    check(m,c)
    m.decls.foreach { x => check(x,c) }
  }
  
  def check(m: UclModule, c: Context) : Unit = {
    //check module level stuff
    def checkRedeclarationAndTypes(decls: Map[UclIdentifier, UclType]) : Unit = {
      val externalDecls : Iterable[UclIdentifier] = c.constants.keys ++ c.functions.keys ++ c.inputs.keys ++ 
        c.outputs.keys ++ c.types.keys ++ c.variables.keys ++ c.procedures.keys
      decls.foreach(i => {
        assert(externalDecls.count { x => x.value == i._1.value } == 1, 
          "Declaration " + i + " has conflicting name")
        if (i._2.isInstanceOf[UclSynonymType]) { //check that the type is acceptable
          assert(c.types.keys.exists { j => j.value == i._2.asInstanceOf[UclSynonymType].id.value }, 
            "Declaration " + i + " has unknown type")
        }
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
    val externalDecls : Iterable[UclIdentifier] = c.constants.keys ++ c.functions.keys ++ c.inputs.keys ++ 
      c.outputs.keys ++ c.types.keys ++ c.variables.keys ++ c.procedures.keys
    d match {
      case UclProcedureDecl(id,sig,decls,body) =>
        assert((sig.inParams.map(i => i._1) ++ sig.outParams.map(i => i._1)).distinct.size ==
          (sig.inParams.map(i => i._1) ++ sig.outParams.map(i => i._1)).size,
          "Signature of procedure " + id + " contains arguments of the same name")
        (sig.inParams ++ sig.outParams).foreach(i => { 
          //check that name is not reused
          assert((externalDecls ++ sig.inParams.map(j => j._1) ++ sig.outParams.map(j => j._1)).
              count { x => x.value == i._1.value } == 1, 
              "Signature of procedure " + id + " contains redeclaration: " + i)
          if (i._2.isInstanceOf[UclSynonymType]) { //check that the type are acceptable
            assert(c.types.keys.exists { j => j.value == i._2.asInstanceOf[UclSynonymType].id.value }, 
                "Signature of procedure " + id + " contains unknown type: " + i)
          }
        })
     
        decls.foreach { i => {
          //check that name is not reused
          assert((externalDecls ++ decls.map(j => j.id)).count { x => x.value == i.id.value } == 1, 
              "Local variable " + i + " redeclared")
          if (i.typ.isInstanceOf[UclSynonymType]) { //check that the type is acceptable
            assert(c.types.keys.exists { j => j.value == i.typ.asInstanceOf[UclSynonymType].id.value }, 
              "Local variable " + i + " has unknown type")
          }
        } }
                   
        var c2: Context = c.copyContext()
        c2.inputs = c.inputs ++ (sig.inParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c.variables ++ (sig.outParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c2.variables ++ (decls.map(i => i.id -> i.typ).toMap)
        body.foreach { x => check(x,c2) }
        
      case UclFunctionDecl(id,sig) =>
        assert((sig.args.map(i => i._1)).distinct.size == (sig.args.map(i => i._1)).size, 
            "Signature of function " + id + " contains arguments of the same name")
        sig.args.foreach(i => { 
          //check that name is not reused
          assert((externalDecls ++ sig.args.map(j => j._1)).
              count { x => x.value == i._1.value } == 1, 
              "Signature of function " + id + " contains redeclaration: " + i)
          if (i._2.isInstanceOf[UclSynonymType]) { //check that the type are acceptable
            assert(c.types.keys.exists { j => j.value == i._2.asInstanceOf[UclSynonymType].id.value }, 
                "Signature of function " + id + " contains unknown type: " + i)
          }
        })
      case UclTypeDecl(id,typ) => check(typ, c)
      case UclStateVarDecl(id, typ) => check(typ, c)
      case UclInputVarDecl(id,typ) => check(typ, c)
      case UclOutputVarDecl(id, typ) => check(typ, c)
      case UclConstantDecl(id, typ) => check(typ, c)
      case _ => ()
    }
  }
  
  def check(typ: UclType, c: Context) : Unit = {
    val externalDecls : Iterable[UclIdentifier] = c.constants.keys ++ c.functions.keys ++ c.inputs.keys ++ 
      c.outputs.keys ++ c.types.keys ++ c.variables.keys ++ c.procedures.keys
    if (typ.isInstanceOf[UclEnumType]) {
      typ.asInstanceOf[UclEnumType].ids.foreach { i => 
        assert((externalDecls ++ typ.asInstanceOf[UclEnumType].ids).
        count{ j => j.value == i.value } == 1, "Enum " + typ + " has a redeclaration")
      }
    } else if (typ.isInstanceOf[UclRecordType]) {
      val t = typ.asInstanceOf[UclRecordType]
      //assert no map type
      t.fields.foreach { i => 
        assert((externalDecls ++ t.fields.map(a => a._1)).count { j => j.value == i._1.value } == 1, 
            "Record " + typ + " has a redeclaration")
        //assert no maps
        assert(!(i._2.isInstanceOf[UclMapType] || i._2.isInstanceOf[UclArrayType]), 
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
      assert(c.types.keys.exists { x => x.value == typ.asInstanceOf[UclSynonymType].id.value }, 
          "Synonym Type " + typ + " does not exist.")
    }
  }
  
  def check(lhs: UclLhs, c: Context) : Unit = {
    lhs.mapSelect match {
      case Some(ms) => ms.index.foreach { x => check(x,c) }
      case None => ()
    }
    lhs.recordSelect match {
      case Some(rs) => rs.foreach { x =>  }
      case None => ()
    }
  }
  
  def check(s: UclStatement, c: Context) : Unit = {
    val externalDecls : Iterable[UclIdentifier] = c.constants.keys ++ c.functions.keys ++ c.inputs.keys ++ 
      c.outputs.keys ++ c.types.keys ++ c.variables.keys ++ c.procedures.keys
    s match {
      case UclAssertStmt(e) => check(e,c)
      case UclAssumeStmt(e) => check(e,c)
      case UclHavocStmt(id) => 
        assert(c.variables.keys.exists { x => x.value == id.value }, 
            "Statement " + s + " updates unknown variable")
      case UclAssignStmt(lhss, rhss) => lhss.foreach{ x => check(x,c) }; rhss.foreach { x => check(x,c) }
      case UclIfElseStmt(e, t, f) => check(e,c); (t ++ f).foreach { x => check(x,c) };
      case UclForStmt(_,_,body) => body.foreach{x => check(x,c)}
      case UclCaseStmt(body) => body.foreach { x => check(x._1,c);  x._2.foreach { y => check(y,c) } }
      case UclProcedureCallStmt(id, lhss, args) =>
        assert(c.procedures.keys.exists { x => x.value == id.value }, "Calling unknown procedure " + id)
        lhss.foreach{ x => check(x,c) }
        args.foreach{ x => check(x,c) }
    }
  }
  
  def check(e: UclExpr, c: Context) : Unit = {
    val externalDecls : Iterable[UclIdentifier] = c.constants.keys ++ c.functions.keys ++ c.inputs.keys ++ 
      c.outputs.keys ++ c.types.keys ++ c.variables.keys ++ c.procedures.keys
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
         assert(c.functions.keys.exists{x => x.value == id.value}, id + " is not a function");
         op.args.foreach { x => check(x,c) }
       case UclITE(e,t,f) => check(e,c); check(t,c); check(f,c);
       case UclLambda(ids,e) => ids.foreach { 
           x => check(x._2,c);
           assert(x._2.isInstanceOf[UclIntType] || x._2.isInstanceOf[UclBoolType],
             "Lambda indexed by non-primitive type");
         }
         ids.foreach{ x => assert((externalDecls ++ ids.map(i => i._1)).
             count { i => i.value == x._1.value } == 1, "Lambda argument has a redeclaration") }
         var c2: Context = c.copyContext()
         c2.inputs = c.inputs ++ (ids.map(i => i._1 -> i._2).toMap)
         check(e,c2);
       case UclIdentifier(id) => 
         assert((c.constants.keys ++ c.inputs.keys ++ c.outputs.keys ++ c.variables.keys).
         exists{i => i.value == id}, "Identifier " + id + " not found");
       case _ => ()
     } 
  }
}