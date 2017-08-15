
/**
 * @author rohitsinha
 */
package uclid {
  import uclid.lang._
  import lang.UclidSemanticAnalyzer
  import lang.Context
  import lang.UclType
  import lang.UclStatement
  import lang.UclSkipStmt
  import lang.UclProcedureDecl
  import lang.UclProcedureCallStmt
  import lang.Operator
  import lang.IntLit
  import lang.UclNegation
  import lang.MulOp
  import lang.UclModule
  import lang.UclMapType
  import lang.UclLhs
  import lang.UclLambda
  import lang.LTOp
  import lang.LEOp
  import lang.UclIntType
  import lang.UclImplication
  import lang.UclIfElseStmt
  import lang.Identifier
  import lang.UclITE
  import lang.UclOperatorApplication
  import lang.UclHavocStmt
  import lang.GTOp
  import lang.GEOp
  import lang.UclFuncApplication
  import lang.UclForStmt
  import lang.Expr
  import lang.UclEquality
  import lang.UclDisjunction
  import lang.UclConjunction
  import lang.UclCaseStmt
  import lang.BoolLit
  import lang.UclBoolType
  import lang.UclBiImplication
  import lang.UclAssumeStmt
  import lang.UclAssignStmt
  import lang.UclAssertStmt
  import lang.UclArrayType
  import lang.UclArrayStoreOperation
  import lang.UclArraySelectOperation
  import lang.AddOp
  
  object UniqueIdGenerator {
    var i : Int = 0;
    def unique() : Int = {i = i + 1; return i}
  }
  
  object UclidSymbolicSimulator {
    var asserts : List[smt.Expr] = List.empty
    
    type SymbolTable = Map[Identifier, smt.Expr];
    
    def newHavocSymbol(name: String, t: smt.Type) = 
      new smt.Symbol("_ucl_" + UniqueIdGenerator.unique() + "_" + name, t)
    def newInputSymbol(name: String, step: Int, t: smt.Type) = 
      new smt.Symbol("_ucl_" + step +"_" + name, t)
    def newConstantSymbol(name: String, t: smt.Type) = 
      new smt.Symbol(name,t)
    
    def initialize(m: UclModule) : SymbolTable = {
      var c : Context = new Context();
      c.extractContext(m);
      
      var st : SymbolTable = Map.empty;
      st = c.constants.foldLeft(st)((acc,i) => acc + (i._1 -> newConstantSymbol(i._1.value, toSMT(c.constants(i._1),c))));
      st = simulate(c.init, st, c);
      (c.variables ++ c.outputs).foreach { i => 
        Utils.assert(st contains i._1, "Init Block does not assign to " + i)  
      }
      return st
    }
    
    def simulate_steps(m: UclModule, number_of_steps: Int) : (SymbolTable,List[smt.Expr]) = 
    {
      var c : Context = new Context();
      c.extractContext(m);
      
      var st : SymbolTable = initialize(m);
      //st = c.variables.foldLeft(st)((acc,i) => acc + (i._1 -> newHavocSymbol(i._1.value, toSMT(c.variables(i._1)))));
      for (step <- 1 to number_of_steps) {
        st = c.inputs.foldLeft(st)((acc,i) => acc + (i._1 -> newInputSymbol(i._1.value, step, toSMT(c.inputs(i._1),c))));
        st = simulate(m, st, c);
        println("****** After step# " + step + " ******");
        println(st)
      }
      
      return (st,asserts)
    }
    
    def toSMT(t: UclType, c: Context) : smt.Type = {
      def dealWithFunc(inTypes: List[UclType], outType: UclType) : Unit = {
        if (inTypes.filter { x => !(x.isInstanceOf[UclBoolType] || x.isInstanceOf[UclIntType]) }.size > 0 ||
            !(outType.isInstanceOf[UclBoolType] || outType.isInstanceOf[UclIntType])
        ) {
          throw new Utils.UnimplementedException("Primitive map types implemented thus far")
        }
      }
      t match {
        case UclIntType() => return smt.IntType()
        case UclBoolType() => return smt.BoolType()
        case UclMapType(inTypes,outType) => 
          //dealWithFunc(inTypes, outType);
          return smt.MapType(inTypes.map(t => 
            toSMT(UclidSemanticAnalyzer.transitiveType(t,c),c)), 
            toSMT(UclidSemanticAnalyzer.transitiveType(outType,c),c))
        case UclArrayType(inTypes,outType) => 
          //dealWithFunc(inTypes, outType);
          return smt.ArrayType(inTypes.map(t => 
            toSMT(UclidSemanticAnalyzer.transitiveType(t,c),c)), 
            toSMT(UclidSemanticAnalyzer.transitiveType(outType,c),c))
      }
    }
    
    def toSMT(op: Operator, c: Context) : smt.Operator = {
      op match {
        case LTOp() => return smt.IntLTOp
        case LEOp() => return smt.IntLEOp
        case GTOp() => return smt.IntGTOp
        case GEOp() => return smt.IntGEOp
        case AddOp() => return smt.IntAddOp
        case SubOp() => return smt.IntSubOp
        case MulOp() => return smt.IntMulOp
      }
    }
    
    def simulate(stmts: List[UclStatement], symbolTable: SymbolTable, c: Context) : SymbolTable = {
      return stmts.foldLeft(symbolTable)((acc,i) => simulate(i, acc, c));
    }
    
    def simulate(m: UclModule, symbolTable: SymbolTable, c: Context) : SymbolTable = {
      return simulate(c.next, symbolTable, c)
    }
    
    def simulate(s: UclStatement, symbolTable: SymbolTable, c: Context) : SymbolTable = {
      def simulateAssign(lhss: List[UclLhs], args: List[smt.Expr], input: SymbolTable) : SymbolTable = {
        //println("Invoking simulateAssign with " + lhss + " := " + args + " and symboltable " + symbolTable)
        var st : SymbolTable = input;
        def lhs(i: (UclLhs,smt.Expr)) = { i._1 }
        def rhs(i: (UclLhs,smt.Expr)) = { i._2 }
        (lhss zip args).foreach { x =>
          var arraySelectOp = x._1.arraySelect match { case Some(as) => as; case None => null};
          var recordSelectOp = x._1.recordSelect match { case Some(rs) => rs; case None => null};
          //st = st.updated(lhs(x).id, rhs(x))
          if (arraySelectOp == null && recordSelectOp == null) {
            st = st + (lhs(x).id -> rhs(x))
          } else if (arraySelectOp != null && recordSelectOp == null) {
            st = st + (lhs(x).id -> smt.ArrayStoreOperation(st(lhs(x).id), 
                arraySelectOp.map(i => evaluate(i, st, c)), rhs(x)))
          } else if (arraySelectOp == null && recordSelectOp != null) {
            throw new Utils.UnimplementedException("No support for records")
          } else if (arraySelectOp != null && recordSelectOp != null) {
            throw new Utils.UnimplementedException("No support for records")
          }
        }
        return st
      }
      s match {
        case UclSkipStmt() => return symbolTable
        case UclAssertStmt(e) => 
          this.asserts = this.asserts ++ List(evaluate(e,symbolTable,c))
          return symbolTable
        case UclAssumeStmt(e) => return symbolTable
        case UclHavocStmt(id) => 
          return symbolTable.updated(id, newHavocSymbol(id.value, toSMT(c.variables(id),c)))
        case UclAssignStmt(lhss,rhss) =>
          val es = rhss.map(i => evaluate(i, symbolTable, c));
          return simulateAssign(lhss, es, symbolTable)
        case UclIfElseStmt(e,then_branch,else_branch) =>
          var then_modifies : Set[Identifier] = writeSet(then_branch,c)
          var else_modifies : Set[Identifier] = writeSet(else_branch,c)
          //compute in parallel
          var then_st : SymbolTable = simulate(then_branch, symbolTable, c)
          var else_st : SymbolTable = simulate(else_branch, symbolTable, c)
          return symbolTable.keys.filter { id => then_modifies.contains(id) || else_modifies.contains(id) }.
            foldLeft(symbolTable){ (acc,id) => 
              acc.updated(id, smt.ITE(evaluate(e, symbolTable,c), then_st(id), else_st(id)))
            }
        case UclForStmt(id, range, body) => throw new Utils.UnimplementedException("Cannot symbolically execute For loop")
        case UclCaseStmt(body) => throw new Utils.UnimplementedException("Cannot symbolically execute Case stmt")
        case UclProcedureCallStmt(id,lhss,args) =>
          var st : SymbolTable = (c.procedures(id).sig.inParams zip args).
            foldLeft(symbolTable){(acc,x) => acc.updated(x._1._1, evaluate(x._2, symbolTable, c) )}
          var c2: Context = c.copyContext()
          val proc: UclProcedureDecl = c.procedures(id)
          c2.inputs = c.inputs ++ (proc.sig.inParams.map(i => i._1 -> i._2).toMap)
          c2.variables = c.variables ++ (proc.sig.outParams.map(i => i._1 -> i._2).toMap)
          c2.variables = c2.variables ++ (proc.decls.map(i => i.id -> i.typ).toMap)
          st = proc.decls.foldLeft(st)((acc,i) => acc + (i.id -> newHavocSymbol(i.id.value, toSMT(i.typ,c))));
          st = simulate(proc.body, st, c2)
          st = simulateAssign(lhss, proc.sig.outParams.map(i => st(i._1)), st)
          //remove procedure arguments
          st = proc.sig.inParams.foldLeft(st)((acc,i) => acc - i._1)
          return st 
        case _ => return symbolTable
      }
    }
    
    def writeSet(stmts: List[UclStatement], c: Context) : Set[Identifier] = {
      def stmtWriteSet(stmt: UclStatement, c: Context) : Set[Identifier] = stmt match {
        case UclSkipStmt() => Set.empty
        case UclAssertStmt(e) => Set.empty
        case UclAssumeStmt(e) => Set.empty
        case UclHavocStmt(id) => Set(id)
        case UclAssignStmt(lhss,rhss) => 
          return lhss.map { lhs => 
            var lhs_id : String = lhs.id.value;
            lhs.recordSelect match {
              case Some(rs) => throw new Utils.UnimplementedException("Unimplemented records in LHS")
              case None => Identifier(lhs_id)
            }
          }.toSet
        case UclIfElseStmt(e,then_branch,else_branch) => 
          return writeSet(then_branch,c) ++ writeSet(else_branch,c)
        case UclForStmt(id, range, body) => return writeSet(body,c)
        case UclCaseStmt(body) => 
          return body.foldLeft(Set.empty[Identifier]) { (acc,i) => acc ++ writeSet(i._2,c) }
        case UclProcedureCallStmt(id,lhss,args) => return writeSet(c.procedures(id).body,c)
      }
      return stmts.foldLeft(Set.empty[Identifier]){(acc,s) => acc ++ stmtWriteSet(s,c)}
    }
  
    //TODO: get rid of this and use subtituteSMT instead
    def substitute(e: Expr, id: Identifier, arg: Expr) : Expr = {
       e match {
         case UclBiImplication(l,r) => 
           return UclBiImplication(substitute(l,id,arg), substitute(r,id,arg))
         case UclImplication(l,r) =>
           return UclImplication(substitute(l,id,arg), substitute(r,id,arg))
         case UclConjunction(l,r) => 
           return UclConjunction(substitute(l,id,arg), substitute(r,id,arg))
         case UclDisjunction(l,r) => 
           return UclDisjunction(substitute(l,id,arg), substitute(r,id,arg))
         case UclNegation(l) => return UclNegation(substitute(l,id,arg))
         case UclEquality(l,r) => 
           return UclEquality(substitute(l,id,arg), substitute(r,id,arg))
         case UclOperatorApplication(op,args) =>
           return UclOperatorApplication(op, args.map(x => substitute(x, id, arg)))
         case UclArraySelectOperation(a,index) => 
           return UclArraySelectOperation(a, index.map(x => substitute(x, id, arg)))
         case UclArrayStoreOperation(a,index,value) => 
           return UclArrayStoreOperation(a, index.map(x => substitute(x, id, arg)), substitute(value, id, arg))
         case UclFuncApplication(f,args) => 
           return UclFuncApplication(substitute(f,id,arg), args.map(x => substitute(x,id,arg)))
         case UclITE(cond,t,f) =>
           return UclITE(substitute(cond,id,arg), substitute(t,id,arg), substitute(f,id,arg))
         case UclLambda(idtypes, le) =>
           Utils.assert(idtypes.exists(x => x._1.value == id.value), "Lambda arguments of the same name")
           return UclLambda(idtypes, substitute(le, id, arg))
         case IntLit(n) => return e
         case BoolLit(b) => return e
         case Identifier(i) => return (if (id.value == i) arg else e)
         case _ => throw new Utils.UnimplementedException("Should not get here")
       }
    }
    
    def substituteSMT(e: smt.Expr, s: smt.Symbol, arg: smt.Expr) : smt.Expr = {
       e match {
         case smt.OperatorApplication(op,args) =>
           return smt.OperatorApplication(op, args.map(x => substituteSMT(x, s, arg)))
         case smt.ArraySelectOperation(a,index) => 
           return smt.ArraySelectOperation(a, index.map(x => substituteSMT(x, s, arg)))
         case smt.ArrayStoreOperation(a,index,value) => 
           return smt.ArrayStoreOperation(a, index.map(x => substituteSMT(x, s, arg)), substituteSMT(value, s, arg))
         case smt.FunctionApplication(f,args) => 
           return smt.FunctionApplication(substituteSMT(f,s,arg), args.map(x => substituteSMT(x,s,arg)))
         case smt.ITE(cond,t,f) =>
           return smt.ITE(substituteSMT(cond,s,arg), substituteSMT(t,s,arg), substituteSMT(f,s,arg))
         case smt.Lambda(idtypes, le) =>
           Utils.assert(idtypes.exists(x => x.id == s.id), "Lambda arguments of the same name")
           return smt.Lambda(idtypes, substituteSMT(le, s, arg))
         case smt.IntLit(n) => return e
         case smt.BooleanLit(b) => return e
         case smt.Symbol(id,typ) => return (if (id == s.id) arg else e)
         case _ => throw new Utils.UnimplementedException("Should not get here")
       }
    }
  
    def evaluate(e: Expr, symbolTable: SymbolTable, c: Context) : smt.Expr = {
       e match { //check that all identifiers in e have been declared
         case UclBiImplication(l,r) => 
           return smt.OperatorApplication(smt.IffOp, List(evaluate(l,symbolTable,c), evaluate(r,symbolTable,c)))
         case UclImplication(l,r) =>
           return smt.OperatorApplication(smt.ImplicationOp, List(evaluate(l,symbolTable,c), evaluate(r,symbolTable,c)))
         case UclConjunction(l,r) => 
           return smt.OperatorApplication(smt.ConjunctionOp, List(evaluate(l,symbolTable,c), evaluate(r,symbolTable,c)))
         case UclDisjunction(l,r) => 
           return smt.OperatorApplication(smt.DisjunctionOp, List(evaluate(l,symbolTable,c), evaluate(r,symbolTable,c)))
         case UclNegation(l) => 
           return smt.OperatorApplication(smt.NegationOp, List(evaluate(l,symbolTable,c)))
         case UclEquality(l,r) => 
           return smt.OperatorApplication(smt.EqualityOp, List(evaluate(l,symbolTable,c), evaluate(r,symbolTable,c)))
         case UclOperatorApplication(op,args) =>
           return smt.OperatorApplication(toSMT(op,c), args.map(i => evaluate(i, symbolTable, c)))
         case UclArraySelectOperation(a,index) => 
           return smt.ArraySelectOperation(evaluate(a, symbolTable, c), 
               index.map { x => evaluate(x,symbolTable,c) })
         case UclArrayStoreOperation(a,index,value) => 
           return smt.ArrayStoreOperation(evaluate(a, symbolTable, c), 
               index.map { x => evaluate(x,symbolTable,c) }, 
               evaluate(value, symbolTable,c))
         case UclFuncApplication(f,args) => f match {
           case Identifier(id) => 
             if (c.constants.contains(Identifier(id))) {
               return smt.FunctionApplication(evaluate(f, symbolTable,c), args.map(i => evaluate(i,symbolTable,c))) 
             } else if (c.variables.contains(Identifier(id))) {
               symbolTable(Identifier(id)) match {
                 case smt.Lambda(ids,e) => return (ids zip args.map(x => evaluate(x,symbolTable,c))).
                 foldLeft(e){(acc,x) => substituteSMT(acc, x._1, x._2)}
               }
             } else {
               throw new Exception("How did i get here?") //should either be a lambda or an identifier
             }
           case UclLambda(idtypes,le) => //do beta sub
             var le_sub = (idtypes.map(x => x._1) zip args).foldLeft(le){(acc,x) => substitute(acc, x._1, x._2)}
             return evaluate(le_sub, symbolTable, c)
           case _ => throw new Exception("How did i get here?")
         }
         case UclITE(cond,t,f) =>
           return smt.ITE(evaluate(cond,symbolTable,c), evaluate(t,symbolTable,c), evaluate(f,symbolTable,c))
         case UclLambda(ids,le) => 
           return smt.Lambda(ids.map(i => smt.Symbol(i._1.value, toSMT(i._2,c))), evaluate(le,symbolTable,c))
         case IntLit(n) => smt.IntLit(n)
         case BoolLit(b) => smt.BooleanLit(b)
         case BitVectorLit(bv, w) => smt.BitVectorLit(bv, w)
         case Identifier(id) => symbolTable(Identifier(id))
         case _ => throw new Utils.UnimplementedException("Should not get here")
      }
    }
  }
}