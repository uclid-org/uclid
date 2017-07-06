
/**
 * @author rohitsinha
 */
package uclid {
  import uclid.lang._
  import scala.collection.mutable.ArrayBuffer
  
  object UniqueIdGenerator {
    var i : Int = 0;
    def unique() : Int = {i = i + 1; return i}
  }
  
  class UclidSymbolicSimulator (module : Module) {
    var asserts : List[smt.Expr] = List.empty
    var context : Context = new Context();
    
    type SymbolTable = Map[Identifier, smt.Expr];
    var symbolTable : SymbolTable = Map.empty
    
    def newHavocSymbol(name: String, t: smt.Type) = 
      new smt.Symbol("_ucl_" + UniqueIdGenerator.unique() + "_" + name, t)
    def newInputSymbol(name: String, step: Int, t: smt.Type) = 
      new smt.Symbol("_ucl_" + step +"_" + name, t)
    def newConstantSymbol(name: String, t: smt.Type) = 
      new smt.Symbol(name,t)
    
    def execute(solver : smt.SolverInterface) {
      module.cmds.foreach((cmd) => {
        cmd match {
          case UclInitializeCmd() => initialize()
          case UclSimulateCmd(steps) => simulate(steps.value.toInt)
          case UclDecideCmd() => {
            asserts.foreach{ (e) =>
              println("Assertion: " + e.toString)
              solver.check(smt.OperatorApplication(smt.NegationOp, List(e))) match {
                case Some(false) => println("Assertion HOLDS.")
                case Some(true)  => println("Assertion FAILED.")
                case None        => println("Assertion INDETERMINATE.")
              }
            }
          }
          case _ => throw new Utils.UnimplementedException("Command not supported: " + cmd.toString)
        }
      })
    }
    
    def initialize() {
      context.extractContext(module)
      val initSymbolTable = context.constants.foldLeft(Map.empty[Identifier, smt.Expr]){
        (acc,i) => acc + (i._1 -> newConstantSymbol(i._1.value, toSMT(context.constants(i._1),context)))
      };
      symbolTable = simulate(context.init, initSymbolTable, context);
      (context.variables ++ context.outputs).foreach { i => 
        Utils.assert(symbolTable.contains(i._1), "Init Block does not assign to " + i)  
      }
    }
    
    def simulate(number_of_steps: Int) : (SymbolTable,List[smt.Expr]) = 
    {
      def newInputSymbols(st : SymbolTable, step : Int) : SymbolTable = {
        context.inputs.foldLeft(st)((acc,i) => {
          acc + (i._1 -> newInputSymbol(i._1.value, step, toSMT(i._2, context))) 
        })
      }
      //st = context.variables.foldLeft(st)((acc,i) => acc + (i._1 -> newHavocSymbol(i._1.value, toSMT(context.variables(i._1)))));
      var currentState = symbolTable
      var states = new ArrayBuffer[SymbolTable]()
      
      for (step <- 1 to number_of_steps) {
        val stWInputs = newInputSymbols(currentState, step)
        states += stWInputs
        currentState = simulate(stWInputs);
        println("****** After step# " + step + " ******");
        println(currentState)
      }
      
      return (currentState,asserts)
    }
    
    def toSMT(t: Type, context: Context) : smt.Type = {
      def dealWithFunc(inTypes: List[Type], outType: Type) : Unit = {
        if (inTypes.filter { x => !(x.isInstanceOf[BoolType] || x.isInstanceOf[IntType]) }.size > 0 ||
            !(outType.isInstanceOf[BoolType] || outType.isInstanceOf[IntType])
        ) {
          throw new Utils.UnimplementedException("Primitive map types implemented thus far")
        }
      }
      t match {
        case IntType() => return smt.IntType()
        case BoolType() => return smt.BoolType()
        case BitVectorType(w) => return smt.BitVectorType(w)
        case MapType(inTypes,outType) => 
          //dealWithFunc(inTypes, outType);
          return smt.MapType(inTypes.map(t => 
            toSMT(UclidSemanticAnalyzer.transitiveType(t,context),context)), 
            toSMT(UclidSemanticAnalyzer.transitiveType(outType,context),context))
        case ArrayType(inTypes,outType) => 
          //dealWithFunc(inTypes, outType);
          return smt.ArrayType(inTypes.map(t => 
            toSMT(UclidSemanticAnalyzer.transitiveType(t,context),context)), 
            toSMT(UclidSemanticAnalyzer.transitiveType(outType,context),context))
        case _ => throw new Utils.UnimplementedException("Need to handle more types here.")
      }
    }
    
    def toSMT(op: Operator, context: Context) : smt.Operator = {
      op match {
        // Polymorphic operators are not allowed.
        case p : PolymorphicOperator => throw new Utils.RuntimeError("Polymorphic operators must have been eliminated by now.")
        // Integer operators.
        case IntLTOp() => return smt.IntLTOp
        case IntLEOp() => return smt.IntLEOp
        case IntGTOp() => return smt.IntGTOp
        case IntGEOp() => return smt.IntGEOp
        case IntAddOp() => return smt.IntAddOp
        case IntSubOp() => return smt.IntSubOp
        case IntMulOp() => return smt.IntMulOp
        // Bitvector operators.
        case BVLTOp(w) => return smt.BVLTOp(w)
        case BVLEOp(w) => return smt.BVLEOp(w)
        case BVGTOp(w) => return smt.BVGTOp(w)
        case BVGEOp(w) => return smt.BVGEOp(w)
        case BVAddOp(w) => return smt.BVAddOp(w)
        case BVSubOp(w) => return smt.BVSubOp(w)
        case BVMulOp(w) => return smt.BVMulOp(w)
        // Boolean operators.
        case ConjunctionOp() => return smt.ConjunctionOp
        case DisjunctionOp() => return smt.DisjunctionOp
        case IffOp() => return smt.IffOp
        case ImplicationOp() => return smt.ImplicationOp
        case NegationOp() => return smt.NegationOp
        // Comparison operators.
        case EqualityOp() => return smt.EqualityOp
        case InequalityOp() => return smt.InequalityOp
        // FIXME
        case _ => throw new Utils.UnimplementedException("Operator not supported yet.")
      }
    }
    
    def simulate(stmts: List[UclStatement], symbolTable: SymbolTable, c : Context) : SymbolTable = {
      return stmts.foldLeft(symbolTable)((acc,i) => simulate(i, acc, c));
    }
    
    def simulate(symbolTable: SymbolTable) : SymbolTable = {
      return simulate(context.next, symbolTable, context)
    }
    
    def simulate(s: UclStatement, symbolTable: SymbolTable, c : Context) : SymbolTable = {
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
          st = proc.decls.foldLeft(st)((acc,i) => acc + (i.id -> newHavocSymbol(i.id.value, toSMT(i.typ,c2))));
          st = proc.sig.outParams.foldLeft(st)((acc, i) => acc + (i._1 -> newHavocSymbol(i._1.value, toSMT(i._2, c2))))
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
  
    def evaluate(e: Expr, symbolTable: SymbolTable, context: Context) : smt.Expr = {
       e match { //check that all identifiers in e have been declared
         case UclOperatorApplication(op,args) =>
           return smt.OperatorApplication(toSMT(op,context), args.map(i => evaluate(i, symbolTable, context)))
         case UclArraySelectOperation(a,index) => 
           return smt.ArraySelectOperation(evaluate(a, symbolTable, context), 
               index.map { x => evaluate(x,symbolTable,context) })
         case UclArrayStoreOperation(a,index,value) => 
           return smt.ArrayStoreOperation(evaluate(a, symbolTable, context), 
               index.map { x => evaluate(x,symbolTable,context) }, 
               evaluate(value, symbolTable,context))
         case UclFuncApplication(f,args) => f match {
           case Identifier(id) => 
             if (context.constants.contains(Identifier(id))) {
               return smt.FunctionApplication(evaluate(f, symbolTable,context), args.map(i => evaluate(i,symbolTable,context))) 
             } else if (context.variables.contains(Identifier(id))) {
               symbolTable(Identifier(id)) match {
                 case smt.Lambda(ids,e) => return (ids zip args.map(x => evaluate(x,symbolTable,context))).
                 foldLeft(e){(acc,x) => substituteSMT(acc, x._1, x._2)}
               }
             } else {
               throw new Exception("How did i get here?") //should either be a lambda or an identifier
             }
           case UclLambda(idtypes,le) => //do beta sub
             var le_sub = (idtypes.map(x => x._1) zip args).foldLeft(le){(acc,x) => substitute(acc, x._1, x._2)}
             return evaluate(le_sub, symbolTable, context)
           case _ => throw new Exception("How did i get here?")
         }
         case UclITE(cond,t,f) =>
           return smt.ITE(evaluate(cond,symbolTable,context), evaluate(t,symbolTable,context), evaluate(f,symbolTable,context))
         case UclLambda(ids,le) => 
           return smt.Lambda(ids.map(i => smt.Symbol(i._1.value, toSMT(i._2,context))), evaluate(le,symbolTable,context))
         case IntLit(n) => smt.IntLit(n)
         case BoolLit(b) => smt.BooleanLit(b)
         case BitVectorLit(bv, w) => smt.BitVectorLit(bv, w)
         case Identifier(id) => symbolTable(Identifier(id))
         case _ => throw new Utils.UnimplementedException("Should not get here")
      }
    }
  }
}