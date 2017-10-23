
/**
 * @author rohitsinha
 * 
 * with (loads of) modifications by pramod
 */
package uclid

import lang._

import scala.collection.mutable.ArrayBuffer
import uclid.smt.EnumLit

object UniqueIdGenerator {
  var i : Int = 0;
  def unique() : Int = {i = i + 1; return i}
}

case class AssertInfo(name : String, iter : Int, expr : smt.Expr, pos : ASTPosition) {
  override def toString = {
    "[Step #" + iter.toString + "] " + name + " @ " + pos.toString
  }
}
case class CheckResult(assert : AssertInfo, result : smt.SolverResult)

class UclidSymbolicSimulator (module : Module) {
  var asserts : List[AssertInfo] = List.empty
  var assumes : List[smt.Expr] = List.empty
  var results : List[CheckResult] = List.empty
  var context : Context = new Context()
  val scope = ScopeMap.empty + module
  
  type SymbolTable = Map[IdentifierBase, smt.Expr];
  var symbolTable : SymbolTable = Map.empty
  type FrameTable = ArrayBuffer[SymbolTable]
  var frameTable : FrameTable = ArrayBuffer.empty
  
  def newHavocSymbol(name: String, t: smt.Type) = 
    new smt.Symbol("$undef_" + UniqueIdGenerator.unique() + "_" + name, t)
  def newInputSymbol(name: String, step: Int, t: smt.Type) = {
    new smt.Symbol("$input_" + step +"_" + name, t)
  }
  def newConstantSymbol(name: String, t: smt.Type) = 
    new smt.Symbol("$const_"+name,t)
  
  def execute(solver : smt.SolverInterface) : List[CheckResult] = {
    module.cmds.foreach {
      (cmd) => {
        cmd.name.toString match {
          case "clear_context" =>
            asserts = List.empty
            assumes = List.empty
            results = List.empty
            symbolTable = Map.empty
            frameTable.clear()
          case "initialize" => 
            initialize(false, true, false)
            results = List.empty
          case "simulate" => 
            simulate(cmd.args(0).asInstanceOf[IntLit].value.toInt, true, false)
          case "k_induction_base" =>
            val k = cmd.args(0).asInstanceOf[IntLit].value.toInt
            initialize(false, true, false)
            simulate(k, true, false)
          case "k_induction_step" =>
            val k = cmd.args(0).asInstanceOf[IntLit].value.toInt
            initialize(true, false, true)
            simulate(k-1, false, true)
            simulate(1, true, false)
          case "decide" =>
            // assumes.foreach((e) => println("assumption : " + e.toString))
            // asserts.foreach((e) => println("assertion  : " + e.toString + "; " + e.expr.toString))
            solver.addAssumptions(assumes)
            results = asserts.foldLeft(results){ 
              case (acc, e) =>
                val sat = solver.check(smt.OperatorApplication(smt.NegationOp, List(e.expr)))
                val result = sat.result match {
                  case Some(true)  => smt.SolverResult(Some(false), sat.model)
                  case Some(false) => smt.SolverResult(Some(true), sat.model)
                  case None        => smt.SolverResult(None, None)
                }
                CheckResult(e, result) :: acc
            }
            solver.popAssumptions();
          case "print_results" =>
            printResults(results)
          case "print_cex" =>
            printCEX(results, cmd.args)
          case "print_module" =>
            println(module.toString)
          case _ => 
            throw new Utils.UnimplementedException("Command not supported: " + cmd.toString)
        }
      }
    }
    return results
  }

  def initialize(havocInit : Boolean, addAssertions : Boolean, addAssumptions : Boolean) {
    val initSymbolTable = scope.map.foldLeft(Map.empty[IdentifierBase, smt.Expr]){
      (mapAcc, decl) => {
        decl._2 match {
          case Scope.ConstantVar(id, typ) => mapAcc + (id -> newConstantSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.Function(id, typ) => mapAcc + (id -> newConstantSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> newHavocSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> newHavocSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.StateVar(id, typ) => mapAcc + (id -> newHavocSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case _ => mapAcc
        }
      }
    }
    context.extractContext(module)
    symbolTable = if (!havocInit) { 
      simulate(0, context.init, initSymbolTable, context)
    } else {
      initSymbolTable
    }

    if (addAssertions) {
      addAsserts(0, symbolTable)
    }
    if (addAssumptions) {
      assumeAssertions(symbolTable)
    }
    frameTable.clear()
    frameTable += symbolTable
    // println("*** INITIAL ****")
    // printSymbolTable(symbolTable)
  }

  def simulate(number_of_steps: Int, addAssertions : Boolean, addAssertionsAsAssumes : Boolean) : SymbolTable = 
  {
    def newInputSymbols(st : SymbolTable, step : Int) : SymbolTable = {
      scope.map.foldLeft(st)((acc, decl) => {
        decl._2 match {
          case Scope.InputVar(id, typ) => acc + (id -> newInputSymbol(id.name, step, smt.Converter.typeToSMT(typ)))
          case _ => acc
        }
      })
    }
    var currentState = symbolTable
    var states = new ArrayBuffer[SymbolTable]()
    
    for (step <- 1 to number_of_steps) {
      // println("*** BEFORE STEP " + step.toString + "****")
      // printSymbolTable(currentState)
      val stWInputs = newInputSymbols(currentState, step)
      states += stWInputs
      currentState = simulate(step, stWInputs);
      if (addAssertions) { addAsserts(step, currentState)  }
      if (addAssertionsAsAssumes) { assumeAssertions(symbolTable) }
      frameTable += currentState
      // println("*** AFTER STEP " + step.toString + "****")
      // printSymbolTable(currentState)
    }

    return currentState
  }

  def printResults(assertionResults : List[CheckResult]) {
    val passCount = assertionResults.count((p) => p.result.isTrue)
    val failCount = assertionResults.count((p) => p.result.isFalse)
    val undetCount = assertionResults.count((p) => p.result.isUndefined)
    
    Utils.assert(passCount + failCount + undetCount == assertionResults.size, "Unexpected assertion count.")
    println("%d assertions passed.".format(passCount))
    println("%d assertions failed.".format(failCount))
    println("%d assertions indeterminate.".format(undetCount))
    
    if (failCount > 0) {
      assertionResults.foreach{ (p) => 
        if (p.result.isFalse) {
          println("  FAILED -> " + p.assert.toString)
        }
      }
    }
    if (undetCount > 0) {
      assertionResults.foreach{ (p) => 
        if (p.result.isUndefined) {
          println("  UNDEF -> " + p.assert.toString)
        }
      }
    }
  }

  def printCEX(results : List[CheckResult], exprs : List[Expr]) {
    results.foreach((res) => {
      if (res.result.isModelDefined) {
        printCEX(res, exprs)
      }
    })
  }

  def printCEX(res : CheckResult, exprs : List[Expr]) {
    println("CEX for assertion @ " + res.assert.pos.toString)
    val exprsToPrint = if (exprs.size == 0) { 
      val vars = (context.inputs.keys ++ context.variables.keys ++ context.outputs.keys)
      vars.toList.sortWith((l, r) => l.name < r.name)
    } else {
      exprs
    }
    
    val model = res.result.model.get
    val indices = 0 to (frameTable.size - 1)
    (indices zip frameTable).foreach{ case (i, frame) => {
      println("=================================")
      println("Step #" + i.toString)
      printFrame(frame, model, exprsToPrint)
      println("=================================")
    }}
  }

  def printFrame(f : SymbolTable, m : smt.Model, exprs : List[Expr]) {
    def expr(id : lang.Identifier) : Option[smt.Expr] = {
      if (f.contains(id)) { Some(evaluate(id, f, context)) } 
      else { None }
    }
    
    exprs.foreach { (e) => {
      try {
        val result = m.evalAsString(evaluate(e, f , context))
        println("  " + e.toString + " : " + result)
      } catch {
        case excp : java.util.NoSuchElementException =>
          println("  " + e.toString + " : <UNDEF> ")
      }
    }}
  }

  def printSymbolTable(symbolTable : SymbolTable) {
    val keys = symbolTable.keys.toList.sortWith((l, r) => l.name < r.name)
    keys.foreach {
      (k) => {
        println (k.toString + " : " + symbolTable.get(k).get.toString)
      }
    }
  }

  /** Add module specifications (properties) to the list of proof obligations */
  def addAsserts(iter : Int, symbolTable : SymbolTable) {
    this.asserts = context.specifications.foldLeft(this.asserts){(asserts, prop) => {
      val property = AssertInfo("property " + prop._1.toString, iter, evaluate(prop._2, symbolTable, context), prop._2.position)
      // println ("addAsserts: " + property.toString + "; " + property.expr.toString)
      property :: asserts
    }}
  }
  
  /** Assume assertions (for inductive proofs). */
  def assumeAssertions(symbolTable : SymbolTable) {
    this.assumes = context.specifications.foldLeft(this.assumes){
      (acc, prop) => (evaluate(prop._2, symbolTable, context)) :: acc
    }
  }
  

  def simulate(iter : Int, stmts: List[Statement], symbolTable: SymbolTable, c : Context) : SymbolTable = {
    return stmts.foldLeft(symbolTable)((acc,i) => simulate(iter, i, acc, c));
  }

  def simulate(iter : Int, symbolTable: SymbolTable) : SymbolTable = {
    val state = simulate(iter, context.next, symbolTable, context)
    return state
  }
  
  def simulate(iter : Int, s: Statement, symbolTable: SymbolTable, c : Context) : SymbolTable = {
    def recordSelect(field : String, rec : smt.Expr) = {
      smt.OperatorApplication(smt.RecordSelectOp(field), List(rec))
    }
    def recordUpdate(field : String, rec : smt.Expr, newVal : smt.Expr) = {
      smt.OperatorApplication(smt.RecordUpdateOp(field), List(rec, newVal))
    }
    def simulateRecordUpdateExpr(st : smt.Expr, fields : List[String], newVal : smt.Expr) : smt.Expr = {
      fields match {
        case hd :: tl =>
          recordUpdate(hd, st, simulateRecordUpdateExpr(recordSelect(hd, st), tl, newVal))
        case Nil =>
          newVal
      }
    }

    def simulateAssign(lhss: List[Lhs], args: List[smt.Expr], input: SymbolTable) : SymbolTable = {
      //println("Invoking simulateAssign with " + lhss + " := " + args + " and symboltable " + symbolTable)
      var st : SymbolTable = input;
      def lhs(i: (Lhs,smt.Expr)) = { i._1 }
      def rhs(i: (Lhs,smt.Expr)) = { i._2 }
      (lhss zip args).foreach { x =>
        lhs(x) match {
          case LhsId(id) => 
            st = st + (id -> rhs(x))
          case LhsArraySelect(id, indices) => 
            st = st + (id -> smt.ArrayStoreOperation(st(id), indices.map(i => evaluate(i, st, c)), rhs(x)))
          case LhsRecordSelect(id, fields) =>
            st = st + (id -> simulateRecordUpdateExpr(st(id), fields.map(_.toString), rhs(x)))
          case LhsSliceSelect(id, slice) =>
            val resType = st(id).typ.asInstanceOf[smt.BitVectorType]
            val op = smt.BVReplaceOp(resType.width, slice.hi, slice.lo)
            val args = List(st(id), rhs(x))
            st = st + (id-> smt.OperatorApplication(op, args))
        }
      }
      return st
    }
    s match {
      case SkipStmt() => return symbolTable
      case AssertStmt(e, id) => 
        this.asserts = AssertInfo("assertion", iter, evaluate(e,symbolTable,c), s.position) :: this.asserts 
        return symbolTable
      case AssumeStmt(e, id) => 
        this.assumes = this.assumes ++ List(evaluate(e,symbolTable,c))
        return symbolTable
      case HavocStmt(id) => 
        return symbolTable.updated(id, newHavocSymbol(id.name, smt.Converter.typeToSMT(c.variables(id))))
      case AssignStmt(lhss,rhss) =>
        val es = rhss.map(i => evaluate(i, symbolTable, c));
        return simulateAssign(lhss, es, symbolTable)
      case IfElseStmt(e,then_branch,else_branch) =>
        var then_modifies : Set[IdentifierBase] = writeSet(then_branch,c)
        var else_modifies : Set[IdentifierBase] = writeSet(else_branch,c)
        //compute in parallel
        var then_st : SymbolTable = simulate(iter, then_branch, symbolTable, c)
        var else_st : SymbolTable = simulate(iter, else_branch, symbolTable, c)
        return symbolTable.keys.filter { id => then_modifies.contains(id) || else_modifies.contains(id) }.
          foldLeft(symbolTable){ (acc,id) => 
            acc.updated(id, smt.ITE(evaluate(e, symbolTable,c), then_st(id), else_st(id)))
          }
      case ForStmt(id, range, body) => throw new Utils.UnimplementedException("Cannot symbolically execute For loop")
      case CaseStmt(body) => throw new Utils.UnimplementedException("Cannot symbolically execute Case stmt")
      case ProcedureCallStmt(id,lhss,args) =>
        var st : SymbolTable = (c.procedures(id).sig.inParams zip args).
          foldLeft(symbolTable){(acc,x) => acc.updated(x._1._1, evaluate(x._2, symbolTable, c) )}
        var c2: Context = c.copyContext()
        val proc: ProcedureDecl = c.procedures(id)
        c2.inputs = c.inputs ++ (proc.sig.inParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c.variables ++ (proc.sig.outParams.map(i => i._1 -> i._2).toMap)
        c2.variables = c2.variables ++ (proc.decls.map(i => i.id -> i.typ).toMap)
        st = proc.decls.foldLeft(st)((acc,i) => acc + (i.id -> newHavocSymbol(i.id.name, smt.Converter.typeToSMT(i.typ))));
        st = proc.sig.outParams.foldLeft(st)((acc, i) => acc + (i._1 -> newHavocSymbol(i._1.name, smt.Converter.typeToSMT(i._2))))
        st = simulate(iter, proc.body, st, c2)
        st = simulateAssign(lhss, proc.sig.outParams.map(i => st(i._1)), st)
        //remove procedure arguments
        st = proc.sig.inParams.foldLeft(st)((acc,i) => acc - i._1)
        return st 
      case _ => return symbolTable
    }
  }

  def writeSet(stmts: List[Statement], c: Context) : Set[IdentifierBase] = {
    def stmtWriteSet(stmt: Statement, c: Context) : Set[IdentifierBase] = stmt match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, id) => Set.empty
      case AssumeStmt(e, id) => Set.empty
      case HavocStmt(id) => Set(id)
      case AssignStmt(lhss,rhss) => 
        return lhss.map(lhs => lhs.ident).toSet
      case IfElseStmt(e,then_branch,else_branch) => 
        return writeSet(then_branch,c) ++ writeSet(else_branch,c)
      case ForStmt(id, range, body) => return writeSet(body,c)
      case CaseStmt(body) => 
        return body.foldLeft(Set.empty[IdentifierBase]) { (acc,i) => acc ++ writeSet(i._2,c) }
      case ProcedureCallStmt(id,lhss,args) => return writeSet(c.procedures(id).body,c)
    }
    return stmts.foldLeft(Set.empty[IdentifierBase]){(acc,s) => acc ++ stmtWriteSet(s,c)}
  }

  //TODO: get rid of this and use subtituteSMT instead
  def substitute(e: Expr, id: Identifier, arg: Expr) : Expr = {
     e match {
       case OperatorApplication(op,args) =>
         return OperatorApplication(op, args.map(x => substitute(x, id, arg)))
       case ArraySelectOperation(a,index) => 
         return ArraySelectOperation(a, index.map(x => substitute(x, id, arg)))
       case ArrayStoreOperation(a,index,value) => 
         return ArrayStoreOperation(a, index.map(x => substitute(x, id, arg)), substitute(value, id, arg))
       case FuncApplication(f,args) => 
         return FuncApplication(substitute(f,id,arg), args.map(x => substitute(x,id,arg)))
       case ITE(cond,t,f) =>
         return ITE(substitute(cond,id,arg), substitute(t,id,arg), substitute(f,id,arg))
       case Lambda(idtypes, le) =>
         Utils.assert(idtypes.exists(x => x._1.name == id.name), "Lambda arguments of the same name")
         return Lambda(idtypes, substitute(le, id, arg))
       case IntLit(n) => return e
       case BoolLit(b) => return e
       case Identifier(i) => return (if (id.name == i) arg else e)
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
    smt.Converter.exprToSMT(e, symbolTable, scope)
  }
}
