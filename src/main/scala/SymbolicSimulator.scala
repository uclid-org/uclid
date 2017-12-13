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
 * Authors: Rohit Sinha, Pramod Subramanyan

 * Symbolic simulator/model checker for UCLID5.
 *
 */

package uclid

import lang._

import scala.collection.mutable.ArrayBuffer
import uclid.smt.EnumLit

object UniqueIdGenerator {
  var i : Int = 0;
  def unique() : Int = {i = i + 1; return i}
}

object SymbolicSimulator {
  type SymbolTable = Map[Identifier, smt.Expr];
  type FrameTable = ArrayBuffer[SymbolTable]
}

class SymbolicSimulator (module : Module) {
  val scope = Scope.empty + module
  val assertionTree = new AssertionTree()

  var symbolTable : SymbolicSimulator.SymbolTable = Map.empty
  var frameTable : SymbolicSimulator.FrameTable = ArrayBuffer.empty

  def newHavocSymbol(name: String, t: smt.Type) =
    new smt.Symbol("$undef_" + UniqueIdGenerator.unique() + "_" + name, t)
  def newInputSymbol(name: String, step: Int, t: smt.Type) = {
    new smt.Symbol("$input_" + step +"_" + name, t)
  }
  def newConstantSymbol(name: String, t: smt.Type) =
    new smt.Symbol("$const_"+name,t)

  def execute(solver : smt.SolverInterface) : List[CheckResult] = {
    var proofResults : List[CheckResult] = List.empty
    def resetState() {
      assertionTree.resetToInitial()
      symbolTable = Map.empty
      frameTable.clear()
    }
    // add axioms as assumptions.
    module.cmds.foreach {
      (cmd) => {
        cmd.name.toString match {
          case "clear_context" =>
            resetState()
            proofResults = List.empty
          case "initialize" =>
            initialize(false, true, false, "initialize")
          case "simulate" =>
            simulate(cmd.args(0).asInstanceOf[IntLit].value.toInt, true, false, "simulate")
          case "induction" =>
            val k = if (cmd.args.size > 0) { 
              cmd.args(0).asInstanceOf[IntLit].value.toInt 
            } else { 1 }

            // base case.
            resetState()
            initialize(false, true, false, "induction (base case)")
            simulate(k, true, false, "induction (base case)")

            // inductive step
            resetState()
            initialize(true, false, true, "induction (inductive step)")
            simulate(k-1, false, true, "induction (inductive step)")
            simulate(1, true,  false, "induction (inductive step)")

            // go back to original state.
            resetState()
          case "decide" =>
            // assumes.foreach((e) => println("assumption : " + e.toString))
            // asserts.foreach((e) => println("assertion  : " + e.toString + "; " + e.expr.toString))
            proofResults = assertionTree.verify(solver)
          case "print_results" =>
            printResults(proofResults)
          case "print_cex" =>
            printCEX(proofResults, cmd.args)
          case "print_module" =>
            println(module.toString)
          case _ =>
            throw new Utils.UnimplementedException("Command not supported: " + cmd.toString)
        }
      }
    }
    return proofResults
  }

  def initialize(havocInit : Boolean, addAssertions : Boolean, addAssumptions : Boolean, label : String) {
    val initSymbolTable = scope.map.foldLeft(Map.empty[Identifier, smt.Expr]){
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
    symbolTable = if (!havocInit && module.init.isDefined) {
      simulate(0, module.init.get.body, initSymbolTable, label)
    } else {
      initSymbolTable
    }

    addModuleAssumptions(symbolTable)

    if (addAssertions) {
      addAsserts(0, symbolTable, label)
    }
    if (addAssumptions) {
      assumeAssertions(symbolTable)
    }
    frameTable.clear()
    frameTable += symbolTable
    // println("*** INITIAL ****")
    // printSymbolTable(symbolTable)
  }

  def simulate(number_of_steps: Int, addAssertions : Boolean, addAssertionsAsAssumes : Boolean, label : String) : SymbolicSimulator.SymbolTable =
  {
    def newInputSymbols(st : SymbolicSimulator.SymbolTable, step : Int) : SymbolicSimulator.SymbolTable = {
      scope.map.foldLeft(st)((acc, decl) => {
        decl._2 match {
          case Scope.InputVar(id, typ) => acc + (id -> newInputSymbol(id.name, step, smt.Converter.typeToSMT(typ)))
          case _ => acc
        }
      })
    }
    var currentState = symbolTable
    var states = new ArrayBuffer[SymbolicSimulator.SymbolTable]()

    for (step <- 1 to number_of_steps) {
      // println("*** BEFORE STEP " + step.toString + "****")
      // printSymbolTable(currentState)
      val stWInputs = newInputSymbols(currentState, step)
      states += stWInputs
      currentState = simulate(step, stWInputs, label);
      if (addAssertions) { addAsserts(step, currentState, label)  }
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
    println("CEX for %s".format(res.assert.toString, res.assert.pos.toString))
    val exprsToPrint = if (exprs.size == 0) {
      val vars = (scope.inputs ++ scope.vars ++ scope.outputs).map(_.id)
      vars.toList.sortWith((l, r) => l.name < r.name)
    } else {
      exprs
    }

    val model = res.result.model.get
    val ft = res.assert.frameTable
    val indices = 0 to (ft.size - 1)
    (indices zip ft).foreach{ case (i, frame) => {
      println("=================================")
      println("Step #" + i.toString)
      printFrame(frame, model, exprsToPrint)
      println("=================================")
    }}
  }

  def printFrame(f : SymbolicSimulator.SymbolTable, m : smt.Model, exprs : List[Expr]) {
    def expr(id : lang.Identifier) : Option[smt.Expr] = {
      if (f.contains(id)) { Some(evaluate(id, f)) }
      else { None }
    }

    exprs.foreach { (e) => {
      try {
        val result = m.evalAsString(evaluate(e, f))
        println("  " + e.toString + " : " + result)
      } catch {
        case excp : java.util.NoSuchElementException =>
          println("  " + e.toString + " : <UNDEF> ")
      }
    }}
  }

  def printSymbolTable(symbolTable : SymbolicSimulator.SymbolTable) {
    val keys = symbolTable.keys.toList.sortWith((l, r) => l.name < r.name)
    keys.foreach {
      (k) => {
        println (k.toString + " : " + symbolTable.get(k).get.toString)
      }
    }
  }

  /** Add assertion. */
  def addAssert(property : AssertInfo) {
    assertionTree.addAssert(property)
  }
  /** Add assumption. */
  def addAssumption(e : smt.Expr) {
    assertionTree.addAssumption(e)
  }
  /** Add module specifications (properties) to the list of proof obligations */
  def addAsserts(iter : Int, symbolTable : SymbolicSimulator.SymbolTable, label : String) {
    scope.specs.foreach(specVar => {
      val prop = module.properties.find(p => p.id == specVar.varId).get
      val property = AssertInfo(prop.name, label, frameTable.clone(), iter, evaluate(prop.expr, symbolTable), prop.expr.position)
      // println ("addAsserts: " + property.toString + "; " + property.expr.toString)
      addAssert(property)
    })
  }
  /** Add module-level axioms/assumptions. */
  def addModuleAssumptions(symbolTable : SymbolicSimulator.SymbolTable) {
    module.axioms.foreach(ax => addAssumption(evaluate(ax.expr, symbolTable)))
  }
  /** Assume assertions (for inductive proofs). */
  def assumeAssertions(symbolTable : SymbolicSimulator.SymbolTable) {
    scope.specs.foreach(sp => addAssumption(evaluate(sp.expr, symbolTable)))
  }


  def simulate(iter : Int, stmts: List[Statement], symbolTable: SymbolicSimulator.SymbolTable, label : String) : SymbolicSimulator.SymbolTable = {
    return stmts.foldLeft(symbolTable)((acc,i) => simulate(iter, i, acc, label));
  }

  def simulate(iter : Int, symbolTable: SymbolicSimulator.SymbolTable, label : String) : SymbolicSimulator.SymbolTable = {
    // FIXME: Make sure module has a next declaration.
    simulate(iter, module.next.get.body, symbolTable, label)
  }

  def simulate(iter : Int, s: Statement, symbolTable: SymbolicSimulator.SymbolTable, label : String) : SymbolicSimulator.SymbolTable = {
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

    def simulateAssign(lhss: List[Lhs], args: List[smt.Expr], input: SymbolicSimulator.SymbolTable, label : String) : SymbolicSimulator.SymbolTable = {
      //println("Invoking simulateAssign with " + lhss + " := " + args + " and symboltable " + symbolTable)
      var st : SymbolicSimulator.SymbolTable = input;
      def lhs(i: (Lhs,smt.Expr)) = { i._1 }
      def rhs(i: (Lhs,smt.Expr)) = { i._2 }
      (lhss zip args).foreach { x =>
        lhs(x) match {
          case LhsId(id) =>
            st = st + (id -> rhs(x))
          case LhsArraySelect(id, indices) =>
            st = st + (id -> smt.ArrayStoreOperation(st(id), indices.map(i => evaluate(i, st)), rhs(x)))
          case LhsRecordSelect(id, fields) =>
            st = st + (id -> simulateRecordUpdateExpr(st(id), fields.map(_.toString), rhs(x)))
          case LhsSliceSelect(id, slice) =>
            val resType = st(id).typ.asInstanceOf[smt.BitVectorType]
            val op = smt.BVReplaceOp(resType.width, slice.hi, slice.lo)
            val args = List(st(id), rhs(x))
            st = st + (id-> smt.OperatorApplication(op, args))
          case LhsVarSliceSelect(id, fields) =>
            // FIXME: Implement VarSliceSelect.
            throw new Utils.UnimplementedException("FIXME: Implement simulateAssign for VarSliceSelect.")
        }
      }
      return st
    }
    s match {
      case SkipStmt() => return symbolTable
      case AssertStmt(e, id) =>
        addAssert(AssertInfo("assertion", label, frameTable.clone(), iter, evaluate(e,symbolTable), s.position))
        return symbolTable
      case AssumeStmt(e, id) =>
        addAssumption(evaluate(e,symbolTable))
        return symbolTable
      case HavocStmt(id) =>
        return symbolTable.updated(id, newHavocSymbol(id.name, smt.Converter.typeToSMT(scope.typeOf(id).get)))
      case AssignStmt(lhss,rhss) =>
        val es = rhss.map(i => evaluate(i, symbolTable));
        return simulateAssign(lhss, es, symbolTable, label)
      case IfElseStmt(e,then_branch,else_branch) =>
        var then_modifies : Set[Identifier] = writeSet(then_branch)
        var else_modifies : Set[Identifier] = writeSet(else_branch)
        //compute in parallel
        var then_st : SymbolicSimulator.SymbolTable = simulate(iter, then_branch, symbolTable, label)
        var else_st : SymbolicSimulator.SymbolTable = simulate(iter, else_branch, symbolTable, label)
        return symbolTable.keys.filter { id => then_modifies.contains(id) || else_modifies.contains(id) }.
          foldLeft(symbolTable){ (acc,id) =>
            acc.updated(id, smt.ITE(evaluate(e, symbolTable), then_st(id), else_st(id)))
          }
      case ForStmt(id, range, body) => throw new Utils.UnimplementedException("Cannot symbolically execute For loop")
      case CaseStmt(body) => throw new Utils.UnimplementedException("Cannot symbolically execute Case stmt")
      case ProcedureCallStmt(id,lhss,args) =>
        throw new Utils.RuntimeError("ProcedureCallStmt must have been inlined by now.")
      case _ => return symbolTable
    }
  }

  def writeSet(stmts: List[Statement]) : Set[Identifier] = {
    def stmtWriteSet(stmt: Statement) : Set[Identifier] = stmt match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, id) => Set.empty
      case AssumeStmt(e, id) => Set.empty
      case HavocStmt(id) => Set(id)
      case AssignStmt(lhss,rhss) =>
        return lhss.map(lhs => lhs.ident).toSet
      case IfElseStmt(e,then_branch,else_branch) =>
        return writeSet(then_branch) ++ writeSet(else_branch)
      case ForStmt(id, range, body) => return writeSet(body)
      case CaseStmt(body) =>
        return body.foldLeft(Set.empty[Identifier]) { (acc,i) => acc ++ writeSet(i._2) }
      case ProcedureCallStmt(id,lhss,args) =>
        throw new Utils.RuntimeError("ProcedureCallStmt must have been inlined by now.")
      case ModuleCallStmt(id) =>
        throw new Utils.RuntimeError("ModuleCallStmt must have been inlined by now.")
    }
    return stmts.foldLeft(Set.empty[Identifier]){(acc,s) => acc ++ stmtWriteSet(s)}
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

  def evaluate(e: Expr, symbolTable: SymbolicSimulator.SymbolTable) : smt.Expr = {
    smt.Converter.exprToSMT(e, symbolTable, scope)
  }
}
