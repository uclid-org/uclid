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
  type SymbolTable = SymbolicSimulator.SymbolTable
  type FrameTable = SymbolicSimulator.FrameTable

  val context = Scope.empty + module
  val assertionTree = new AssertionTree()

  var symbolTable : SymbolTable = Map.empty
  var frameTable : FrameTable = ArrayBuffer.empty

  def newHavocSymbol(name: String, t: smt.Type) = {
    new smt.Symbol("havoc_" + UniqueIdGenerator.unique() + "_" + name, t)
  }
  def newInputSymbol(name: String, step: Int, t: smt.Type) = {
    new smt.Symbol("input_" + step + "_" + name, t)
  }
  def newStateSymbol(name: String, step: Int, t: smt.Type) = {
    new smt.Symbol("state_" + step + "_" + name, t)
  }
  def newConstantSymbol(name: String, t: smt.Type) = {
    new smt.Symbol("const_" + name, t)
  }

  def resetState() {
    assertionTree.resetToInitial()
    symbolTable = Map.empty
    frameTable.clear()
  }
  def execute(solver : smt.Context) : List[CheckResult] = {
    var proofResults : List[CheckResult] = List.empty
    def noLTLFilter(name : Identifier, decorators : List[ExprDecorator]) : Boolean = !ExprDecorator.isLTLProperty(decorators)
    // add axioms as assumptions.
    module.cmds.foreach {
      (cmd) => {
        cmd.name.toString match {
          case "clear_context" =>
            resetState()
            proofResults = List.empty
          case "unroll" =>
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString
              case None    => "unroll"
            }
            initialize(false, true, false, context, label, noLTLFilter)
            symbolicSimulate(cmd.args(0).asInstanceOf[IntLit].value.toInt, true, false, context, label, noLTLFilter)
          case "bmc" =>
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString()
              case None => "bmc"
            }
            def LTLFilter(name : Identifier, decorators: List[ExprDecorator]) : Boolean = {
              val nameStr = name.name
              val nameStrToCheck = if (nameStr.endsWith(":safety")) {
                nameStr.substring(0, nameStr.size - 7)
              } else if (nameStr.endsWith(":liveness")) {
                nameStr.substring(0, nameStr.size - 9)
              } else {
                nameStr
              }
              val nameToCheck = Identifier(nameStrToCheck)
              ExprDecorator.isLTLProperty(decorators) &&  (cmd.params.isEmpty || cmd.params.contains(nameToCheck))
            }
            initialize(false, true, false, context, label, LTLFilter)
            symbolicSimulate(cmd.args(0).asInstanceOf[IntLit].value.toInt, true, false, context, label, LTLFilter)
          case "induction" =>
            val labelBase : String = cmd.resultVar match {
              case Some(l) => l.toString
              case None    => "induction (base case)"
            }
            val labelStep : String = cmd.resultVar match {
              case Some(l) => l.toString
              case None    => "induction (step)"
            }
            val k = if (cmd.args.size > 0) { 
              cmd.args(0).asInstanceOf[IntLit].value.toInt 
            } else { 1 }

            // base case.
            resetState()
            initialize(false, true, false, context, labelBase, noLTLFilter)
            symbolicSimulate(k-1, true, false, context, labelBase, noLTLFilter)

            // inductive step
            resetState()
            initialize(true, false, true, context, labelStep, noLTLFilter)
            if (k - 1 > 0) {
              symbolicSimulate(k-1, false, true, context, labelStep, noLTLFilter)
            }
            symbolicSimulate(1, true,  false, context, labelStep, noLTLFilter)

            // go back to original state.
            resetState()
          case "verify" =>
            val procName = cmd.args(0).asInstanceOf[Identifier]
            val proc = module.procedures.find(p => p.id == procName).get
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString
              case None    => "verify(%s)".format(procName.toString)
            }
            verifyProcedure(proc, label)
          case "check" =>
            // assumes.foreach((e) => println("assumption : " + e.toString))
            // asserts.foreach((e) => println("assertion  : " + e.toString + "; " + e.expr.toString))
            proofResults = assertionTree.verify(solver)
          case "print_results" =>
            printResults(proofResults, cmd.argObj)
          case "print_cex" =>
            printCEX(proofResults, cmd.args, cmd.argObj)
          case "print_smt2" =>
            printSMT2(assertionTree, cmd.argObj, solver)
          case "print_module" =>
            println(module.toString)
          case _ =>
            throw new Utils.UnimplementedException("Command not supported: " + cmd.toString)
        }
      }
    }
    return proofResults
  }

  def getInitSymbolTable(scope : Scope) : SymbolTable = {
    scope.map.foldLeft(Map.empty[Identifier, smt.Expr]){
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
  }

  def initialize(havocInit : Boolean, addAssertions : Boolean, addAssumptions : Boolean, scope : Scope, label : String, filter : ((Identifier, List[ExprDecorator]) => Boolean)) {
    val initSymbolTable = getInitSymbolTable(scope)     
    symbolTable = if (!havocInit && module.init.isDefined) {
      simulate(0, List.empty, module.init.get.body, initSymbolTable, scope, label)
    } else {
      initSymbolTable
    }

    val pastTable = Map(1 -> initSymbolTable)
    addModuleAssumptions(symbolTable, pastTable, scope)

    frameTable.clear()
    frameTable += symbolTable

    if (addAssertions) { addAsserts(0, symbolTable, pastTable, label, scope, filter) }
    if (addAssumptions) { assumeAssertions(symbolTable, pastTable, scope) }
    // println("*** INITIAL ****")
    // printSymbolTable(symbolTable)
  }

  def newInputSymbols(st : SymbolTable, step : Int, scope : Scope) : SymbolTable = {
    scope.map.foldLeft(st)((acc, decl) => {
      decl._2 match {
        case Scope.InputVar(id, typ) => acc + (id -> newInputSymbol(id.name, step, smt.Converter.typeToSMT(typ)))
        case _ => acc
      }
    })
  }

  /* This can be used as a post-processing step which might make unrolling complex expressions faster. */
  def renameStates(st : SymbolTable, step : Int, scope : Scope) : SymbolTable = {
    val renamedExprs = scope.map.map(_._2).filter(!_.typ.isArray)collect {
      case Scope.StateVar(id, typ) =>
        val newVariable = newStateSymbol(id.name, step, smt.Converter.typeToSMT(typ))
        val stateExpr = st.get(id).get
        val smtExpr = smt.OperatorApplication(smt.EqualityOp, List(newVariable, stateExpr))
        (id, newVariable, smtExpr)
    }
    renamedExprs.foreach(p => addAssumption(p._3))
    renamedExprs.foldLeft(st)((acc, p) => st + (p._1 -> p._2))
  }

  def symbolicSimulate(number_of_steps: Int, addAssertions : Boolean, addAssertionsAsAssumes : Boolean, scope : Scope, label : String, filter : ((Identifier, List[ExprDecorator]) => Boolean)) : SymbolTable =
  {
    var currentState = symbolTable
    var states = new ArrayBuffer[SymbolTable]()
    // add initial state.
    for (step <- 1 to number_of_steps) {
      // println("*** BEFORE STEP " + step.toString + "****")
      // printSymbolTable(currentState)
      val stWInputs = newInputSymbols(currentState, step, scope)
      states += stWInputs
      currentState = renameStates(simulate(step, stWInputs, scope, label), step, scope)
      val numPastFrames = frameTable.size
      val pastTables = ((0 to (numPastFrames - 1)) zip frameTable).map(p => ((numPastFrames - p._1) -> p._2)).toMap 
      frameTable += currentState
      addModuleAssumptions(currentState, pastTables, scope)
      if (addAssertions) { addAsserts(step, currentState, pastTables, label, scope, filter)  }
      if (addAssertionsAsAssumes) { assumeAssertions(symbolTable, pastTables, scope) }
      // println("*** AFTER STEP " + step.toString + "****")
      // printSymbolTable(currentState)
    }
    return currentState
  }

  def printResults(assertionResults : List[CheckResult], arg : Option[Identifier]) {
    def labelMatches(p : AssertInfo) : Boolean = {
      arg match {
        case Some(id) => id.toString == p.label
        case None => true
      }
    }
    val passCount = assertionResults.count((p) => labelMatches(p.assert) && p.result.isTrue)
    val failCount = assertionResults.count((p) => labelMatches(p.assert) && p.result.isFalse)
    val undetCount = assertionResults.count((p) => labelMatches(p.assert) && p.result.isUndefined)

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

  def printCEX(results : List[CheckResult], exprs : List[Expr], arg : Option[Identifier]) {
    def labelMatches(p : AssertInfo) : Boolean = {
      arg match {
        case Some(id) => id.toString == p.label
        case None => true
      }
    }
    results.foreach((res) => {
      if (labelMatches(res.assert) && res.result.isModelDefined) {
        printCEX(res, exprs)
      }
    })
  }

  def printCEX(res : CheckResult, exprs : List[Expr]) {
    println("CEX for %s".format(res.assert.toString, res.assert.pos.toString))
    val scope = res.assert.context
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
      val pastFrames = (0 to (i-1)).map(j => (j + 1) -> ft(i - 1 - j)).toMap
      printFrame(frame, pastFrames, model, exprsToPrint, scope)
      println("=================================")
    }}
  }

  def printSMT2(aTree : AssertionTree, label : Option[Identifier], solver : smt.Context) {
    throw new Utils.UnimplementedException("Implement print_smt2.")
  }

  def printFrame(f : SymbolTable, pastFrames : Map[Int, SymbolTable], m : smt.Model, exprs : List[Expr], scope : Scope) {
    def expr(id : lang.Identifier) : Option[smt.Expr] = {
      if (f.contains(id)) { Some(evaluate(id, f, pastFrames, scope)) }
      else { None }
    }

    exprs.foreach { (e) => {
      try {
        val result = m.evalAsString(evaluate(e, f, pastFrames, scope))
        println("  " + e.toString + " : " + result)
      } catch {
        case excp : Utils.UnknownIdentifierException =>
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

  /** Add assertion. */
  def addAssert(property : AssertInfo) {
    assertionTree.addAssert(property)
  }
  /** Add assumption. */
  def addAssumption(e : smt.Expr) {
    assertionTree.addAssumption(e)
  }

  def verifyProcedure(proc : ProcedureDecl, label : String) = {
    val procScope = context + proc
    val initSymbolTable = simulate(0, List.empty, module.init.get.body, getInitSymbolTable(context), context, label)
    val initProcState0 = newInputSymbols(initSymbolTable, 1, context)
    val initProcState1 = proc.sig.inParams.foldLeft(initProcState0)((acc, arg) => {
      acc + (arg._1 -> newInputSymbol(arg._1.name, 1, smt.Converter.typeToSMT(arg._2)))
    })
    val initProcState = proc.sig.outParams.foldLeft(initProcState1)((acc, arg) => {
      acc + (arg._1 -> newHavocSymbol(arg._1.name, smt.Converter.typeToSMT(arg._2)))
    })
    // println("**** initProcState ****")
    // printSymbolTable(initProcState)

    // add assumption.
    proc.requires.foreach(r => assertionTree.addAssumption(evaluate(r, initProcState, Map.empty, procScope)))
    // simulate procedure execution.
    val finalState = simulate(1, List.empty, proc.body, initProcState, procScope, label)
    // create frame table.
    val frameTable = new FrameTable()
    frameTable += initProcState
    frameTable += finalState 

    // println("**** finalState ****")
    // printSymbolTable(finalState)

    // add assertions.
    proc.ensures.foreach {
      e => {
        val name = "postcondition"
        val expr = evaluate(e, finalState, Map(1 -> initProcState), procScope)
        assertionTree.addAssert(AssertInfo(name, label, frameTable, procScope, 1, smt.BooleanLit(true), expr, List.empty, e.position))
      }
    }
    resetState()

  }

  /** Add module specifications (properties) to the list of proof obligations */
  def addAsserts(iter : Int, symbolTable : SymbolTable, pastTables : Map[Int, SymbolTable], 
                label : String, scope : Scope, filter : ((Identifier, List[ExprDecorator]) => Boolean)) {
    
    val table = frameTable.clone()
      
    scope.specs.foreach(specVar => {
      val prop = module.properties.find(p => p.id == specVar.varId).get
      if (filter(prop.id, prop.params)) {
        val property = AssertInfo(prop.name, label, table, scope, iter, smt.BooleanLit(true), evaluate(prop.expr, symbolTable, pastTables, scope), prop.params, prop.expr.position)
        // println ("addAsserts: " + property.toString + "; " + property.expr.toString)
        addAssert(property)
      }
    })
  }

  /** Add module-level axioms/assumptions. */
  def addModuleAssumptions(symbolTable : SymbolTable, pastTables : Map[Int, SymbolTable], scope : Scope) {
    module.axioms.foreach(ax => addAssumption(evaluate(ax.expr, symbolTable, pastTables, scope)))
  }

  /** Assume assertions (for inductive proofs). */
  def assumeAssertions(symbolTable : SymbolTable, pastTables : Map[Int, SymbolTable], scope : Scope) {
    scope.specs.foreach(sp => addAssumption(evaluate(sp.expr, symbolTable, pastTables, scope)))
  }

  def simulate(iter : Int, symbolTable: SymbolTable, scope : Scope, label : String) : SymbolTable = {
    simulate(iter, List.empty, module.next.get.body, symbolTable, scope, label)
  }

  def simulate(iter : Int, pathConditions: List[smt.Expr], stmts: List[Statement], symbolTable: SymbolTable, scope : Scope, label : String) : SymbolTable = {
    return stmts.foldLeft(symbolTable)((acc,i) => simulate(iter, pathConditions, i, acc, scope, label));
  }

  def simulate(iter : Int, pathConditions: List[smt.Expr], s: Statement, symbolTable: SymbolTable, scope : Scope, label : String) : SymbolTable = {
    val numPastFrames = frameTable.size
    lazy val pastTables = ((0 to (numPastFrames - 1)) zip frameTable).map(p => ((numPastFrames - p._1) -> p._2)).toMap

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

    def simulateAssign(lhss: List[Lhs], args: List[smt.Expr], input: SymbolTable, label : String) : SymbolTable = {
      //println("Invoking simulateAssign with " + lhss + " := " + args + " and symboltable " + symbolTable)
      var st : SymbolTable = input;
      def lhs(i: (Lhs,smt.Expr)) = { i._1 }
      def rhs(i: (Lhs,smt.Expr)) = { i._2 }
      (lhss zip args).foreach { x =>
        lhs(x) match {
          case LhsId(id) =>
            st = st + (id -> rhs(x))
          case LhsArraySelect(id, indices) =>
            st = st + (id -> smt.ArrayStoreOperation(st(id), indices.map(i => evaluate(i, st, pastTables, scope)), rhs(x)))
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

    // println("iter: " + iter.toString())
    // println(Utils.join(s.toLines, "\n"))

    s match {
      case SkipStmt() => return symbolTable
      case AssertStmt(e, id) =>
        val frameTableP = frameTable.clone()
        frameTableP += symbolTable
        val initPathCondExpr : smt.Expr = smt.BooleanLit(true)
        val pathCondExpr = pathConditions.foldLeft(initPathCondExpr) {
          (acc, pc) => {
            smt.OperatorApplication(smt.ConjunctionOp, List(acc, pc))
          }
        }
        addAssert(
            AssertInfo(
                "assertion", label, frameTableP, 
                scope, iter, pathCondExpr, 
                evaluate(e,symbolTable, pastTables, scope), 
                List.empty, s.position))
        return symbolTable
      case AssumeStmt(e, id) =>
        addAssumption(evaluate(e,symbolTable, pastTables, scope))
        return symbolTable
      case HavocStmt(id) =>
        return symbolTable.updated(id, newHavocSymbol(id.name, smt.Converter.typeToSMT(scope.typeOf(id).get)))
      case AssignStmt(lhss,rhss) =>
        val es = rhss.map(i => evaluate(i, symbolTable, pastTables, scope));
        return simulateAssign(lhss, es, symbolTable, label)
      case IfElseStmt(e,then_branch,else_branch) =>
        var then_modifies : Set[Identifier] = writeSet(then_branch)
        var else_modifies : Set[Identifier] = writeSet(else_branch)
        //compute in parallel
        val condExpr = evaluate(e, symbolTable, pastTables, scope)
        var then_st : SymbolTable = simulate(iter, condExpr :: pathConditions, then_branch, symbolTable, scope, label)
        var else_st : SymbolTable = simulate(iter, condExpr :: pathConditions, else_branch, symbolTable, scope, label)
        return symbolTable.keys.filter { id => then_modifies.contains(id) || else_modifies.contains(id) }.
          foldLeft(symbolTable){ (acc,id) =>
            acc.updated(id, smt.OperatorApplication(smt.ITEOp, List(condExpr, then_st(id), else_st(id))))
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
       case smt.Lambda(idtypes, le) =>
         Utils.assert(idtypes.exists(x => x.id == s.id), "Lambda arguments of the same name")
         return smt.Lambda(idtypes, substituteSMT(le, s, arg))
       case smt.IntLit(n) => return e
       case smt.BooleanLit(b) => return e
       case smt.Symbol(id,typ) => return (if (id == s.id) arg else e)
       case _ => throw new Utils.UnimplementedException("Should not get here")
     }
  }

  def evaluate(e: Expr, symbolTable: SymbolTable, pastTables : Map[Int, SymbolTable], scope : Scope) : smt.Expr = {
    def idToSMT(id : lang.Identifier, scope : lang.Scope, past : Int) : smt.Expr = {
      val smtType = scope.typeOf(id) match {
        case Some(typ) => smt.Converter.typeToSMT(typ)
        case None => throw new Utils.UnknownIdentifierException(id)
      }
      
      if (scope.isQuantifierVar(id)) { smt.Symbol(id.name, smtType) } 
      else {
        past match {
          case 0 => symbolTable(id)
          case _ =>
            pastTables.get(past) match {
              case Some(pFrame) => pFrame(id)
              case None => newHavocSymbol(id.name, smtType)
            }
        }
      }
    }
    smt.Converter.exprToSMT(e, idToSMT, scope)
  }
}
