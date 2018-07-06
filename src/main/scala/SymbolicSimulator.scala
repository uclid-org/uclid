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
 * Authors: Rohit Sinha, Pramod Subramanyan

 * Symbolic simulator/model checker for UCLID5.
 *
 */

package uclid

import lang._

import scala.collection.mutable.ArrayBuffer
import com.typesafe.scalalogging.Logger

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
  var assertionTree = new AssertionTree()
  val defaultLog = Logger(classOf[SymbolicSimulator])
  val frameLog = Logger("uclid.SymbolicSimulator.frame")
  val assertLog = Logger("uclid.SymbolicSimulator.assert")
  val verifyProcedureLog = Logger("uclid.SymbolicSimulator.verifyProc")

  var symbolTable : SymbolTable = Map.empty
  var frameTable : FrameTable = ArrayBuffer.empty
  
  var synthesizedInvariants : ArrayBuffer[lang.Expr] = ArrayBuffer.empty

  def newHavocSymbol(name: String, t: smt.Type) = {
    new smt.Symbol("havoc_" + UniqueIdGenerator.unique() + "_" + name, t)
  }
  def newInitSymbol(name: String, t : smt.Type) = {
    new smt.Symbol("initial_" + UniqueIdGenerator.unique() + "_" + name, t)
  }
  def newVarSymbol(name: String, t: smt.Type) = {
    new smt.Symbol("var_" + UniqueIdGenerator.unique() + "_" + name, t)
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
  var proofResults : List[CheckResult] = List.empty
  def dumpResults(label: String, log : Logger) {
    log.debug("{} --> proofResults.size = {}", label, proofResults.size.toString)
  }
  def execute(solver : smt.Context, synthesizer : Option[smt.SynthesisContext], config : UclidMain.Config) : List[CheckResult] = {
    proofResults = List.empty
    def noLTLFilter(name : Identifier, decorators : List[ExprDecorator]) : Boolean = !ExprDecorator.isLTLProperty(decorators)
    // add axioms as assumptions.
    module.cmds.foreach {
      (cmd) => {
        cmd.name.toString match {
          case "clear_context" =>
            assertionTree = new AssertionTree()
            proofResults = List.empty
            dumpResults("clear_context", defaultLog)
          case "unroll" =>
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString
              case None    => "unroll"
            }
            initialize(false, true, false, context, label, noLTLFilter)
            symbolicSimulate(0, cmd.args(0)._1.asInstanceOf[IntLit].value.toInt, true, false, context, label, noLTLFilter)
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
            symbolicSimulate(0, cmd.args(0)._1.asInstanceOf[IntLit].value.toInt, true, false, context, label, LTLFilter)
          case "induction" =>
            val labelBase : String = cmd.resultVar match {
              case Some(l) => l.toString + ": induction (base)"
              case None    => "induction (base)"
            }
            val labelStep : String = cmd.resultVar match {
              case Some(l) => l.toString + ": induction (step)"
              case None    => "induction (step)"
            }
            val k = if (cmd.args.size > 0) {
              cmd.args(0)._1.asInstanceOf[IntLit].value.toInt
            } else { 1 }

            // base case.
            resetState()
            initialize(false, true, false, context, labelBase, noLTLFilter)
            symbolicSimulate(0, k-1, true, false, context, labelBase, noLTLFilter) // if k - 1, symbolicSimulate is a NOP.

            // inductive step
            resetState()
            // we are assuming that the assertions hold for k-1 steps (by passing false, true to initialize and symbolicSimulate)
            initialize(true, false, true, context, labelStep, noLTLFilter)
            if ((k - 1) > 0) {
              symbolicSimulate(0, k-1, false, true, context, labelStep, noLTLFilter)
            }
            // now are asserting that the assertion holds by pass true, false to symbolicSimulate.
            symbolicSimulate(k-1, 1, true,  false, context, labelStep, noLTLFilter)

            // go back to original state.
            resetState()
          case "verify" =>
            val procName = cmd.args(0)._1.asInstanceOf[Identifier]
            val proc = module.procedures.find(p => p.id == procName).get
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString + ": verify(%s)".format(procName.toString())
              case None    => "verify(%s)".format(procName.toString)
            }
            verifyProcedure(proc, label)
          case "check" =>
            proofResults = assertionTree.verify(solver)
          case "synthesize_invariant" =>
            synthesizer match {
              case None =>
                UclidMain.println("Error: Can't execute synthesize_invariant as synthesizer was not provided. ")
              case Some(synth) => {
                synthesizeInvariants(context, noLTLFilter, synth, cmd.params(0).toString) match {
                  // Failed to synthesize invariant
                  case None => UclidMain.println("Failed to synthesize invariant.")
                  // Successfully synthesized an invariant
                  case Some(invFunc) => {
                    // Add synthesized function to list
                    synthesizedInvariants += invFunc
                    UclidMain.println("====== Successfully synthesized an invariant ======")
                    UclidMain.println(invFunc.toString())
                    UclidMain.println("===================================================")
                  }
                }
              }
            }
            
          case "print" =>
            UclidMain.println(cmd.args(0)._1.asInstanceOf[StringLit].value)
          case "print_results" =>
            dumpResults("print_results", defaultLog)
            printResults(proofResults, cmd.argObj, config)
          case "print_cex" =>
            printCEX(proofResults, cmd.args, cmd.argObj)
          case "print_smt2" =>
            printSMT2(assertionTree, cmd.argObj, solver)
          case "print_module" =>
            UclidMain.println(module.toString)
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
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> smt.EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.StateVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.SharedVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case _ => mapAcc
        }
      }
    }
  }

  /**
   * Create symbolic expressions for the init block.
   *
   * @param havocInit: if this is true, then the initial state is left unconstrained. If not, we execute the module's init block.
   * @param addAssertions: if this is true, then we assert module-level assertions, otherwise we ignore them unless addAssumptions = true.
   * @param addAssumptions: if this is true, then we assume module-level assertions, otherwise we assert them if addAssertions = true.
   * @param scope: is the context.
   * @param label: is a label for the result (this may be auto-generated if none is specified by the user.)
   * @param filter is a function that tells us which properties (module-level assertions/invariants) should be considered.
   * 	             For property p if filter(p.id, p.decorators) == false, then the property is ignored.
   */
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
  }

  def newInputSymbols(st : SymbolTable, step : Int, scope : Scope) : SymbolTable = {
    scope.map.foldLeft(st)((acc, decl) => {
      decl._2 match {
        case Scope.InputVar(id, typ) => acc + (id -> newInputSymbol(id.name, step, smt.Converter.typeToSMT(typ)))
        case _ => acc
      }
    })
  }

  /**
   * Create new SMT symbolic variables for each state.
   *
   * This is called after each step of symbolic simulation and prevents the expression
   * trees from blowing up.
   *
   * @param st The symbol table.
   * @param step The current frame number.
   * @param scope The current scope.
   */
  def renameStates(st : SymbolTable, frameNumber : Int, scope : Scope) : SymbolTable = {
    val renamedExprs = scope.map.map(_._2).collect {
      case Scope.StateVar(id, typ) =>
        val newVariable = newStateSymbol(id.name, frameNumber, smt.Converter.typeToSMT(typ))
        val stateExpr = st.get(id).get
        val smtExpr = smt.OperatorApplication(smt.EqualityOp, List(newVariable, stateExpr))
        (id, newVariable, smtExpr)
    }
    renamedExprs.foreach(p => addAssumption(p._3))
    renamedExprs.foldLeft(st)((acc, p) => st + (p._1 -> p._2))
  }

  /**
   * Create symbolic expressions for the next block.
   *
   * @param startStep The step number from which start (usually 1, except for k-induction, where it is k.)
   * @param numberOfSteps The number of steps for which to execute.
   * @param addAssertions If this is true, then all module-level assertions are asserted. If this is false, then assertions are ignored unless addAssertionsAsAssume = true.
   * @param addAssertionsAsAsume If this is true, then module-level assertion are assumed, not asserted.
   * @param scope The current scope.
   * @param label A label associated with the current verification task.
   * @param filter A function which identifies which assertions are to be considered.
   */
  def symbolicSimulate(
      startStep: Int, numberOfSteps: Int, addAssertions : Boolean, addAssertionsAsAssumes : Boolean, 
      scope : Scope, label : String, filter : ((Identifier, List[ExprDecorator]) => Boolean))
  {
    var currentState = symbolTable
    var states = new ArrayBuffer[SymbolTable]()
    // add initial state.
    for (step <- 1 to numberOfSteps) {
      val stWInputs = newInputSymbols(currentState, step + startStep, scope)
      states += stWInputs
      currentState = renameStates(simulate(step + startStep, stWInputs, scope, label), step + startStep, scope)
      val numPastFrames = frameTable.size
      val pastTables = ((0 to (numPastFrames - 1)) zip frameTable).map(p => ((numPastFrames - p._1) -> p._2)).toMap
      frameTable += currentState
      addModuleAssumptions(currentState, pastTables, scope)
      if (addAssertions) { addAsserts(step, currentState, pastTables, label, scope, filter)  }
      if (addAssertionsAsAssumes) { assumeAssertions(currentState, pastTables, scope) }
    }
    symbolTable = currentState
  }

  def printResults(assertionResults : List[CheckResult], arg : Option[Identifier], config : UclidMain.Config) {
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
    UclidMain.println("%d assertions passed.".format(passCount))
    UclidMain.println("%d assertions failed.".format(failCount))
    UclidMain.println("%d assertions indeterminate.".format(undetCount))

    if (config.verbose > 0) {
      assertionResults.foreach{ (p) =>
        if (p.result.isTrue) {
          UclidMain.println("  PASSED -> " + p.assert.toString)
        }
      }
    }
    if (failCount > 0) {
      assertionResults.foreach{ (p) =>
        if (p.result.isFalse) {
          UclidMain.println("  FAILED -> " + p.assert.toString)
        }
      }
    }
    if (undetCount > 0) {
      assertionResults.foreach{ (p) =>
        if (p.result.isUndefined) {
          UclidMain.println("  UNDEF -> " + p.assert.toString)
        }
      }
    }
  }

  def printCEX(results : List[CheckResult], exprs : List[(Expr, String)], arg : Option[Identifier]) {
    def labelMatches(p : AssertInfo) : Boolean = {
      arg match {
        case Some(id) => id.toString == p.label || p.label.startsWith(id.toString + ":")
        case None => true
      }
    }
    results.foreach((res) => {
      if (labelMatches(res.assert) && res.result.isModelDefined) {
        printCEX(res, exprs)
      }
    })
  }

  def printCEX(res : CheckResult, exprs : List[(Expr, String)]) {
    UclidMain.println("CEX for %s".format(res.assert.toString, res.assert.pos.toString))
    val scope = res.assert.context
    lazy val instVarMap = module.getAnnotation[InstanceVarMapAnnotation]().get

    val exprsToPrint : List[(Expr, String)] = if (exprs.size == 0) {
      val vars = ((scope.inputs ++ scope.vars ++ scope.outputs).map { 
        p => {
          instVarMap.rMap.get(p.id) match {
            case Some(str) => (p.id, str)
            case None => (p.id, p.id.toString)
          }
        }
      })
      vars.toList.sortWith((l, r) => l._2 < r._2)
    } else {
      exprs
    }

    frameLog.debug("Assertion: {}", res.assert.expr.toString())
    frameLog.debug("FrameTable: {}", res.assert.frameTable.toString())

    val model = res.result.model.get
    val ft = res.assert.frameTable
    val indices = 0 to (ft.size - 1)
    (indices zip ft).foreach{ case (i, frame) => {
      UclidMain.println("=================================")
      UclidMain.println("Step #" + i.toString)
      val pastFrames = (0 to (i-1)).map(j => (j + 1) -> ft(i - 1 - j)).toMap
      printFrame(frame, pastFrames, model, exprsToPrint, scope)
      UclidMain.println("=================================")
    }}
  }

  def printSMT2(aTree : AssertionTree, label : Option[Identifier], solver : smt.Context) {
    throw new Utils.UnimplementedException("Implement print_smt2.")
  }

  def printFrame(f : SymbolTable, pastFrames : Map[Int, SymbolTable], m : smt.Model, exprs : List[(Expr, String)], scope : Scope) {
    def expr(id : lang.Identifier) : Option[smt.Expr] = {
      if (f.contains(id)) { Some(evaluate(id, f, pastFrames, scope)) }
      else { None }
    }

    exprs.foreach { (e) => {
      try {
        val result = m.evalAsString(evaluate(e._1, f, pastFrames, scope))
        UclidMain.println("  " + e._2 + " : " + result)
      } catch {
        case excp : Utils.UnknownIdentifierException =>
          UclidMain.println("  " + e.toString + " : <UNDEF> ")
      }
    }}
  }

  def printSymbolTable(symbolTable : SymbolTable) {
    val keys = symbolTable.keys.toList.sortWith((l, r) => l.name < r.name)
    keys.foreach {
      (k) => {
        UclidMain.println (k.toString + " : " + symbolTable.get(k).get.toString)
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

  /** Debug logger. */
  def logState(logger : Logger, label : String, symTbl : SymbolTable) {
    logger.debug("==" + label + "==")
    symTbl.foreach {
      case (id, expr) =>
        logger.debug("  {} -> {}", id.toString(), expr.toString())
    }
  }

  def verifyProcedure(proc : ProcedureDecl, label : String) = {
    val procScope = context + proc
    val initSymbolTable = getInitSymbolTable(context)
    val initProcState0 = newInputSymbols(initSymbolTable, 1, context)
    val initProcState1 = proc.sig.inParams.foldLeft(initProcState0)((acc, arg) => {
      acc + (arg._1 -> newInputSymbol(arg._1.name, 1, smt.Converter.typeToSMT(arg._2)))
    })
    val initProcState = proc.sig.outParams.foldLeft(initProcState1)((acc, arg) => {
      acc + (arg._1 -> newHavocSymbol(arg._1.name, smt.Converter.typeToSMT(arg._2)))
    })
    frameTable.clear()
    frameTable += initProcState
    logState(verifyProcedureLog, "initProcState", initProcState)
    // add assumption.
    proc.requires.foreach(r => assertionTree.addAssumption(evaluate(r, initProcState, Map.empty, procScope)))
    // simulate procedure execution.
    val finalState = simulate(1, List.empty, proc.body, initProcState, procScope, label)
    // create frame table.
    frameTable += finalState
    logState(verifyProcedureLog, "finalState", finalState)

    val frameTableP = frameTable.clone()
    // add assertions.
    proc.ensures.foreach {
      e => {
        val name = "postcondition"
        val expr = evaluate(e, finalState, Map(1 -> initProcState), procScope)
        val assert = AssertInfo(name, label, frameTableP, procScope, 1, smt.BooleanLit(true), expr, List.empty, e.position)
        frameLog.debug("FrameTable: {}", assert.frameTable.toString())
        assertionTree.addAssert(assert)
      }
    }
    resetState()

  }

  def getDefaultSymbolTable(scope : Scope) : SymbolTable = {
    scope.map.foldLeft(Map.empty[Identifier, smt.Expr]){
      (mapAcc, decl) => {
        decl._2 match {
          case Scope.ConstantVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.Function(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> smt.EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.StateVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.SharedVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case _ => mapAcc
        }
      }
    }
  }

  def synthesizeInvariants(ctx : Scope, filter : ((Identifier, List[ExprDecorator]) => Boolean), synthesizer : smt.SynthesisContext, logic : String) : Option[lang.Expr] = {
    resetState()
    // FIXME: need to account for getInitSymbolTable in the constraints generated by synthesizer.synthesizeInvariant.
    val defaultSymbolTable = getDefaultSymbolTable(ctx)
    val initState = simulate(0, List.empty, module.init.get.body, defaultSymbolTable, ctx, "synthesize")
    val nextState = simulate(0, List.empty, module.next.get.body, defaultSymbolTable, ctx, "synthesize")
    val invariants = ctx.specs.map(specVar => {
      val prop = module.properties.find(p => p.id == specVar.varId).get
      if (filter(prop.id, prop.params)) {
        Some(evaluate(prop.expr, defaultSymbolTable, Map.empty, ctx))
      } else {
        None
      }
    }).flatten.toList
    return synthesizer.synthesizeInvariant(initState, nextState, invariants, ctx, logic)
  }

  /** Add module specifications (properties) to the list of proof obligations */
  def addAsserts(frameNumber : Int, symbolTable : SymbolTable, pastTables : Map[Int, SymbolTable],
                label : String, scope : Scope, filter : ((Identifier, List[ExprDecorator]) => Boolean)) {
    val table = frameTable.clone()
    scope.specs.foreach(specVar => {
      val prop = module.properties.find(p => p.id == specVar.varId).get
      if (filter(prop.id, prop.params)) {
        val property = AssertInfo(prop.name, label, table, scope, frameNumber, smt.BooleanLit(true), evaluate(prop.expr, symbolTable, pastTables, scope), prop.params, prop.expr.position)
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

  def simulate(frameNumber : Int, symbolTable: SymbolTable, scope : Scope, label : String) : SymbolTable = {
    simulate(frameNumber, List.empty, module.next.get.body, symbolTable, scope, label)
  }

  def simulate(frameNumber : Int, pathConditions: List[smt.Expr], stmts: List[Statement], symbolTable: SymbolTable, scope : Scope, label : String) : SymbolTable = {
    return stmts.foldLeft(symbolTable)((acc,i) => simulate(frameNumber, pathConditions, i, acc, scope, label));
  }

  def simulate(frameNumber : Int, pathConditions: List[smt.Expr], s: Statement, symbolTable: SymbolTable, scope : Scope, label : String) : SymbolTable = {
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
      var st : SymbolTable = input;
      def lhs(i: (Lhs,smt.Expr)) = { i._1 }
      def rhs(i: (Lhs,smt.Expr)) = { i._2 }
      (lhss zip args).foreach { x =>
        lhs(x) match {
          case LhsId(id) =>
            st = st + (id -> rhs(x))
          case LhsNextId(id) =>
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

    lazy val initPathCondExpr : smt.Expr = smt.BooleanLit(true)
    lazy val pathCondExpr = pathConditions.foldLeft(initPathCondExpr) {
      (acc, pc) => {
        smt.OperatorApplication(smt.ConjunctionOp, List(acc, pc))
      }
    }

    frameLog.debug("statement: %s".format(s.toString()))
    frameLog.debug("symbolTable: %s".format(symbolTable.toString()))
    s match {
      case SkipStmt() => return symbolTable
      case AssertStmt(e, id) =>
        val frameTableP = frameTable.clone()
        frameTableP += symbolTable
        val assertionName : String = id match {
          case None => "assertion"
          case Some(i) => i.toString()
        }
        val assertExpr = evaluate(e,symbolTable, pastTables, scope)
        val assert = AssertInfo(
                assertionName, label, frameTableP,
                scope, frameNumber, pathCondExpr,
                assertExpr, List.empty, s.position)
        assertLog.debug("Assertion: {}", e.toString)
        assertLog.debug("VC: {}", assertExpr.toString)
        frameLog.debug("FrameTableSize: {}", frameTableP.size)
        addAssert(assert)
        return symbolTable
      case AssumeStmt(e, id) =>
        val assumpExpr = evaluate(e,symbolTable, pastTables, scope)
        val effectiveExpr = smt.OperatorApplication(smt.ImplicationOp, List(pathCondExpr, assumpExpr))
        addAssumption(effectiveExpr)
        return symbolTable
      case HavocStmt(h) =>
        h match {
          case HavocableId(id) =>
            return symbolTable.updated(id, newHavocSymbol(id.name, smt.Converter.typeToSMT(scope.typeOf(id).get)))
          case HavocableNextId(id) =>
            throw new Utils.AssertionError("HavocableNextIds should have eliminated by now.")
          case HavocableFreshLit(f) =>
            throw new Utils.AssertionError("Fresh literals must have been eliminated by now.")
        }
      case AssignStmt(lhss,rhss) =>
        val es = rhss.map(i => evaluate(i, symbolTable, pastTables, scope));
        return simulateAssign(lhss, es, symbolTable, label)
      case BlockStmt(vars, stmts) =>
        val declaredVars = vars.flatMap(vs => vs.ids.map(v => (v, vs.typ)))
        val initSymbolTable = symbolTable
        val localSymbolTable = declaredVars.foldLeft(initSymbolTable) { 
          (acc, v) => acc + (v._1 -> newHavocSymbol(v._1.name, smt.Converter.typeToSMT(v._2)))
        }
        val overwrittenSymbols : List[(Identifier, smt.Expr)] = declaredVars.foldLeft(List.empty[(Identifier, smt.Expr)]) {
          (acc, v) => {
            initSymbolTable.get(v._1) match {
              case None => acc
              case Some(expr) => (v._1 -> expr) :: acc
            }
          }
        }

        frameLog.debug("declared variables  : " + vars.toString())
        frameLog.debug("init symbol table   : " + initSymbolTable.toString())
        frameLog.debug("local symbol table  : " + localSymbolTable.toString())
        frameLog.debug("overwritten symbols : " + overwrittenSymbols.toString())

        val simTable1 = simulate(frameNumber, pathConditions, stmts, localSymbolTable, scope + vars, label)
        val simTable2 = declaredVars.foldLeft(simTable1)((tbl, p) => tbl - p._1)
        overwrittenSymbols.foldLeft(simTable2)((acc, p) => acc + (p._1 -> p._2))
      case IfElseStmt(e,then_branch,else_branch) =>
        var then_modifies : Set[Identifier] = writeSet(then_branch)
        var else_modifies : Set[Identifier] = writeSet(else_branch)
        // compute in parallel.
        val condExpr = evaluate(e, symbolTable, pastTables, scope)
        val negCondExpr = smt.OperatorApplication(smt.NegationOp, List(condExpr))
        var then_st : SymbolTable = simulate(frameNumber, condExpr :: pathConditions, then_branch, symbolTable, scope, label)
        var else_st : SymbolTable = simulate(frameNumber, negCondExpr :: pathConditions, else_branch, symbolTable, scope, label)
        return symbolTable.keys.filter { id => then_modifies.contains(id) || else_modifies.contains(id) }.
          foldLeft(symbolTable){ (acc,id) =>
            acc.updated(id, smt.OperatorApplication(smt.ITEOp, List(condExpr, then_st(id), else_st(id))))
          }
      case ForStmt(_, _, _, _) => throw new Utils.AssertionError("Cannot symbolically execute for loops.")
      case WhileStmt(_, _, _) => throw new Utils.AssertionError("Cannot symbolically execute while loops.")
      case CaseStmt(_) => throw new Utils.AssertionError("Cannot symbolically execute case statement.")
      case ProcedureCallStmt(id,lhss,args) => throw new Utils.AssertionError("Cannot symbolically execute procedure calls.")
      case ModuleCallStmt(_) => throw new Utils.AssertionError("Cannot symbolically execute module calls.")
    }
  }

  def writeSet(stmt: Statement) : Set[Identifier] = stmt match {
    case SkipStmt() => Set.empty
    case AssertStmt(e, id) => Set.empty
    case AssumeStmt(e, id) => Set.empty
    case HavocStmt(h) => 
      h match {
        case HavocableId(id) =>
          Set(id)
        case HavocableNextId(id) =>
          throw new Utils.AssertionError("HavocableNextIds should have been eliminated by now.")
        case HavocableFreshLit(f) =>
          throw new Utils.AssertionError("Fresh literals must have been eliminated by now.")
      }
    case AssignStmt(lhss,rhss) =>
      return lhss.map(lhs => lhs.ident).toSet
    case BlockStmt(vars, stmts) =>
      val declaredVars : Set[Identifier] = vars.flatMap(vs => vs.ids.map(id => id)).toSet
      return writeSets(stmts) -- declaredVars
    case IfElseStmt(e,then_branch,else_branch) =>
      return writeSet(then_branch) ++ writeSet(else_branch)
    case ForStmt(id, typ, range, body) => return writeSet(body)
    case WhileStmt(_, body, invs) => return writeSet(body)
    case CaseStmt(body) =>
      return body.foldLeft(Set.empty[Identifier]) { (acc,i) => acc ++ writeSet(i._2) }
    case ProcedureCallStmt(id,lhss,args) =>
      throw new Utils.RuntimeError("ProcedureCallStmt must have been inlined by now.")
    case ModuleCallStmt(id) =>
      throw new Utils.RuntimeError("ModuleCallStmt must have been inlined by now.")
  }
  def writeSets(stmts: List[Statement]) : Set[Identifier] = {
    return stmts.foldLeft(Set.empty[Identifier]){(acc,s) => acc ++ writeSet(s)}
  }

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
    frameLog.debug("expr: %s".format(e.toString()))
    frameLog.debug("symbolTable: %s".format(symbolTable.toString()))
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
