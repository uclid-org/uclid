
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
import vcd.VCD

import scala.util.Try
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import com.typesafe.scalalogging.Logger
import uclid.smt.{Z3HornSolver, Z3Interface}

import scala.collection.mutable.{Map => MutableMap}
import org.scalactic.source.Position
import scala.util.parsing.input.NoPosition

object UniqueIdGenerator {
  var i : Int = 0;
  def unique() : Int = {i = i + 1; return i}
}

object SymbolicSimulator {
  type SymbolTable = Map[Identifier, smt.Expr]
  type FrameTable = ArrayBuffer[SymbolTable]
  type SymbolHyperTable = Map[Identifier, Array[smt.Expr]]
  type FrameHyperTable = Array[SymbolHyperTable]
  type SimulationTable = ArrayBuffer[FrameTable]
  def simRecordLength(simRecord : SimulationTable) : Int = {
    Utils.assert(simRecord.size > 0, "Invalid length")
    val sz = simRecord(0).size
    Utils.assert(simRecord.forall(ft => ft.size == sz), "Invalid lengths")
    sz
  }
}

class SymbolicSimulator (module : Module) {
  type SymbolTable = SymbolicSimulator.SymbolTable
  type FrameTable = SymbolicSimulator.FrameTable
  type SymbolHyperTable = SymbolicSimulator.SymbolHyperTable
  type FrameHyperTable = SymbolicSimulator.FrameHyperTable
  type SimulationTable = SymbolicSimulator.SimulationTable

  val context = Scope.empty + module
  var assertionTree = new AssertionTree()
  val defaultLog = Logger(classOf[SymbolicSimulator])
  val frameLog = Logger("uclid.SymbolicSimulator.frame")
  val assertLog = Logger("uclid.SymbolicSimulator.assert")
  val verifyProcedureLog = Logger("uclid.SymbolicSimulator.verifyProc")

  var assumes = new ListBuffer[smt.Expr]()
  var hyperAssumes = new ListBuffer[smt.Expr]()
  var asserts = new ListBuffer[AssertInfo]()
  var hyperAsserts = new ListBuffer[AssertInfo]()

  var symbolTable : SymbolTable = Map.empty
  var frameList : FrameTable = ArrayBuffer.empty

  var lazySC : Option[LazySCSolver] = None
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
  def newOracleSymbol(name: String, t: FunctionSig, binary : String) = {
    new smt.OracleSymbol("oracle_" + name, t, binary)
  }
  def newSynthSymbol(name: String, t: FunctionSig, gSym : Option[smt.GrammarSymbol], gargs: List[String], conds : List[Expr]) = {
    new smt.SynthSymbol("synth_" + name, t, gSym, gargs, conds)
  }
  def newGrammarSymbol(name: String, t: smt.Type, nts: List[smt.NonTerminal]) = {
    new smt.GrammarSymbol("grammar_" + name, t, nts)
  }
  def newTaintSymbol(name: String, t: smt.Type) = {
    new smt.Symbol("taint_" + UniqueIdGenerator.unique() + "_" + name, t)
  }

  /** Helper that converts a scope grammar to GrammarSymbol
   *
   *  @grammar the scope grammar to convert
   *  @scope current context
   */
  def grammarToGrammarSymbol(gSym: lang.Identifier, typ : lang.FunctionSig, scope: lang.Scope): smt.GrammarSymbol = {
    val getgrammar = scope.get(gSym)
    val grammar : lang.Scope.Grammar = getgrammar match {
      case Some(_) => getgrammar.get.asInstanceOf[lang.Scope.Grammar]
      case None => throw new Utils.RuntimeError("SyGuS grammar not found: grammar " + gSym.toString())
    }
    if (grammar.gTyp.asInstanceOf[lang.MapType].outType != typ.retType) {
      throw new Utils.RuntimeError("SyGuS grammar type does not match synth-fun: for grammar " + gSym.toString())
    }
    val id = grammar.id.name
    val symbolTyp = smt.Converter.typeToSMT(grammar.gTyp)
    val nts = grammar.nts.map(smt.Converter.nonTerminalToSyGuS2(_, scope))
    smt.GrammarSymbol(id, symbolTyp, nts)
  }

  def resetState() {
    assertionTree.resetToInitial()
    symbolTable = Map.empty
    frameList.clear()
  }
  var proofResults : List[CheckResult] = List.empty
  def dumpResults(label: String, log : Logger) {
    log.debug("{} --> proofResults.size = {}", label, proofResults.size.toString)
  }
  def frameTableToHyperTable(frameTbl : FrameTable) : FrameHyperTable = {
    frameTbl.map {
      (symTbl) => { symTbl.map((sym) => (sym._1 -> Array(sym._2))) }
    }.toArray
  }
  def simTableToHyperTable(simTbl : SimulationTable) : FrameHyperTable = {
    Utils.assert(simTbl.size > 0, "Must have at least one array of frames")
    val numFrames = simTbl(0).size
    Utils.assert(simTbl.forall(frameTbl => frameTbl.size == numFrames), "Must have the same number of frames in each trace")
    val numTraces = simTbl.size
    (1 to numFrames).toArray.map {
      (frameIndex) => {
        val symTbl0 : SymbolTable = simTbl(0)(frameIndex)
        val ids0 = symTbl0.map(id => id._1)
        val ids = ids0.filter(id => simTbl.forall(frameTbl => frameTbl(frameIndex).contains(id)))
        ids.map(
            id => (id -> simTbl.map(frameTbl => frameTbl(frameIndex).get(id).get).toArray)
        ).toMap[Identifier, Array[smt.Expr]]
      }
    }
  }
  def execute(solver : smt.Context, config : UclidMain.Config) : List[CheckResult] = {
    proofResults = List.empty
    def noLTLFilter(name : Identifier, decorators : List[ExprDecorator], properties: List[Identifier]) : Boolean = {
      !ExprDecorator.isLTLProperty(decorators) &&
        (properties.isEmpty || properties.contains(name))
    }
    def createNoLTLFilter(properties : List[Identifier]) : ((Identifier, List[ExprDecorator]) => Boolean) = {
      (id : Identifier, decorators : List[ExprDecorator]) => noLTLFilter(id, decorators, properties)
    }
    def createLTLFilter(properties : List[Identifier]) : ((Identifier, List[ExprDecorator]) => Boolean) = {
      (id : Identifier, decorators : List[ExprDecorator]) => LTLFilter(id, decorators, properties)
    }

    def LTLFilter(name : Identifier, decorators: List[ExprDecorator], properties: List[Identifier]) : Boolean = {
      val nameStr = name.name
      val nameStrToCheck = if (nameStr.endsWith(":safety")) {
        nameStr.substring(0, nameStr.size - 7)
      } else if (nameStr.endsWith(":liveness")) {
        nameStr.substring(0, nameStr.size - 9)
      } else {
        nameStr
      }
      val nameToCheck = Identifier(nameStrToCheck)
      ExprDecorator.isLTLProperty(decorators) &&  
        (properties.isEmpty || properties.contains(nameToCheck))
    }
    def extractProperties(name : Identifier, params: List[CommandParams]) : List[Identifier] = {
      params.filter(p => p.name == name).flatMap(ps => ps.values.map(p => p.asInstanceOf[Identifier]))
    }

    def prove(isLTL: Boolean, hyperInv: Boolean, cmd: GenericProofCommand) =
    {
      UclidMain.printVerbose("Starting symbolic simulation for " + cmd.name)
      val start = System.nanoTime()
      val label : String = cmd.resultVar match {
        case Some(l) => l.toString
        case None    => cmd.name.toString
      }
      val properties : List[Identifier] = extractProperties(Identifier("properties"), cmd.params)
      val propertyFilter =  if(isLTL) createLTLFilter(properties)else createNoLTLFilter(properties)
      if(hyperInv)
      {
        UclidMain.printVerbose("Module has hyperproperties. Using symbolic simulation for hyperproperties")
        symbolicSimulateLambdas(0, cmd.args(0)._1.asInstanceOf[IntLit].value.toInt, true, false,
                                      context, label, propertyFilter, propertyFilter, solver);
      }
      else
      {
        UclidMain.printVerbose("Module has no hyperproperties. Using plain symbolic simulation")
        initialize(false, true, false, context, label, propertyFilter, propertyFilter)
        symbolicSimulate(0, cmd.args(0)._1.asInstanceOf[IntLit].value.toInt, true, false, context, label, 
                            propertyFilter, propertyFilter)
      }
      val delta =  (System.nanoTime() - start) / 1000000.0
      UclidMain.printStats(f"Symbolic simulation took ${delta}%.1f ms")
    }
    // add axioms as assumptions.
    module.cmds.foreach {
      (cmd) => {
        val start = System.nanoTime()
        UclidMain.printVerbose("Starting Symbolic Simulation")
        cmd.name.toString match {
          case "clear_context" =>
            assertionTree = new AssertionTree()
            proofResults = List.empty
            dumpResults("clear_context", defaultLog)
          case "unroll" | "bmc_noLTL" =>
            assertionTree.startVerificationScope()
            prove(false, hasHyperInvariant(module.properties), cmd)
          case "horn" =>
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString
              case None    => "horn"
            }
            val properties : List[Identifier] = extractProperties(Identifier("properties"), cmd.params)
            runHornSolver(context, label, createNoLTLFilter(properties), createNoLTLFilter(properties))
            val delta =  (System.nanoTime() - start) / 1000000.0
            UclidMain.printStats(f"Symbolic simulation for horn solver construction took $delta%.1f ms")
          case "lazysc" =>
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString
              case None    => "unroll"
            }
            val lz = new LazySCSolver(this)
            lazySC = Some(lz)
            val properties : List[Identifier] = extractProperties(Identifier("properties"), cmd.params)
            val propertyFilter = createNoLTLFilter(properties)
            runLazySC(lz, cmd.args(0)._1.asInstanceOf[IntLit].value.toInt, context, label, propertyFilter, propertyFilter, solver)
            val delta =  (System.nanoTime() - start) / 1000000.0
            UclidMain.printStats(f"Symbolic simulation for lazySC took $delta%.1f ms")
          case "bmc" =>
          // do the LTL properties
            assertionTree.startVerificationScope()
            // do nonLTL
            prove(false, hasHyperInvariant(module.properties), cmd)
            // do LTL
            prove(true, hasHyperInvariant(module.properties), cmd)
          case "bmc_LTL" =>
          // do the LTL properties
            assertionTree.startVerificationScope()
            prove(true, hasHyperInvariant(module.properties), cmd)
          case "induction" =>
            assertionTree.startVerificationScope()
            val labelBase : String = cmd.resultVar match {
              case Some(l) => l.toString + ": induction_base"
              case None    => "induction_base"
            }
            val labelStep : String = cmd.resultVar match {
              case Some(l) => l.toString + ": induction_step"
              case None    => "induction_step"
            }
            val k = if (cmd.args.size > 0) {
              cmd.args(0)._1.asInstanceOf[IntLit].value.toInt
            } else { 1 }

            // extract properties to be proven.
            val commandProperties : List[Identifier] = extractProperties(Identifier("properties"), cmd.params)
            val commandPreProperties : List[Identifier] = extractProperties(Identifier("pre"), cmd.params)
            val commandAssumeProperties: List[Identifier] = extractProperties(Identifier("assumptions"), cmd.params)
            val preStateProperties = if (commandPreProperties.size == 0) {
              commandProperties ++ commandAssumeProperties
            } else {
              commandProperties ++ commandAssumeProperties ++ commandPreProperties
            }
            val assumptionFilter = createNoLTLFilter(preStateProperties)
            val propertyFilter = createNoLTLFilter(commandProperties)
            def postAssumptionFilter(name : Identifier, decorators : List[ExprDecorator]) : Boolean = {
              !ExprDecorator.isLTLProperty(decorators) && (commandAssumeProperties.contains(name))
            }
            
            assertLog.debug("preStateProperties: {}", preStateProperties.toString())

            // base case.
            resetState()
            initialize(false, true, false, context, labelBase, assumptionFilter, propertyFilter)
            symbolicSimulate(0, k-1, true, false, context, labelBase, assumptionFilter, propertyFilter) // if k - 1 = 0, symbolicSimulate is a NOP.

            // inductive step
            resetState()
            // we are assuming that the assertions hold for k-1 steps (by passing false, true to initialize and symbolicSimulate)
            initialize(true, false, true, context, labelStep, assumptionFilter, propertyFilter)
            if ((k - 1) > 0) {
              symbolicSimulate(0, k-1, false, true, context, labelStep, assumptionFilter, propertyFilter)
            }
            // now are asserting that the assertion holds by pass true, false to symbolicSimulate.
            symbolicSimulate(k-1, 1, true,  false, context, labelStep, assumptionFilter, propertyFilter)
            val delta =  (System.nanoTime() - start) / 1000000.0
            UclidMain.printStats(f"Symbolic simulation for induction took $delta%.1f ms")
            // go back to original state.
            resetState()
          case "verify" =>
            val procName = cmd.args(0)._1.asInstanceOf[Identifier]
            val proc = module.procedures.find(p => p.id == procName).get
            val label : String = cmd.resultVar match {
              case Some(l) => l.toString + ": verify_%s".format(procName.toString())
              case None    => "verify_%s".format(procName.toString)
            }
            verifyProcedure(proc, label)
            val delta =  (System.nanoTime() - start) / 1000000.0
            UclidMain.printStats(f"Symbolic simulation for verify took $delta%.1f ms")
          case "check" => {
            val needModel = module.cmds.filter(p => p.isPrintCEX).size > 0
            lazySC match {
              case None => proofResults = assertionTree.verify(solver, needModel)
              case Some(lz) => proofResults = lz.assertionTree.verify(solver, needModel)
            }
            if (solver.filePrefix != "") {
              val smtOutput = solver.toString()
              val pref = solver.filePrefix
              if (config.smtSolver.size > 0) {
                Utils.writeToFile(f"$pref.smt2", smtOutput)
              } else if (config.synthesizer.size > 0) {
                Utils.writeToFile(f"$pref.sl", smtOutput)
              }
            } else if (config.synthesizer.size > 0) {
              proofResults = List(CheckResult(AssertInfo("Synth", "All", ArrayBuffer(frameList), context, 1, smt.BooleanLit(true), smt.BooleanLit(true), List.empty, ASTPosition(module.filename, NoPosition)), solver.checkSynth()))
            }
            dumpResults("print_results", defaultLog)
            printResults(proofResults, cmd.argObj, config)
          } 
          case "print" =>
            UclidMain.printStatus(cmd.args(0)._1.asInstanceOf[StringLit].value)
          case "print_results" =>
            // do nothing because we printed results when we checked
            // dumpResults("print_results", defaultLog)
            // printResults(proofResults, cmd.argObj, config)
          case "print_cex" =>
            printCEX(proofResults, cmd.args, cmd.argObj)
          case "dump_cex_vcds" =>
            dumpCEXVCDFiles(proofResults)
          case "print_module" =>
            UclidMain.printStatus(module.toString)
          case "set_solver_option" =>
            val option = cmd.args(0)._1.asInstanceOf[lang.StringLit].value
            val value : smt.Context.SolverOption = cmd.args(1)._1 match {
              case BoolLit(b) => smt.Context.BoolOption(b)
              case IntLit(i) => smt.Context.IntOption(i.toInt)
              case StringLit(s) => smt.Context.StringOption(s)
              case _ => throw new Utils.AssertionError(
                "Unexpected option value: " + cmd.args(1)._1.toString)
            }
            solver.addOption(option, value)
          case "assign_macro" =>
            UclidMain.printStatus("This will modify a macro")
            UclidMain.printStatus(cmd.args(0).toString())
            UclidMain.printStatus(cmd.macroBody.toString())
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
          case Scope.SynthesisFunction(id, typ, gSym, gargs, conds) => mapAcc + (id -> newSynthSymbol(id.name, typ, gSym.map(gSym => grammarToGrammarSymbol(gSym, typ, scope)), gargs.map(_.name), conds))
          case Scope.OracleFunction(id, typ, binary) => mapAcc + (id -> newOracleSymbol(id.name, typ, binary))
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> smt.EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.StateVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.SharedVar(id, typ) => mapAcc + (id -> newInitSymbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.Grammar(id, typ, nts) => mapAcc + (id -> newGrammarSymbol(id.name, smt.Converter.typeToSMT(typ), nts.map(smt.Converter.nonTerminalToSyGuS2(_, scope))))
          case _ => mapAcc
        }
      }
    }
  }


  def getVarsInOrder(map: Map[smt.Expr, Identifier], scope: Scope) : List[List[smt.Expr]] = {
    val ids = map.map(p => p._2).toList
    val reverse_map = map.map(_.swap)
    val const_vars = ids.filter(id => scope.get(id).get match {
      case Scope.ConstantVar(id, typ) => true
      case _ => false
    }).map(id => reverse_map.get(id).get).sortBy{
        v =>
          val s = v.toString.split("_")
          val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
           name
    }
    /*val func_vars = ids.filter(id => scope.get(id).get match {
      case Scope.Function(id, typ) => true
      case _ => false
    }).map(id => reverse_map.get(id).get)
    */
    val input_vars = ids.filter(id => scope.get(id).get match {
      case Scope.InputVar(id, typ) => true
      case _ => false
    }).map(id => reverse_map.get(id).get).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
        name
    }
    val output_vars = ids.filter(id => scope.get(id).get match {
      case Scope.OutputVar(id, typ) => true
      case _ => false
    }).map(id => reverse_map.get(id).get).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
        name
    }
    val state_vars = ids.filter(id => scope.get(id).get match {
      case Scope.StateVar(id, typ) => true
      case _ => false
    }).map(id => reverse_map.get(id).get).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
        name
    }
    val shared_vars = ids.filter(id => scope.get(id).get match {
      case Scope.SharedVar(id, typ) => true
      case _ => false
    }).map(id => reverse_map.get(id).get).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
        name
    }
    List(const_vars, input_vars, output_vars, state_vars, shared_vars)

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
  def initialize(havocInit : Boolean, addAssertions : Boolean, addAssumptions : Boolean, 
                 scope : Scope, label : String, 
                 assumptionFilter : ((Identifier, List[ExprDecorator]) => Boolean),
                 propertyFilter : ((Identifier, List[ExprDecorator]) => Boolean))
  {
    val initSymbolTable = getInitSymbolTable(scope)
    val frameTbl = ArrayBuffer(initSymbolTable)

    addModuleAssumptions(initSymbolTable, frameTbl, 0, scope, addAssumptionToTree _)

    symbolTable = if (!havocInit && module.init.isDefined) {
      simulateStmt(0, List.empty, module.init.get.body, initSymbolTable, frameTbl, scope, label, addAssumptionToTree _, addAssertToTree _)
    } else {
      initSymbolTable
    }

    addModuleAssumptions(symbolTable, frameTbl, 1, scope, addAssumptionToTree _)

    frameList.clear()
    frameList += symbolTable
    val simTbl : SimulationTable = ArrayBuffer(frameList)

    if (addAssertions) { addAsserts(0, symbolTable, frameList, simTbl, label, scope, propertyFilter, addAssertToTree _) }
    if (addAssumptions) { assumeAssertions(symbolTable, frameTbl, 1, scope, assumptionFilter, addAssumptionToTree _) }
  }

  def newInputSymbols(st : SymbolTable, step : Int, scope : Scope) : SymbolTable = {
    scope.map.foldLeft(st)((acc, decl) => {
      decl._2 match {
        case Scope.InputVar(id, typ) => acc + (id -> newInputSymbol(id.name, step, smt.Converter.typeToSMT(typ)))
        case _ => acc
      }
    })
  }

  def addAssumesToList(e: smt.Expr, params: List[ExprDecorator]) : Unit = {
    if (ExprDecorator.isHyperproperty(params)) {
      hyperAssumes += e
    } else {
      assumes += e
    }
  }

  def addHyperAssertsToList(assert: AssertInfo) : Unit = {
    hyperAsserts += assert
  }
  def addAssertsToList(assert: AssertInfo) : Unit = {
    asserts += assert
  }

  def clearAssumes() = {
    assumes.clear()
    asserts.clear()
    hyperAsserts.clear()
    hyperAssumes.clear()
  }

  def noHyperInvariantFilter(filter : ((Identifier, List[ExprDecorator]) => Boolean)) =  (n : Identifier, d : List[ExprDecorator]) => {
    filter(n, d) && !ExprDecorator.isHyperproperty(d)
  }

  def HyperInvariantFilter(filter : ((Identifier, List[ExprDecorator]) => Boolean)) =  (n : Identifier, d : List[ExprDecorator]) => {
    filter(n, d) && ExprDecorator.isHyperproperty(d)
  }
  def getInitLambda(havocInit: Boolean, addAssertions: Boolean, addAssumptions: Boolean, scope: Scope, label: String,
                    assumptionFilter: ((Identifier, List[ExprDecorator]) => Boolean),
                    propertyFilter : ((Identifier, List[ExprDecorator]) => Boolean)) = {
    clearAssumes()
    val initSymbolTable = getInitSymbolTable(scope)
    val initFrameTbl = ArrayBuffer(initSymbolTable)
    val symTab = if (!havocInit && module.init.isDefined) {
      simulateStmt(0, List.empty, module.init.get.body, initSymbolTable, initFrameTbl, scope, label, addAssumesToList _, addAssertsToList _)
    } else {
      initSymbolTable
    }

    addModuleAssumptions(symTab, initFrameTbl, 1, scope, addAssumesToList _)
    frameList.clear()
    frameList += initSymbolTable
    val simTbl : SimulationTable = ArrayBuffer(frameList)

    if (addAssertions) {
      addAsserts(1, symTab, frameList, simTbl, label, scope, noHyperInvariantFilter(propertyFilter), addAssertsToList _)
      addAsserts(1, symTab, frameList, simTbl, label, scope, HyperInvariantFilter(propertyFilter), addHyperAssertsToList _)
    }
    if (addAssumptions) { assumeAssertions(symTab, frameList, 1, scope, assumptionFilter, addAssumesToList _) }

    val reverse_map = initSymbolTable.map(_.swap) // Map new smt Vars back to IDs
    val conjunct = reverse_map.map(p => if (p._1 != symTab.get(reverse_map.get(p._1).get).get) Some(smt.OperatorApplication(smt.EqualityOp,

      List(p._1, symTab.get(reverse_map.get(p._1).get).get))) else None).toList.flatten ++ assumes.toList


    val conjunction = if (conjunct.length > 1) { smt.OperatorApplication(smt.ConjunctionOp, conjunct)}
                      else if (conjunct.length == 1) conjunct(0)
                      else new smt.BooleanLit(true)

    val lambda = smt.Lambda(getVarsInOrder(reverse_map, scope).flatten.map(p => p.asInstanceOf[smt.Symbol]), conjunction)
    (lambda, asserts.toList, initSymbolTable, hyperAsserts.toList, hyperAssumes.toList)
  }

  def getNextLambda(init_symTab: Map[Identifier, smt.Expr], addAssertions : Boolean, addAssertionsAsAssumes : Boolean,
                      scope : Scope, label : String,
                      assumptionFilter: ((Identifier, List[ExprDecorator]) => Boolean),
                      propertyFilter : ((Identifier, List[ExprDecorator]) => Boolean)) =
  {

    clearAssumes()

    var currentState = init_symTab
    val reverse_init_map = currentState.map(_.swap)
    val init_vars = getVarsInOrder(reverse_init_map, scope)

    var states = new ArrayBuffer[SymbolTable]()

    //frameTable += init_symTab
    // add initial state.

    val stWInputs = currentState//newInputSymbols(currentState, 1, scope)
    states += stWInputs
    val symTableP = simulateModuleNext(1, stWInputs, states, scope, label, addAssumesToList _, addAssertsToList _)
    var assumesLambda = assumes.clone()

    val eqStates = symTableP.filter(p => stWInputs.get(p._1) match {
      case Some(st) => (st == p._2)
      case None => false
    }).map(_._1).toSet

    defaultLog.debug("eqStates: {}", eqStates.toString())
    currentState = renameStatesLambda(symTableP, eqStates, 1, scope, addAssumesToList _)
    var assumesLength = assumes.length
    val numPastFrames = frameList.size
    frameList += currentState
    val simTbl = ArrayBuffer(frameList)
    addModuleAssumptions(currentState, frameList, numPastFrames, scope, addAssumesToList _)
    
    assumes.takeRight(assumes.length - assumesLength).foreach(expr => assumesLambda += expr)
    assumesLength = assumes.length

    if (addAssertions) {
      addAsserts(1, currentState, frameList, simTbl, label, scope, noHyperInvariantFilter(propertyFilter), addAssertsToList _)
      addAsserts(1, currentState, frameList, simTbl, label, scope, HyperInvariantFilter(propertyFilter), addHyperAssertsToList _)
    }
    if (addAssertionsAsAssumes) { assumeAssertions(currentState, frameList, numPastFrames, scope, assumptionFilter, addAssumesToList _) }
    assumes.takeRight(assumes.length - assumesLength).foreach(expr => assumesLambda += expr)


    // Output/Input vars are renamed in renameStatesLambda
    val final_vars = getVarsInOrder(currentState.map(_.swap), scope)

    val conjunct = if (assumes.length > 1) smt.OperatorApplication(smt.ConjunctionOp, assumes.toList)
                    else if (assumes.length == 0) new smt.BooleanLit(true)
                    else assumes(0)
    val lambda = smt.Lambda((init_vars.flatten ++ final_vars.flatten).map(p => p.asInstanceOf[smt.Symbol]), conjunct)


    (lambda, asserts.toList, currentState,
      hyperAsserts.toList, hyperAssumes.toList, assumesLambda.toList)
  }

  def runHornSolver(scope: Scope, label: String, 
      assumptionFilter : ((Identifier, List[ExprDecorator]) => Boolean),
      propertyFilter : ((Identifier, List[ExprDecorator]) => Boolean)) = {
    val init_lambda = getInitLambda(false, true, false, scope, label, assumptionFilter, propertyFilter)
    val next_lambda = getNextLambda(init_lambda._3, true, false, scope, label, assumptionFilter, propertyFilter)
    val h = new Z3HornSolver(this)
    val context = new Z3Interface()
    val lazySc = new LazySCSolver(this)
    val initTaintLambda = lazySc.getTaintInitLambdaV2(init_lambda._1, scope, context, init_lambda._5)
    val nextTaintLambda = lazySc.getNextTaintLambdaV2(next_lambda._1, next_lambda._5, next_lambda._6, next_lambda._4, scope)
    val combinedInitLambda = lazySc.getCombinedInitLambda(init_lambda._1, initTaintLambda)
    val combinedNextLambda = lazySc.getCombinedNextLambda(next_lambda._1, nextTaintLambda._1)
    //h.convertHyperInvToTaint(next_lambda._1, next_lambda._4)
    //h.solveTaintLambdasV2(combinedInitLambda, combinedNextLambda, scope)
    h.solveLambdas(init_lambda._1, next_lambda._1, init_lambda._5, init_lambda._2, init_lambda._4, next_lambda._4, next_lambda._5, next_lambda._2, scope)
  }

  def runLazySC(lazySC: LazySCSolver, bound: Int, scope: Scope, label: String, 
      assumptionFilter: ((Identifier, List[ExprDecorator]) => Boolean), 
      propertyFilter: ((Identifier, List[ExprDecorator]) => Boolean), 
      solver: smt.Context) = {

      //Z3HornSolver.test1()

      lazySC.simulateLazySCV2(bound, scope, label, assumptionFilter, propertyFilter)
  }

  def symbolicSimulateLambdasHyperAssert(startStep: Int, numberOfSteps: Int, hypPropIdx: Int, 
                              addAssertions : Boolean, addAssertionsAsAssumes : Boolean,
                              scope : Scope, label : String, 
                              assumptionFilter : ((Identifier, List[ExprDecorator]) => Boolean),
                              propertyFilter : ((Identifier, List[ExprDecorator]) => Boolean),
                              solver: smt.Context) = {
    // At this point symbolTable must have the initial symbols.
    resetState()

    val init_lambda = getInitLambda(false, true, false, scope, label, assumptionFilter, propertyFilter)
    val next_lambda = getNextLambda(init_lambda._3, true, false, scope, label, assumptionFilter, propertyFilter)
    //val s = new LazySCSolver(this, solver)

    val num_copies = getMaxHyperInvariant(scope)
    val simRecord = new SimulationTable
    var prevVarTable = new ArrayBuffer[List[List[smt.Expr]]]()
    var havocTable = new ArrayBuffer[List[(smt.Symbol, smt.Symbol)]]()

    var inputStep = 0
    for (i <- 1 to num_copies) {
      var frames = new FrameTable
      val initSymTab = newInputSymbols(getInitSymbolTable(scope), inputStep, scope)
      inputStep += 1
      frames += initSymTab
      var prevVars = getVarsInOrder(initSymTab.map(_.swap), scope)
      prevVarTable += prevVars
      val init_havocs = getHavocs(init_lambda._1.e)
      val havoc_subs = init_havocs.map {
        havoc =>
          val s = havoc.id.split("_")
          val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
          (havoc, newHavocSymbol(name, havoc.typ))
      }
      havocTable += havoc_subs
      val init_conjunct = substitute(betaSubstitution(init_lambda._1, prevVars.flatten), havoc_subs)
      addAssumptionToTree(init_conjunct, List.empty)
      simRecord += frames
    }

    val hyperAssumesInit = rewriteHyperAssumes(
      init_lambda._1, 0, init_lambda._5, simRecord, 0, scope, prevVarTable.toList)
    hyperAssumesInit.foreach {
      hypAssume =>
        addAssumptionToTree(hypAssume, List.empty)
    }

    /*
    val asserts_init = rewriteAsserts(
      init_lambda._1, init_lambda._2, 0,
      prevVarTable(0).flatten.map(p => p.asInstanceOf[smt.Symbol]),
      simRecord.clone(), havocTable(0))

    asserts_init.foreach {
      assert =>
        // FIXME: simTable
        addAssertToTree(assert)
    }
    */
    val filteredInitHyperAssert = List(init_lambda._4(hypPropIdx))
    val asserts_init_hyper = rewriteHyperAsserts(
      init_lambda._1, 0, filteredInitHyperAssert, simRecord, 0, scope, prevVarTable.toList)
    asserts_init_hyper.foreach {
      assert =>
        // FIXME: simTable
        addAssertToTree(assert)
    }

    var symTabStep = symbolTable
    for (i <- 1 to numberOfSteps) {
      for (j <- 1 to num_copies) {
        symTabStep = newInputSymbols(getInitSymbolTable(scope), inputStep, scope)
        inputStep += 1
        simRecord(j - 1) += symTabStep
        val new_vars = getVarsInOrder(symTabStep.map(_.swap), scope)
        val next_havocs = getHavocs(next_lambda._1.e)
        val havoc_subs = next_havocs.map {
          havoc =>
            val s = havoc.id.split("_")
            val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
            (havoc, newHavocSymbol(name, havoc.typ))
        }
        val next_conjunct = substitute(betaSubstitution(next_lambda._1, (prevVarTable(j - 1) ++ new_vars).flatten), havoc_subs)
        addAssumptionToTree(next_conjunct, List.empty)
        havocTable(j - 1) = havoc_subs
        prevVarTable(j - 1) = new_vars
      }

      val hyperAssumesNext = rewriteHyperAssumes(next_lambda._1, numberOfSteps, next_lambda._5, simRecord, i, scope, prevVarTable.toList)
      hyperAssumesNext.foreach {
        hypAssume =>
          addAssumptionToTree(hypAssume, List.empty)
      }
      /*
      // Asserting on-HyperInvariant assertions
      // FIXME: simTable
      val asserts_next = rewriteAsserts(
        next_lambda._1, next_lambda._2, i,
        getVarsInOrder(simRecord(0)(i - 1).map(_.swap), scope).flatten.map(p => p.asInstanceOf[smt.Symbol]) ++
          prevVarTable(0).flatten.map(p => p.asInstanceOf[smt.Symbol]), simRecord.clone(), havocTable(0))
      asserts_next.foreach {
        assert =>
          addAssertToTree(assert)
      }*/

      // FIXME: simTable
      defaultLog.debug("i: {}", i)
      val filteredNextHyperAssert = List(next_lambda._4(hypPropIdx))
      val asserts_next_hyper = rewriteHyperAsserts(next_lambda._1, numberOfSteps, filteredNextHyperAssert, simRecord, i, scope, prevVarTable.toList)
      asserts_next_hyper.foreach {
        assert => {
          addAssertToTree(assert)
        }
      }
    }
    symbolTable = symTabStep
    val needModel = module.cmds.filter(p => p.isPrintCEX).size > 0
    val results = assertionTree.verify(solver, needModel)
    UclidMain.printResult("The results are: " + results)
  }

  def symbolicSimulateLambdas(startStep: Int, numberOfSteps: Int, addAssertions : Boolean, addAssertionsAsAssumes : Boolean,
                              scope : Scope, label : String, 
                              assumptionFilter : ((Identifier, List[ExprDecorator]) => Boolean),
                              propertyFilter : ((Identifier, List[ExprDecorator]) => Boolean),
                              solver: smt.Context) = {
      // At this point symbolTable must have the initial symbols.
      resetState()

      val init_lambda = getInitLambda(false, true, false, scope, label, assumptionFilter, propertyFilter)
      val next_lambda = getNextLambda(init_lambda._3, true, false, scope, label, assumptionFilter, propertyFilter)
      //val s = new LazySCSolver(this, solver)

      val num_copies = getMaxHyperInvariant(scope)
      val simRecord = new SimulationTable
      var prevVarTable = new ArrayBuffer[List[List[smt.Expr]]]()
      var havocTable = new ArrayBuffer[List[(smt.Symbol, smt.Symbol)]]()

      var inputStep = 0
      for (i <- 1 to num_copies) {
        var frames = new FrameTable
        val initSymTab = newInputSymbols(getInitSymbolTable(scope), inputStep, scope)
        inputStep += 1
        frames += initSymTab
        var prevVars = getVarsInOrder(initSymTab.map(_.swap), scope)
        prevVarTable += prevVars
        val init_havocs = getHavocs(init_lambda._1.e)
        val havoc_subs = init_havocs.map {
          havoc =>
            val s = havoc.id.split("_")
            val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
            (havoc, newHavocSymbol(name, havoc.typ))
        }
        havocTable += havoc_subs
        val init_conjunct = substitute(betaSubstitution(init_lambda._1, prevVars.flatten), havoc_subs)
        addAssumptionToTree(init_conjunct, List.empty)
        simRecord += frames
      }

      val hyperAssumesInit = rewriteHyperAssumes(
          init_lambda._1, 0, init_lambda._5, simRecord, 0, scope, prevVarTable.toList)
      hyperAssumesInit.foreach {
        hypAssume =>
          addAssumptionToTree(hypAssume, List.empty)
      }


      val asserts_init = rewriteAsserts(
          init_lambda._1, init_lambda._2, 0,
          prevVarTable(0).flatten.map(p => p.asInstanceOf[smt.Symbol]),
          simRecord.clone(), havocTable(0))

      asserts_init.foreach {
        assert =>
          // FIXME: simTable
          addAssertToTree(assert)
      }

      val asserts_init_hyper = rewriteHyperAsserts(
          init_lambda._1, 0, init_lambda._4, simRecord, 0, scope, prevVarTable.toList)
      asserts_init_hyper.foreach {
        assert =>
          // FIXME: simTable
          addAssertToTree(assert)
      }

      var symTabStep = symbolTable
      for (i <- 1 to numberOfSteps) {
          for (j <- 1 to num_copies) {
            symTabStep = newInputSymbols(getInitSymbolTable(scope), inputStep, scope)
            inputStep += 1
            simRecord(j - 1) += symTabStep
            val new_vars = getVarsInOrder(symTabStep.map(_.swap), scope)
            val next_havocs = getHavocs(next_lambda._1.e)
            val havoc_subs = next_havocs.map {
              havoc =>
                val s = havoc.id.split("_")
                val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
                (havoc, newHavocSymbol(name, havoc.typ))
            }
            val next_conjunct = substitute(betaSubstitution(next_lambda._1, (prevVarTable(j - 1) ++ new_vars).flatten), havoc_subs)
            addAssumptionToTree(next_conjunct, List.empty)
            havocTable(j - 1) = havoc_subs
            prevVarTable(j - 1) = new_vars
          }

          val hyperAssumesNext = rewriteHyperAssumes(next_lambda._1, numberOfSteps, next_lambda._5, simRecord, i, scope, prevVarTable.toList)
          hyperAssumesNext.foreach {
            hypAssume =>
              addAssumptionToTree(hypAssume, List.empty)
          }
          // Asserting on-HyperInvariant assertions
          // FIXME: simTable
          val asserts_next = rewriteAsserts(
              next_lambda._1, next_lambda._2, i,
              getVarsInOrder(simRecord(0)(i - 1).map(_.swap), scope).flatten.map(p => p.asInstanceOf[smt.Symbol]) ++
              prevVarTable(0).flatten.map(p => p.asInstanceOf[smt.Symbol]), simRecord.clone(), havocTable(0))
          asserts_next.foreach {
            assert =>
              addAssertToTree(assert)
          }
          // FIXME: simTable
          defaultLog.debug("i: {}", i)
          val asserts_next_hyper = rewriteHyperAsserts(next_lambda._1, numberOfSteps, next_lambda._4, simRecord, i, scope, prevVarTable.toList)
          asserts_next_hyper.foreach {
            assert => {
              addAssertToTree(assert)
            }
          }
      }
      symbolTable = symTabStep
  }

  def rewriteHyperAssumes(
      lambda: smt.Lambda, stepIndex : Integer, hyperAssumes: List[smt.Expr],
      simTable: SimulationTable, step: Int, scope: Scope, prevVarTable: List[List[List[smt.Expr]]]) = {
      hyperAssumes.map {
        hypAssume =>
          rewriteHyperAssume(lambda, stepIndex, hypAssume, simTable, step, scope, prevVarTable)
      }
  }

  //FIXME: Only hyperSelects are rewritten, other variables remain as is.
  //FIXME: Variables without hyperSelects are the unconstrained lambda variables
  def rewriteHyperAssume(
      lambda: smt.Lambda, stepIndex : Integer, hypAssume: smt.Expr,
      simRecord: SimulationTable, step: Int, scope: Scope, prevVars: List[List[List[smt.Expr]]]) = {

      val hyperSelects = getHyperSelects(hypAssume)
      val subs = hyperSelects.map {
      expr =>
        val op = expr.op
        val exp = expr.operands
        op match {
          case smt.HyperSelectOp(i) =>
            if (stepIndex > 0) {
              val actual_params = getVarsInOrder(simRecord(i - 1)(step - 1).map(_.swap), scope).flatten ++ prevVars(i - 1).flatten
              val formal_params = lambda.ids
              assert(actual_params.length == formal_params.length)
              val matches = formal_params.zip(actual_params)
              val final_expr = substitute(exp(0), matches)
              (expr, final_expr)
            }
            else {
              val actual_params = getVarsInOrder(simRecord(i - 1)(step).map(_.swap), scope).flatten
              val formal_params = lambda.ids
              assert(actual_params.length == formal_params.length)
              val matches = formal_params.zip(actual_params)
              val final_expr = substitute(exp(0), matches)
              (expr, final_expr)
            }
          case _ =>
            throw new Utils.RuntimeError("Should never get here.")
        }
    }
    substitute(hypAssume, subs)
  }
  def rewriteHyperAsserts(
      lambda: smt.Lambda, stepIndex : Integer, hyperAsserts: List[AssertInfo], 
      simTable: SimulationTable, step: Int, scope: Scope, prevVarTable: List[List[List[smt.Expr]]]) = {
    hyperAsserts.map {
      assert => {
        defaultLog.debug("step: {}", step)
        rewriteHyperAssert(lambda, stepIndex, assert, simTable, step, scope, prevVarTable)
      }
    }
  }

  def cloneSimRecord(simRecord : SimulationTable) : SimulationTable = {
    simRecord.map(ft => ft.clone()).clone()
  }
  def simRecordLength(simRecord : SimulationTable) : Int = SymbolicSimulator.simRecordLength(simRecord)

  //FIXME: Only hyperSelects are rewritten, other variables remain as is.
  //FIXME: Variables without hyperSelects are the unconstrained lambda variables
  def rewriteHyperAssert(
      lambda: smt.Lambda, stepIndex : Integer, at: AssertInfo, 
      simRecord: SimulationTable, step: Int, scope: Scope, prevVars: List[List[List[smt.Expr]]]) = {

      val hyper_selects = getHyperSelects(at.expr)
      val subs = hyper_selects.map {
        expr =>
          val op = expr.op
          val exp = expr.operands
          op match {
            case smt.HyperSelectOp(i) =>
              if (stepIndex > 0) {
                val actual_params = getVarsInOrder(simRecord(i - 1)(step).map(_.swap), scope).flatten ++ prevVars(i - 1).flatten
                val formal_params = lambda.ids
                assert(actual_params.length == formal_params.length)
                val matches = formal_params.zip(actual_params)
                val final_expr = substitute(exp(0), matches)
                (expr, final_expr)
              }
              else {
                val actual_params = getVarsInOrder(simRecord(i - 1)(step).map(_.swap), scope).flatten
                val formal_params = lambda.ids
                assert(actual_params.length == formal_params.length)
                val matches = formal_params.zip(actual_params)
                val final_expr = substitute(exp(0), matches)
                (expr, final_expr)
              }
            case _ =>
              throw new Utils.RuntimeError("Should never get here.")
          }
      }
      // FIXME: simTable
      val st = AssertInfo(at.name, at.label, cloneSimRecord(simRecord), at.context, step,
                  at.pathCond, substitute(at.expr, subs), at.decorators, at.pos)
      Utils.assert(st.iter + 1 == simRecordLength(st.frameTable), "Invalid length/step combination")
      defaultLog.debug("insi: {}", step)
      defaultLog.debug("[rewrite] iter: {} length: {}", st.iter, SymbolicSimulator.simRecordLength(st.frameTable))
      st
  }

  def getHyperSelects(e: smt.Expr): List[smt.OperatorApplication]  = {
    e match {
      case smt.Symbol(id, symbolTyp) => List()
      case smt.SynthSymbol(id, symbolTyp, _, _, _) => List()
      case smt.OracleSymbol(id, symbolTyp, _) => List()
      case smt.IntLit(n) => List()
      case smt.BooleanLit(b) => List()
      case smt.BitVectorLit(bv, w) => List()
      case smt.EnumLit(id, eTyp) => List()
      case smt.ConstArray(v, arrTyp) => List()
      case smt.MakeTuple(args) => args.flatMap(e => getHyperSelects(e))
      case opapp : smt.OperatorApplication =>
        val op = opapp.op
        val args = opapp.operands.flatMap(exp => getHyperSelects(exp))
        op match {
          case smt.HyperSelectOp(i) => List(opapp) ++ args
          case _ => args
        }
      case smt.ArraySelectOperation(a,index) =>  getHyperSelects(a) ++ index.flatMap(e => getHyperSelects(e))
      case smt.ArrayStoreOperation(a,index,value) =>
        getHyperSelects(a) ++ index.flatMap(e => getHyperSelects(e)) ++ getHyperSelects(value)
      case smt.FunctionApplication(f, args) =>
        args.flatMap(arg => getHyperSelects(arg))
      case _ =>
        throw new Utils.UnimplementedException("'" + e + "' is not yet supported.")
    }

  }
  def getMaxHyperInvariant(scope: Scope) = {
    var max_k = 1
    scope.specs.foreach(specVar => {
      val prop = module.properties.find(p => p.id == specVar.varId).get
      if (ExprDecorator.isHyperproperty(prop.params)) {
         val hyperdec = prop.params.filter(param => param match {
           case HyperpropertyDecorator(k) => true
           case _ => false
         })
         if (max_k < hyperdec(0).asInstanceOf[HyperpropertyDecorator].k) {
           max_k = hyperdec(0).asInstanceOf[HyperpropertyDecorator].k
         }
      }
    })
    max_k
  }

  def hasHyperInvariant(properties: List[SpecDecl]) : Boolean = {
    properties.foreach(prop => {
      if (ExprDecorator.isHyperproperty(prop.params))
        return true;
      })
    return false;
  }

  def getHavocs(e: smt.Expr): List[smt.Symbol] = {
    e match {
      case smt.Symbol(id, symbolTyp) =>
        if (id.startsWith("havoc_")) List(e.asInstanceOf[smt.Symbol]) else List()
      case smt.SynthSymbol(id, symbolTyp, _, _, _) =>
        List()
      case smt.OracleSymbol(_, _, _) =>
        List()
      case smt.IntLit(n) => List()
      case smt.BooleanLit(b) => List()
      case smt.BitVectorLit(bv, w) => List()
      case smt.EnumLit(id, eTyp) => List()
      case smt.ConstArray(v, arrTyp) => List()
      case smt.MakeTuple(args) => args.flatMap(e => getHavocs(e))
      case opapp : smt.OperatorApplication =>
        val op = opapp.op
        val args = opapp.operands.flatMap(exp => getHavocs(exp))
        args

      case smt.ArraySelectOperation(a,index) =>  getHavocs(a) ++ index.flatMap(e => getHavocs(e))
      case smt.ArrayStoreOperation(a,index,value) =>
        getHavocs(a) ++  index.flatMap(e => getHavocs(e)) ++ getHavocs(value)
      case smt.FunctionApplication(f, args) =>
        val f1 = f match {
          case smt.Symbol(id, symbolTyp) =>
            if (id.startsWith("havoc_")) List(e.asInstanceOf[smt.Symbol]) else List()
          case smt.SynthSymbol(id, symbolTyp, _, _, _) =>
            List()
          case smt.OracleSymbol(_, _, _) =>
            List()
          case _ =>
            throw new Utils.RuntimeError("Should never get here.")
        }
        f1 ++ args.flatMap(arg => getHavocs(arg))
      case _ =>
        throw new Utils.UnimplementedException("'" + e + "' is not yet supported.")
    }
  }

  def rewriteAsserts(
      lambda: smt.Lambda, asserts: List[AssertInfo], stepIndex : Integer, 
      actualVars: List[smt.Symbol], simTable: SimulationTable, 
      havocSubs: List[(smt.Symbol, smt.Symbol)]): List[AssertInfo] = {

    Utils.assert(lambda.ids.length == actualVars.length, "Invalid arguments to rewriteAsserts")
    val matches = lambda.ids.zip(actualVars)
    asserts.map(assert => rewriteAssert(assert, matches, stepIndex, simTable, havocSubs))
  }

  def rewriteAssert(
      assert: AssertInfo, matches: List[(smt.Symbol, smt.Symbol)], stepIndex : Integer, 
      simTable: SimulationTable, havocsubs: List[(smt.Symbol, smt.Symbol)]): AssertInfo = {
    defaultLog.debug("rewriteAssert/step: {}", stepIndex)
    AssertInfo(assert.name, assert.label, cloneSimRecord(simTable), 
        assert.context, stepIndex, substitute(substitute(assert.pathCond, matches), havocsubs),
        substitute(substitute(assert.expr, matches), havocsubs), assert.decorators, assert.pos)
  }

  def betaSubstitution(lambda: smt.Lambda, args: List[smt.Expr]): smt.Expr = {
      val formal_params = lambda.ids
      val actual_params = args.map(p => p.asInstanceOf[smt.Symbol])

      assert(formal_params.length == actual_params.length)
      val matches = formal_params.zip(actual_params)
      substitute(lambda.e, matches)
  }


  def substitute(e: smt.Expr, s: List[(smt.Expr, smt.Expr)]): smt.Expr = {
    val m = s.map(p => p._1 -> p._2).toMap
    def rewrite(ex: smt.Expr) : smt.Expr = {
      m.get(ex) match {
        case Some(eX) => eX
        case None => ex
      }
    }
    s.foldLeft(e)((acc, p) => _substitute(acc, p))
    //var memo: MutableMap[smt.Expr, smt.Expr] = MutableMap.empty
    //smt.Context.rewriteExpr(e, rewrite, memo)
  }

  def _substitute(e: smt.Expr, sym: (smt.Expr, smt.Expr)): smt.Expr = {
    //Causes a possible slowdown
    //if (e == sym._1)
    //  return sym._2

    e match {
      case smt.Symbol(id, symbolTyp) => {
        if (sym._1 == e) sym._2
        else e
      }
      case smt.SynthSymbol(id, symbolTyp, _, _, _) => {
        if (sym._1 == e) sym._2
        else e
      }
      case smt.OracleSymbol( _, _, _) => {
        if (sym._1 == e) sym._2
        else e
      }
      case smt.IntLit(n) => e
      case smt.BooleanLit(b) => e
      case smt.BitVectorLit(bv, w) => e
      case smt.EnumLit(id, eTyp) => e
      case smt.ConstArray(exp, arrTyp) => smt.ConstArray(_substitute(exp, sym), arrTyp)
      case smt.MakeTuple(args) => smt.MakeTuple(args.map(e => _substitute(e, sym)))
      case opapp : smt.OperatorApplication =>
        val op = opapp.op
        op match {
          case smt.HyperSelectOp(i) =>
            if (e == sym._1)
              return sym._2
          case _ =>
        }

        val args = opapp.operands.map(exp => _substitute(exp, sym))
        smt.OperatorApplication(op, args)

      case smt.ArraySelectOperation(a,index) =>
        smt.ArraySelectOperation(_substitute(a, sym), index.map(e => _substitute(e, sym)))
      case smt.ArrayStoreOperation(a,index,value) =>
        smt.ArrayStoreOperation(_substitute(a, sym), index.map(e => _substitute(e, sym)), _substitute(value, sym))
      case smt.FunctionApplication(f, args) =>
        val f1 = f match {
          case smt.Symbol(id, symbolTyp) =>
            if (sym._1 == f) sym._2 else f
          case smt.SynthSymbol(id, symbolTyp, _, _, _) =>
            if (sym._1 == f) sym._2 else f
          case smt.OracleSymbol(id, symbolTyp, _) =>
            if (sym._1 == f) sym._2 else f
          case _ =>
            throw new Utils.RuntimeError("Should never get here.")
        }
        smt.FunctionApplication(f1, args.map(e => _substitute(e, sym)))
      case _ =>
        throw new Utils.UnimplementedException("'" + e + "' is not yet supported.")
    }
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
  def renameStates(st : SymbolTable, eqStates : Set[Identifier], frameNumber : Int, scope : Scope, addAssumption : (smt.Expr, List[ExprDecorator]) => Unit) : SymbolTable = {
    val renamedExprs : Iterable[(Identifier, smt.Symbol, smt.Expr)] = scope.map.map(_._2).map {
      case Scope.StateVar(id, typ) =>
        if (!eqStates.contains(id)) {
          val newVariable = newStateSymbol(id.name, frameNumber, smt.Converter.typeToSMT(typ))
          val stateExpr = st.get(id).get
          val smtExpr = smt.OperatorApplication(smt.EqualityOp, List(newVariable, stateExpr))
          Some(id, newVariable, smtExpr)
        } else {
          None
        }
      case _ => None
    }.flatten
    renamedExprs.foreach{ 
      (p) => addAssumption(p._3, List.empty)
    }
    renamedExprs.foldLeft(st)((acc, p) => acc + (p._1 -> p._2))
  }

  def renameStatesLambda(st : SymbolTable, eqStates : Set[Identifier], frameNumber : Int, scope : Scope, addAssumption : (smt.Expr, List[ExprDecorator])  => Unit) : SymbolTable = {
    val renamedExprs : Iterable[(Identifier, smt.Symbol, smt.Expr)] = scope.map.map(_._2).map {
      case Scope.StateVar(id, typ) =>
          val newVariable = newStateSymbol(id.name, frameNumber, smt.Converter.typeToSMT(typ))
          val stateExpr = st.get(id).get
          val smtExpr = smt.OperatorApplication(smt.EqualityOp, List(newVariable, stateExpr))
          Some(id, newVariable, smtExpr)
      case Scope.OutputVar(id, typ) => {
          val newVariable = newStateSymbol(id.name, frameNumber, smt.Converter.typeToSMT(typ))
          val stateExpr = st.get(id).get
          val smtExpr = smt.OperatorApplication(smt.EqualityOp, List(newVariable, stateExpr))
          Some(id, newVariable, smtExpr)
      }
      case Scope.SharedVar(id, typ) => {
        val newVariable = newStateSymbol(id.name, frameNumber, smt.Converter.typeToSMT(typ))
        val stateExpr = st.get(id).get
        val smtExpr = smt.OperatorApplication(smt.EqualityOp, List(newVariable, stateExpr))
        Some(id, newVariable, smtExpr)

      }
      case Scope.InputVar(id, typ) => {
        val newVariable = newInputSymbol(id.name, frameNumber, smt.Converter.typeToSMT(typ))
        val stateExpr = st.get(id).get
        val smtExpr = smt.OperatorApplication(smt.EqualityOp, List(newVariable, stateExpr))
        Some(id, newVariable, smtExpr)

      }
      case _ => None
    }.flatten
    renamedExprs.foreach{
      // FIXME: revisit(AssumptionDecorator)
      (p) => addAssumption(p._3, List.empty)
    }
    renamedExprs.foldLeft(st)((acc, p) => acc + (p._1 -> p._2))
  }

  /**
   * Create symbolic expressions for the next block.
   *
   * @param startStep The step number from which start (usually 1, except for k-induction, where it is k.)
   * @param numberOfSteps The number of steps for which to execute.
   * @param addAssertions If this is true, then all module-level assertions are asserted. If this is false, then assertions are ignored unless addAssertionsAsAssume = true.
   * @param addAssertionsAsAssumes If this is true, then module-level assertion are assumed, not asserted.
   * @param scope The current scope.
   * @param label A label associated with the current verification task.
   * @param filter A function which identifies which assertions are to be considered.
   */
  def symbolicSimulate(
      startStep: Int, numberOfSteps: Int, addAssertions : Boolean, addAssertionsAsAssumes : Boolean,
      scope : Scope, label : String, 
      assumptionFilter : ((Identifier, List[ExprDecorator]) => Boolean),
      propertyFilter: ((Identifier, List[ExprDecorator]) => Boolean))
  {
    var currentState = symbolTable
    var states = new ArrayBuffer[SymbolTable]()
    // add initial state.
    for (step <- 1 to numberOfSteps) {
      val stWInputs = newInputSymbols(currentState, step + startStep, scope)
      states += stWInputs
      addModuleAssumptions(stWInputs, frameList, frameList.size, scope, addAssumptionToTree _)
      val symTableP = simulateModuleNext(step + startStep, stWInputs, frameList, scope, label, addAssumptionToTree _, addAssertToTree _)
      val eqStates = symTableP.filter(p => stWInputs.get(p._1) match {
        case Some(st) => (st == p._2)
        case None => false
      }).map(_._1).toSet
      defaultLog.debug("eqStates: {}", eqStates.toString())
      currentState = renameStates(symTableP, eqStates, step + startStep, scope, addAssumptionToTree _)
      val numPastFrames = frameList.size
      val pastTables = ((0 to (numPastFrames - 1)) zip frameList).map(p => ((numPastFrames - p._1) -> p._2)).toMap
      frameList += currentState
      val simTbl = ArrayBuffer(frameList)
      // FIXME: simTable
      addModuleAssumptions(currentState, frameList, numPastFrames, scope, addAssumptionToTree _)
      if (addAssertions) { addAsserts(step, currentState, frameList, simTbl, label, scope, propertyFilter, addAssertToTree _)  }
      if (addAssertionsAsAssumes) { assumeAssertions(currentState, frameList, numPastFrames, scope, assumptionFilter, addAssumptionToTree _) }
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

    if(!config.smtFileGeneration.isEmpty)
    {
      UclidMain.printStatus("Printed SMTlib file(s) for %d assertions".format(undetCount))
      return
    }

    Utils.assert(passCount + failCount + undetCount == assertionResults.size, "Unexpected assertion count.")
    UclidMain.printResult("%d assertions passed.".format(passCount))
    UclidMain.printResult("%d assertions failed.".format(failCount))
    UclidMain.printResult("%d assertions indeterminate.".format(undetCount))

    if (config.verbose > 0) {
      assertionResults.foreach{ (p) =>
        if (p.result.isTrue) {
          UclidMain.printStatus("  PASSED -> " + p.assert.toString)
        }
      }
    }
    if (failCount > 0) {
      assertionResults.foreach{ (p) =>
        if (p.result.isFalse) {
          UclidMain.printStatus("  FAILED -> " + p.assert.toString)
          defaultLog.debug("FAILED EXPR -> " + p.assert.expr.toString())
        }
      }
    }
    if (undetCount > 0) {
      assertionResults.foreach{ (p) =>
        if (p.result.isUndefined) {
          UclidMain.printStatus("  UNDEF -> " + p.assert.toString)
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
    UclidMain.printStatus("CEX for %s".format(res.assert.toString, res.assert.pos.toString))
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
    val simTable = res.assert.frameTable
    Utils.assert(simTable.size >= 1, "Must have at least one trace")
    val lastFrame = res.assert.iter
    (0 to lastFrame).foreach{ case (i) => {
      UclidMain.printStatus("=================================")
      UclidMain.printStatus("Step #" + i.toString)
      try{
          printFrame(simTable, i, model, exprsToPrint, scope)
      }  catch{
            case _: Throwable => UclidMain.printError("error: unable to parse counterexample frame")
      }
      UclidMain.printStatus("=================================")
    }}
  }

  def printFrame(simTable : SimulationTable, frameNumber : Int, m : smt.Model, exprs : List[(Expr, String)], scope : Scope) {
    exprs.foreach { (e) => {
      try {
        val exprs = simTable.map(ft => m.evalAsString(evaluate(e._1, ft(frameNumber), ft, frameNumber, scope)))
        val strings = Utils.join(exprs.map(_.toString()), ", ")
        UclidMain.printStatus("  " + e._2 + " : " + strings)
      } catch {
        case excp : Utils.UnknownIdentifierException =>
          UclidMain.printStatus("  " + e.toString + " : <UNDEF> ")
      }
    }}
  }
// this function is unused
  def printSymbolTable(symbolTable : SymbolTable) {
    val keys = symbolTable.keys.toList.sortWith((l, r) => l.name < r.name)
    keys.foreach {
      (k) => {
        UclidMain.printVerbose(k.toString + " : " + symbolTable.get(k).get.toString)
      }
    }
  }

  def dumpCEXVCDFiles(results : List[CheckResult]) {
    results.filter(_.result.isModelDefined).foreach(dumpCEXVCD(_))
  }

  def dumpCEXVCD(res : CheckResult) {
    val filename = "%s_step_%d.vcd".format(res.assert.name.map{ case ' ' | ':' => '_' case c => c } , res.assert.iter)
    // Integers are represented as 64b values
    val defaultIntWidth = 64
    val scope = res.assert.context
    lazy val instVarMap = module.getAnnotation[InstanceVarMapAnnotation]().get
    val vars = ((scope.inputs ++ scope.vars ++ scope.outputs).map {
      p => {
        instVarMap.rMap.get(p.id) match {
          case Some(str) => (p, str)
          case None => (p, p.id.toString)
        }
      }
    })

    def getTypeWidth(t: Type): Int = t match {
      case BooleanType() => 1
      case BitVectorType(w: Int) => w
      case IntegerType() => defaultIntWidth
      case _ => throw new Utils.UnimplementedException("VCD dumping supports only bitvector, boolean, and integer types.")
    }

    val vcdWriter = VCD("Top")
    vcdWriter.addWire("Step", defaultIntWidth)
    val activeSortedVars =  vars.toList.sortWith((l, r) => l._2 < r._2).filter(v => Try(getTypeWidth(v._1.typ)).isSuccess)
    activeSortedVars.foreach(v => vcdWriter.addWire(v._2, getTypeWidth(v._1.typ)))
    val model = res.result.model.get
    Utils.assert(res.assert.frameTable.size == 1, "Must have exactly one frame table")
    val ft = res.assert.frameTable(0)
    val indices = 0 to (ft.size - 1)
    (indices zip ft).foreach{ case (i, frame) => {
      vcdWriter.wireChanged("Step", i)
      updateFrameVCD(vcdWriter, frame, ft, i, model, activeSortedVars, scope)
      vcdWriter.incrementTime()
    }}
    vcdWriter.wireChanged("Step", ft.size)
    vcdWriter.incrementTime()
    vcdWriter.write(filename)
  }

  def updateFrameVCD(vcd : VCD, f : SymbolTable, frameTbl : FrameTable, frameNumber : Int, m : smt.Model, exprs : List[(Scope.NamedExpression, String)], scope : Scope) {
    exprs.foreach { (e) => {
      try {
        val result = m.evalAsString(evaluate(e._1.id, f, frameTbl, frameNumber, scope))
        val value = (Try(if (result.toBoolean) BigInt(1) else BigInt(0)).toOption ++ Try(BigInt(result)).toOption).head
        vcd.wireChanged(e._2, value)
      } catch {
        case excp : Utils.UnknownIdentifierException =>
          UclidMain.printResult("  " + e.toString + " : <UNDEF> ")
      }
    }}
  }

  /** Add assertion. */
  def addAssertToTree(prop : AssertInfo) {
    assertionTree.addAssert(prop)
  }
  /** Add assumption. */
  def addAssumptionToTree(e : smt.Expr, params : List[ExprDecorator]) {
    assertLog.debug("Assumption: {}", e.toString())
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

  // Helper functions to verify a procedure
  // NOTE: The following helper functions are writting in a lot of separate places, we
  //          might want to figure out a way to place it somewhere so that we don't 
  //          have to write it in all the classes we use it in (code cleanliness)
  
  def isStatelessExpression(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)    | Scope.InputVar(_, _)  |
               Scope.OutputVar(_, _)   | Scope.SharedVar(_, _) |
               Scope.FunctionArg(_, _) | Scope.Define(_, _, _) |
               Scope.Instance(_)       | Scope.Group(_, _, _) =>
             false
          case Scope.ConstantVar(_, _)      | Scope.Function(_, _)       |
               Scope.LambdaVar(_ , _)       | Scope.ForallVar(_, _)      |
               Scope.ExistsVar(_, _)        | Scope.EnumIdentifier(_, _) |
               Scope.ConstantLit(_, _)      | Scope.SynthesisFunction(_, _, _, _, _) |
               Scope.OracleFunction(_, _, _)| Scope.GroupVar(_, _) =>
             true
          case Scope.ModuleDefinition(_)      | Scope.Grammar(_, _, _)          |
               Scope.TypeSynonym(_, _)        | Scope.Procedure(_, _)           |
               Scope.ProcedureInputArg(_ , _) | Scope.ProcedureOutputArg(_ , _) |
               Scope.ForIndexVar(_ , _)       | Scope.SpecVar(_ , _, _)         |
               Scope.AxiomVar(_ , _, _)       | Scope.VerifResultVar(_, _)      |
               Scope.BlockVar(_, _)           | Scope.SelectorField(_)          |
               Scope.NonTerminal(_, _, _)     | Scope.Macro(_, _, _)           =>
             throw new Utils.RuntimeError("Can't have this identifier in assertion: " + namedExpr.toString())
        }
      case None =>
        throw new Utils.RuntimeError("Unknown identifiers should have been detected by now.")
    }
  }
  def isStatelessExpr(e: Expr, context : Scope) : Boolean = {
    e match {
      case id : Identifier =>
        isStatelessExpression(id, context)
      case ei : ExternalIdentifier =>
        true
      case lit : Literal =>
        true
      case rec : Tuple =>
        rec.values.forall(e => isStatelessExpr(e, context))
      case OperatorApplication(ArraySelect(inds), args) =>
        inds.forall(ind => isStatelessExpr(ind, context)) &&
        args.forall(arg => isStatelessExpr(arg, context))
      case OperatorApplication(ArrayUpdate(inds, value), args) =>
        inds.forall(ind => isStatelessExpr(ind, context)) &&
        args.forall(arg => isStatelessExpr(arg, context)) &&
        isStatelessExpr(value, context)
      case opapp : OperatorApplication =>
        opapp.operands.forall(arg => isStatelessExpr(arg, context + opapp.op))
      case a : ConstArray =>
        isStatelessExpr(a.exp, context)
      case fapp : FuncApplication =>
        isStatelessExpr(fapp.e, context) && fapp.args.forall(a => isStatelessExpr(a, context))
      case lambda : Lambda =>
        isStatelessExpr(lambda.e, context + lambda)
    }
  }

  def verifyProcedure(proc : ProcedureDecl, label : String) = {
    assertionTree.startVerificationScope()

    val procScope = context + proc
    val initSymbolTable = getInitSymbolTable(context)
    val initProcState0 = newInputSymbols(initSymbolTable, 1, context)
    val initProcState1 = proc.sig.inParams.foldLeft(initProcState0)((acc, arg) => {
      acc + (arg._1 -> newInputSymbol(arg._1.name, 1, smt.Converter.typeToSMT(arg._2)))
    })
    val initProcState = proc.sig.outParams.foldLeft(initProcState1)((acc, arg) => {
      acc + (arg._1 -> newHavocSymbol(arg._1.name, smt.Converter.typeToSMT(arg._2)))
    })
    frameList.clear()
    frameList += initProcState
    logState(verifyProcedureLog, "initProcState", initProcState)

    // add all axioms in procedure scope, independent of state variable references
    (Scope.empty + proc).map.foreach {
      case (id, e : Scope.AxiomVar) => {
        assertionTree.addAssumption(evaluate(e.expr, initProcState, ArrayBuffer.empty, 0, procScope))
      }
      case _ => // Do nothing
    }

    // add all stateless module level axioms
    context.map.foreach {
      case (id, e : Scope.AxiomVar) => {
        if (isStatelessExpr(e.expr, procScope)) {
          assertionTree.addAssumption(evaluate(e.expr, initProcState, ArrayBuffer.empty, 0, procScope))
        }
      }
      case _ => // Do nothing
    }

    // add assumption.
    proc.requires.foreach(r => assertionTree.addAssumption(evaluate(r, initProcState, ArrayBuffer.empty, 0, procScope)))
    // simulate procedure execution.
    val finalState = simulateStmt(1, List.empty, proc.body, initProcState, frameList, procScope, label, addAssumptionToTree _, addAssertToTree _)
    // create frame table.
    frameList += finalState
    logState(verifyProcedureLog, "finalState", finalState)

    val simTable = ArrayBuffer(frameList.clone())
    // add assertions.
    proc.ensures.foreach {
      e => {
        val name = "postcondition"
        val expr = evaluate(e, finalState, ArrayBuffer(initProcState), 1, procScope)
        val assert = AssertInfo(name, label, simTable.clone(), procScope, 1, smt.BooleanLit(true), expr, List.empty, e.position)
        frameLog.debug("FrameTable: {}", assert.frameTable.toString())
        // FIXME: need to store simTable here.
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
          case Scope.SynthesisFunction(id, typ, gSym, gargs, conds) => mapAcc + (id -> smt.SynthSymbol(id.name, typ, gSym.map(gSym => grammarToGrammarSymbol(gSym, typ, scope)), gargs.map(_.name), conds))
          case Scope.OracleFunction(id, typ, binary) => mapAcc + (id -> smt.OracleSymbol(id.name, typ, binary))
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> smt.EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.StateVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.SharedVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.Grammar(id, typ, nts) => mapAcc + (id -> smt.GrammarSymbol(id.name, smt.Converter.typeToSMT(typ), nts.map(smt.Converter.nonTerminalToSyGuS2(_, scope))))
          case _ => mapAcc
        }
      }
    }
  }
  def getIndexedSymbolTable(scope : Scope, index : Integer) : SymbolTable = {
    scope.map.foldLeft(Map.empty[Identifier, smt.Expr]){
      (mapAcc, decl) => {
        decl._2 match {
          case Scope.ConstantVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.Function(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.SynthesisFunction(id, typ, gSym, gargs, conds) => mapAcc + (id -> smt.SynthSymbol(id.name, typ, gSym.map(gSym => grammarToGrammarSymbol(gSym, typ, scope)), gargs.map(_.name), conds))
          case Scope.OracleFunction(id, typ, binary) => mapAcc + (id -> smt.OracleSymbol(id.name, typ, binary))
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> smt.EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name + "$" + index.toString(), smt.Converter.typeToSMT(typ)))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name + "$" + index.toString(), smt.Converter.typeToSMT(typ)))
          case Scope.StateVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name + "$" + index.toString(), smt.Converter.typeToSMT(typ)))
          case Scope.SharedVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name + "$" + index.toString(), smt.Converter.typeToSMT(typ)))
          case Scope.Grammar(id, typ, nts) => mapAcc + (id -> smt.GrammarSymbol(id.name, smt.Converter.typeToSMT(typ), nts.map(smt.Converter.nonTerminalToSyGuS2(_, scope))))
          case _ => mapAcc
        }
      }
    }
  }
  def getPrimeSymbolTable(scope : Scope) : SymbolTable = {
    scope.map.foldLeft(Map.empty[Identifier, smt.Expr]){
      (mapAcc, decl) => {
        decl._2 match {
          case Scope.ConstantVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.SynthesisFunction(id, typ, gSym, gargs, conds) => mapAcc + (id -> smt.SynthSymbol(id.name, typ, gSym.map(gSym => grammarToGrammarSymbol(gSym, typ, scope)), gargs.map(_.name), conds))
          case Scope.Function(id, typ) => mapAcc // functions should never be primed
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> smt.EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name, smt.Converter.typeToSMT(typ)))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name + "!", smt.Converter.typeToSMT(typ)))
          case Scope.StateVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name + "!", smt.Converter.typeToSMT(typ)))
          case Scope.SharedVar(id, typ) => mapAcc + (id -> smt.Symbol(id.name + "!", smt.Converter.typeToSMT(typ)))
          case Scope.Grammar(id, typ, nts) => mapAcc + (id -> smt.GrammarSymbol(id.name, smt.Converter.typeToSMT(typ), nts.map(smt.Converter.nonTerminalToSyGuS2(_, scope))))
          case _ => mapAcc
        }
      }
    }
  }

  def createTransitionRelation(ctx : Scope, st : lang.Statement, x0 : SymbolTable, x1 : SymbolTable, label : String) : smt.Expr = {
    var assumptions : ArrayBuffer[smt.Expr] = new ArrayBuffer[smt.Expr]()
    def addAssumption(e : smt.Expr, params : List[ExprDecorator]) : Unit = { assumptions += e }
    var assertions  : ArrayBuffer[AssertInfo] = new ArrayBuffer[AssertInfo]()
    def addAssertion(e : AssertInfo) : Unit = { assertions += e }

    // Symbolically simulate statement.
    val frameTbl : FrameTable = ArrayBuffer.empty
    val symbolicState = simulateStmt(0, List.empty, st, x0, frameTbl, ctx, label, addAssumption _, addAssertion _)
    // Compute init expression from the result of symbolic simulation.
    val symbolicExpressions = (symbolicState.map {
      p => {
        val id = p._1
        ctx.get(id).get match {
          case Scope.StateVar(_, _) | Scope.OutputVar(_, _) | Scope.SharedVar(_, _) =>
            val lhs = x1.get(id).get
            val rhs = p._2
            smt.OperatorApplication(smt.EqualityOp, List(lhs, rhs))
          case _ =>
            smt.BooleanLit(true)
        }
      }
    }.toList ++ assumptions.toList).filter(p => p != smt.BooleanLit(true))
    // Return a conjunction of these expressions.
    smt.Operator.conjunction(symbolicExpressions)
  }

  /** Add module specifications (properties) to the list of proof obligations */
  def addAsserts(frameNumber : Int, symbolTable : SymbolTable, frameTbl : FrameTable, simTbl : SimulationTable,
                label : String, scope : Scope, filter : ((Identifier, List[ExprDecorator]) => Boolean),
                addAssert : (AssertInfo => Unit)) {

    scope.specs.foreach(specVar => {
      val prop = module.properties.find(p => p.id == specVar.varId).get
      if (filter(prop.id, prop.params)) {
        val property = AssertInfo(
            prop.name, label, simTbl.map(ft => ft.clone()), scope, frameNumber, smt.BooleanLit(true),
            evaluate(prop.expr, symbolTable, frameTbl, frameNumber, scope), prop.params, prop.expr.position)
        addAssert(property)
      }
    })
  }

  /** Add module-level axioms/assumptions. */
  def addModuleAssumptions(symbolTable : SymbolTable, frameTbl : FrameTable, frameNumber : Int, scope : Scope, addAssumption : (smt.Expr, List[ExprDecorator]) => Unit) {
    module.axioms.foreach(ax => addAssumption(evaluate(ax.expr, symbolTable, frameTbl, frameNumber, scope), ax.params))
  }

  /** Assume assertions (for inductive proofs). */
  def assumeAssertions(symbolTable : SymbolTable, frameTbl : FrameTable, frameNumber : Int, scope : Scope,
                       filter : ((Identifier, List[ExprDecorator]) => Boolean),
                       addAssumption : (smt.Expr, List[ExprDecorator]) => Unit) {
    scope.specs.foreach(sp => 
      {
        val prop = module.properties.find(p => p.id == sp.varId).get
        if (filter(prop.id, prop.params)) {
          assertLog.debug("selected: {}", prop.id.toString())
          addAssumption(evaluate(sp.expr, symbolTable, frameTbl, frameNumber, scope), sp.params)
        } else {
          assertLog.debug("rejected: {}", prop.id.toString())
        }
      })
  }

  def simulateModuleNext(frameNumber : Int, symbolTable: SymbolTable, frameTable : FrameTable, scope : Scope, label : String,
               addAssume : (smt.Expr, List[ExprDecorator]) => Unit, addAssert : (AssertInfo => Unit)) : SymbolTable = {
    simulateStmt(frameNumber, List.empty, module.next.get.body, symbolTable, frameTable, scope, label, addAssume, addAssert)
  }

  def simulateStmt(frameNumber : Int, pathConditions: List[smt.Expr], s: Statement,
               symbolTable: SymbolTable, frameTable : FrameTable, scope : Scope, label : String,
               addAssumption : (smt.Expr, List[ExprDecorator]) => Unit, addAssert : (AssertInfo => Unit)) : SymbolTable = {

    // Accumulate over a list of statements.
    def simulateStmtList(stmts: List[Statement], symbolTable: SymbolTable, scope : Scope) : SymbolTable = {
        return stmts.foldLeft(symbolTable){
        (acc,i) => simulateStmt(frameNumber, pathConditions, i, acc, frameTable, scope, label, addAssumption, addAssert);
      }
    }

    // Helper function to read from a record.
    def recordSelect(field : String, rec : smt.Expr) = {
      smt.OperatorApplication(smt.RecordSelectOp(field), List(rec))
    }
    // Helper function to update a record.
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
            st = st + (id -> smt.ArrayStoreOperation(st(id), indices.map(i => evaluate(i, st, frameTable, frameNumber, scope)), rhs(x)))
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
        val simTable = ArrayBuffer(frameTableP)
        val assertionName : String = id match {
          case None => "assertion"
          case Some(i) => i.toString()
        }
        val assertExpr = evaluate(e,symbolTable, frameTable, frameNumber, scope)
        val assert = AssertInfo(
                assertionName, label, simTable.clone(),
                scope, frameNumber, pathCondExpr,
                assertExpr, List.empty, s.position)
        assertLog.debug("Assertion: {}", e.toString)
        assertLog.debug("VC: {}", assertExpr.toString)
        frameLog.debug("FrameTableSize: {}", frameTableP.size)
        addAssert(assert)
        return symbolTable
      case AssumeStmt(e, id) =>
        val assumpExpr = evaluate(e,symbolTable, frameTable, frameNumber, scope)
        UclidMain.printVerbose("----Assumption Expr ---- " + e.toString)
        val effectiveExpr = if (pathCondExpr == smt.BooleanLit(true)) {
          assumpExpr
        } else {
          smt.OperatorApplication(smt.ImplicationOp, List(pathCondExpr, assumpExpr))
        }
        addAssumption(effectiveExpr, List.empty)
        return symbolTable
      case HavocStmt(h) =>
        h match {
          case HavocableId(id) =>
            UclidMain.printVerbose("------New Havoc Symbol------!")
            return symbolTable.updated(id, newHavocSymbol(id.name, smt.Converter.typeToSMT(scope.typeOf(id).get)))
          case HavocableNextId(id) =>
            throw new Utils.AssertionError("HavocableNextIds should have eliminated by now.")
          case HavocableFreshLit(f) =>
            throw new Utils.AssertionError("Fresh literals must have been eliminated by now.")
          case HavocableInstanceId(_) =>
            throw new Utils.AssertionError("Havocable instance ids should have been eliminated by now.")
        }
      case AssignStmt(lhss,rhss) =>
        val es = rhss.map(i => evaluate(i, symbolTable, frameTable, frameNumber, scope));
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

        val simTable1 = simulateStmtList(stmts, localSymbolTable, scope + vars)
        val simTable2 = declaredVars.foldLeft(simTable1)((tbl, p) => tbl - p._1)
        overwrittenSymbols.foldLeft(simTable2)((acc, p) => acc + (p._1 -> p._2))
      case IfElseStmt(e,then_branch,else_branch) =>
        var then_modifies : Set[Identifier] = writeSet(then_branch)
        var else_modifies : Set[Identifier] = writeSet(else_branch)
        // compute in parallel.
        val condExpr = evaluate(e, symbolTable, frameTable, frameNumber, scope)
        val negCondExpr = smt.OperatorApplication(smt.NegationOp, List(condExpr))
        var then_st : SymbolTable = simulateStmt(frameNumber, condExpr :: pathConditions, then_branch, symbolTable, frameTable, scope, label, addAssumption, addAssert)
        var else_st : SymbolTable = simulateStmt(frameNumber, negCondExpr :: pathConditions, else_branch, symbolTable, frameTable, scope, label, addAssumption, addAssert)
        return symbolTable.keys.filter { id => then_modifies.contains(id) || else_modifies.contains(id) }.
          foldLeft(symbolTable){ (acc,id) =>
            acc.updated(id, smt.OperatorApplication(smt.ITEOp, List(condExpr, then_st(id), else_st(id))))
          }
      case ForStmt(_, _, _, _) => throw new Utils.AssertionError("Cannot symbolically execute for loops.")
      case WhileStmt(_, _, _) => throw new Utils.AssertionError("Cannot symbolically execute while loops.")
      case CaseStmt(_) => throw new Utils.AssertionError("Cannot symbolically execute case statement.")
      case ProcedureCallStmt(id,lhss,args,instanceId,moduleId) => throw new Utils.AssertionError("Cannot symbolically execute procedure calls.")
      case ModuleCallStmt(_) => throw new Utils.AssertionError("Cannot symbolically execute module calls.")
      case MacroCallStmt(_) => throw new Utils.AssertionError("Cannot symbolically execute macro calls.") 
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
        case HavocableInstanceId(_) =>
          throw new Utils.AssertionError("Havocable instance ids should have been eliminated by now.")
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
    case ProcedureCallStmt(id,lhss,args,instanceId,moduleId) => {
      throw new Utils.RuntimeError("ProcedureCallStmt must have been inlined by now.")
    }
    case ModuleCallStmt(id) =>
      throw new Utils.RuntimeError("ModuleCallStmt must have been inlined by now.")
    case MacroCallStmt(id) =>
      throw new Utils.RuntimeError("MacroCallStmt must have been inlined by now")
  }
  def writeSets(stmts: List[Statement]) : Set[Identifier] = {
    return stmts.foldLeft(Set.empty[Identifier]){(acc,s) => acc ++ writeSet(s)}
  }

  def substitute(e: Expr, id: Identifier, arg: Expr) : Expr = {
     e match {
       case OperatorApplication(ArraySelect(inds), es) =>
         val indsP = inds.map(ind => substitute(ind, id, arg))
         val esP = es.map(e => substitute(e, id, arg))
         OperatorApplication(ArraySelect(indsP), esP)
       case OperatorApplication(ArrayUpdate(inds, value), es) =>
         val indsP = inds.map(ind => substitute(ind, id, arg))
         val esP = es.map(e => substitute(e, id, arg))
         val valueP = substitute(value, id, arg)
         OperatorApplication(ArrayUpdate(indsP, valueP), esP)
       case OperatorApplication(op,args) =>
         OperatorApplication(op, args.map(x => substitute(x, id, arg)))
       case FuncApplication(f,args) =>
         FuncApplication(substitute(f,id,arg), args.map(x => substitute(x,id,arg)))
       case Lambda(idtypes, le) =>
         Utils.assert(idtypes.exists(x => x._1.name == id.name), "Lambda arguments of the same name")
         Lambda(idtypes, substitute(le, id, arg))
       case IntLit(n) => e
       case BoolLit(b) => e
       case Identifier(i) => (if (id.name == i) arg else e)
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
       case smt.SynthSymbol(id,typ, _, _, _) => return (if (id == s.id) arg else e)
       case smt.OracleSymbol(id,typ, _) => return (if (id == s.id) arg else e)
       case _ => throw new Utils.UnimplementedException("Should not get here")
     }
  }

  def evaluate(e: Expr, symbolTable: SymbolTable, frameTable : FrameTable, frameNumber : Int, scope : Scope) : smt.Expr = {
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
            if (frameNumber - past < 0) {
              newHavocSymbol(id.name, smtType)
            } else {
              frameTable(frameNumber - past).get(id) match {
                case Some(expr) => expr
                case None => //UclidMain.println("--------New Havoc Symbol!------ Past = " + past.toString)
                  newHavocSymbol(id.name, smtType)
  
              }
            }
        }
      }
    }
    smt.Converter.exprToSMT(e, idToSMT, scope)
  }
}
