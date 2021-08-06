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
 * Authors: Federico Mora
 *
 * File-based synthesis interface.
 *
 */

package uclid
package smt

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}
import com.typesafe.scalalogging.Logger

class SynthLibInterface(args: List[String], sygusSyntax : Boolean) extends SMTLIB2Interface(args) {
  val synthliblogger = Logger(classOf[SynthLibInterface])

  var astack   : List[List[String]] = List.empty
  var total   : List[String] = List.empty
  var out     : String = ""

  var defineDecls : String = ""
  type DefinesSet = MutableSet[DefineSymbol]
  var addedDefines : DefinesSet = MutableSet.empty

  type SynthVarSet = MutableSet[SynthSymbol]
  var synthVariables : SynthVarSet = MutableSet.empty

  override def generateDeclaration(sym: Symbol) = {
    val (typeName, newTypes) = generateDatatype(sym.typ)
    Utils.assert(newTypes.size == 0, "No new types are expected here.")
    
    var inputTypes = ""
    var cmd = ""

    if (sygusSyntax) {
      if(sym.typ.isInstanceOf[MapType])
      {
        inputTypes = "-> " + generateInputDataTypes(sym.typ).mkString(" ")
        cmd = "(declare-var %s (%s %s ))\n".format(sym, inputTypes, typeName)
      }
      else
      {
        inputTypes = generateInputDataTypes(sym.typ).mkString(" ")
        cmd = "(declare-var %s %s %s )\n".format(sym, inputTypes, typeName)
      }
    } else {
      inputTypes = generateInputDataTypes(sym.typ).mkString(" ")
      cmd = "(declare-fun %s (%s) %s)\n".format(sym, inputTypes, typeName)
    }
    out += cmd
  }

  def generateGrammarDeclaration(grammarSymbol: smt.GrammarSymbol): String = {
    grammarSymbol.nts.foreach {
      (nt) => nt.terms.foreach {
        (trm) => {
          trm.e match {
            case DefineApplication(e, defDecl, args) => generateDefines(defDecl)
            case _ => None
          }
        }
      }
    }
    grammarSymbol.toString
  }

  def generateSynthDeclaration(sym: SynthSymbol) = {
    val (typeName, newTypes) = generateDatatype(sym.typ)
    Utils.assert(newTypes.size == 0, "No new types are expected here.")

    val inputTypes = generateInputDataTypes(sym.typ)
    val inputNames = sym.symbolTyp.args.map( a => a._1.toString())
    val sig =  (inputNames zip inputTypes).map(a => "(" + a._1 + " " + a._2 + ")").mkString(" ")
    var cmd = ""

    if (sygusSyntax) {
      val grammar = sym.grammar.fold("")(generateGrammarDeclaration _)
      cmd = "(synth-fun %s (%s) %s %s)\n".format(sym, sig, typeName, grammar)
    } else {
      cmd = "(synth-blocking-fun %s (%s) %s)\n".format(sym, sig, typeName)
    }
    out += cmd
  }

  def generateDefines(sym: DefineSymbol) = {
    val (typeName, newTypes) = generateDatatype(sym.typ)
    Utils.assert(newTypes.size == 0, "No new types are expected here.")
    val inputTypes = generateInputDataTypes(sym.typ)
    val inputNames = sym.symbolTyp.args.map( a => a._1.toString())
    val sig =  (inputNames zip inputTypes).map(a => "(" + a._1 + " " + a._2 
    + ")").mkString(" ")

    var cmd : String = ""
    if (sygusSyntax) {
      if (!addedDefines.contains(sym))  
      {
        cmd = "(define-fun %s (%s) %s %s)\n".format(sym, sig, typeName, sym.expr)
        defineDecls += cmd
      }
    }
  }

  /**
   *  Helper function that finds the list of all SynthSymbols in an expression.
   */
  def findSynthSymbols(e : Expr) : Set[SynthSymbol] = {
    def symbolFinder(e : Expr) : Set[SynthSymbol] = {
      e match {
        case sym : SynthSymbol => Set(sym)
        case _ => Set.empty[SynthSymbol]
      }
    }
    Context.accumulateOverExpr(e, symbolFinder _, MutableMap.empty)
  }

  override def assert (e: Expr) {
    val symbols = Context.findSymbols(e)
    val symbolsP = symbols.filter(s => !variables.contains(s))
    symbolsP.foreach {
      (s) => {
        variables += s
        generateDeclaration(s)
      }
    }

    val synthSymbols = findSynthSymbols(e)
    val synthSymbolsP = synthSymbols.filter(s => !synthVariables.contains(s))
    synthSymbolsP.foreach {
      (s) => {
        synthVariables += s
        generateSynthDeclaration(s)
      }
    }

    synthliblogger.debug("[begin translate]")
    val smtlib2 = translateExpr(e, false)
    synthliblogger.debug("assert: {}", smtlib2)
    astack = (smtlib2 :: astack.head) :: astack.tail
  }

  override def check(produceModel: Boolean = true) : SolverResult = {
    synthliblogger.debug("check")
    // put in all the assertions as a conjunction
    total = "(and " + astack.foldLeft(""){ (acc, s) => acc + " " + s.mkString(" ")} + ")" :: total
    counten += 1
    return SolverResult(None, None)
  }

  override def checkSynth() : SolverResult = {
    val query = toString()
    UclidMain.printStats(f"Starting solver")
    val start = System.nanoTime()
    writeCommand(query)
    val delta =  (System.nanoTime() - start) / 1000000.0
    UclidMain.printStats(f"Solving took $delta%.1f ms")
    val ans = {
      readResponse() match {
        case Some(strP) =>
          val str = strP.stripLineEnd
          if (str.contains("unsat") || str.startsWith("(")) {
             SolverResult(Some(true), getModel(str))
          } else if (str.contains("sat") || str.contains("unknown")){
            UclidMain.printResult(str);
            SolverResult(Some(false), None)
          } else {
            throw new Utils.AssertionError("Unexpected result from SMT solver: " + str.toString())
          }
        case None =>
          throw new Utils.AssertionError("Unexpected EOF result from SMT solver.")
      }
    }
    solverProcess.finishInput()
    ans
  }

  override def getModel() : Option[Model] = {
    None
  }

  def getModel(str : String) : Option[Model] = {
    UclidMain.printStatus(str)
    None
  }

  override def finish() {
    solverProcess.finishInput()
    Thread.sleep(5)
    solverProcess.kill()
  }

  override def push() {
    synthliblogger.debug("push")
    astack = List.empty :: astack
  }

  override def pop() {
    synthliblogger.debug("pop")
    astack = astack.tail
  }

  override def toString() : String = {
    val aexp = "(or " + total.mkString("\t\n") + ")"
    val query = if (sygusSyntax) {
      synthDeclCommands + "\n" + defineDecls + "\n" + out + "(constraint (not " + aexp +"))\n(check-synth)\n"
    } else {
      out + "(assert " + aexp +")\n(check-sat)\n"
    }
    "(set-logic ALL)\n" + query
  }
}
