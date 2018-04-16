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
 *
 * File-based SMT solver (Z3) interface.
 *
 */

package uclid
package smt

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}
import com.typesafe.scalalogging.Logger

import scala.language.postfixOps

class SMTLIB2Interface(args: List[String]) extends Context {
  val logger = Logger(classOf[SMTLIB2Interface])

  var typeMap : SynonymMap = SynonymMap.empty
  var sorts : MutableMap[String, Type] = MutableMap.empty
  var variables : MutableMap[String, Type] = MutableMap.empty
  var enumLiterals : MutableSet[EnumLit] = MutableSet.empty

  type NameProviderFn = (String, Option[String]) => String
  var expressions : List[Expr] = List.empty
  val solverProcess = new InteractiveProcess(args)

  var typeId = 0
  def getTypeName(suffix: String) : String = {
    typeId += 1
    "type_" + suffix + "_" + typeId.toString()
  }

  def generateDeclaration(x: Symbol) = {
    val typeName = generateDatatype(x.typ)
    val cmd = "(declare-const %s %s)".format(x.id, typeName)
    writeCommand(cmd)
  }

  def generateDatatype(t : Type) : String = {
    typeMap.get(t) match {
      case Some(synTyp) =>
        synTyp.name
      case None =>
        t match {
          case EnumType(members) =>
            val typeName = getTypeName(t.typeNamePrefix)
            val memStr = Utils.join(members.map(s => "(" + s + ")"), " ")
            val declDatatype = "(declare-datatypes ((%s 0)) ((%s)))".format(typeName, memStr)
            typeMap.addSynonym(typeName, t)
            writeCommand(declDatatype)
            typeName
          case ArrayType(indexTypes, elementType) =>
            val indexTypeName = if (indexTypes.size == 1) {
              generateDatatype(indexTypes(0))
            } else {
              val indexTuple = TupleType(indexTypes)
              generateDatatype(indexTuple)
            }
            val elementTypeName = generateDatatype(elementType)
            "(Array %s %s)".format(indexTypeName, elementTypeName)
          case BoolType => "Bool"
          case IntType => "Int"
          case BitVectorType(n) => "(_ BitVec %d)".format(n)
          case _ => 
            throw new Utils.UnimplementedException("TODO: Implement more types in Z3FileInterface.generateDatatype")
        }
    }
  }

  def generateDatatypes(symbols: Set[Symbol]) : String = {
    var arrayArities : Set[Int] = Set.empty;
    symbols.foreach { x =>
      x.typ match {
        case MapType(ins,out) =>
          arrayArities = arrayArities ++ Set(ins.size)
        case ArrayType(ins,out) =>
          arrayArities = arrayArities ++ Set(ins.size)
        case _ => ()
      }
    }

    return arrayArities.foldLeft(""){ (acc,x) =>
      acc + "(declare-datatypes " +
        "(" + ((1 to x).toList).foldLeft("") {
          (acc,i) => acc + " " + "T"+i } + ")" +
        "((MyTuple" + x + " (mk-tuple" + x +
        ((1 to x).toList).foldLeft("") {
            (acc,i) => acc + " (elem"+i+" T"+i+")" } +
        "))))\n"
    }
  }

  def translateExpr(e: Expr) : String = {
    def mkTuple(index: List[Expr]) : String = {
      if (index.size > 1) {
        "(mk-tuple" + index.size + index.foldLeft("")((acc,i) =>
          acc + " " + translateExpr(i)) + ")"
      }
      else {
        translateExpr(index(0))
      }
    }

    e match {
      case Symbol(id,_) => id
      case OperatorApplication(op,operands) =>
        val ops = operands.map(arg => translateExpr(arg))
        "(" + op.toString() + " " + Utils.join(ops, " ") + ")"
      case ArraySelectOperation(e, index) =>
        "(select " + translateExpr(e) + " " + mkTuple(index) + ")"
      case ArrayStoreOperation(e, index, value) =>
        "(store " + translateExpr(e) + " " + mkTuple(index) + " " + translateExpr(value) + ")"
      case FunctionApplication(e, args) =>
        Utils.assert(e.isInstanceOf[Symbol], "Beta has not happened.")
        "(" + translateExpr(e) +
          args.foldLeft(""){(acc,i) =>
            acc + " " + translateExpr(i)} + ")"
      case Lambda(_,_) =>
        throw new Utils.AssertionError("Lambdas in should have been beta-reduced by now.")
      case IntLit(value) => value.toString()
      case BitVectorLit(_,_) =>
        throw new Utils.UnimplementedException("Bitvectors unimplemented")
      case BooleanLit(value) =>
        value match { case true => "true"; case false => "false" }
    }
  }

  def writeCommand(str : String) {
    solverProcess.writeInput(str + "\n")
  }

  def readResponse() : Option[String] = {
    val msg = solverProcess.readOutput()
    msg
  }

  override def assert (e: Expr) {
    val symbols_e = Context.findSymbols(e)
    val symbols_new = symbols_e.filter(s => !variables.contains(s.id))
    val enumLiterals_e = Context.findEnumLits(e)
    val enumLiterals_new = enumLiterals_e.filter(e => !enumLiterals.contains(e))
    val enumTypes_new = enumLiterals_new.filter(p => !typeMap.contains(p.eTyp)).map(p => p.eTyp)
    enumTypes_new.foreach {
      (eTyp) => {
        generateDatatype(eTyp)
      }
    }
    symbols_new.foreach {
      (s) => {
        variables += (s.id -> s.symbolTyp)
        generateDeclaration(s)
      }
    }
    writeCommand("(assert " + translateExpr(e) +")")
  }

  override def check() : SolverResult = {
    Utils.assert(solverProcess.isAlive(), "Solver process is not alive!")
    writeCommand("(check-sat)")
    readResponse() match {
      case Some(strP) =>
        val str = strP.stripLineEnd
        str match {
          case "sat" => SolverResult(Some(true), None)
          case "unsat" => SolverResult(Some(false), None)
          case _ =>
            throw new Utils.AssertionError("Unexpected result from SMT solver: " + str.toString())
        }
      case None =>
        throw new Utils.AssertionError("Unexpected EOF result from SMT solver.")
    }
  }

  override def finish() {
    solverProcess.finishInput()
    Thread.sleep(5)
    solverProcess.kill()
  }

  override def push() {
    writeCommand("(push 1)")
  }

  override def pop() {
    writeCommand("(pop 1)")
  }

  def toSMT2(e : Expr, assumptions : List[Expr], name : String) : String = {
    def assertionToString(e : Expr) : String = "(assert " + translateExpr(e) + ")\n"

    val symbols_e = Context.findSymbols(e)
    val symbols = expressions.foldRight(symbols_e)((ex, s) => s ++ Context.findSymbols(ex))
    val decl = symbols.foldLeft(""){(acc,x) => acc + generateDeclaration(x)}
    val datatypes = generateDatatypes(symbols)
    val assertions = (e :: expressions).foldRight("")((e, str) => assertionToString(e) + str)
    val formula = datatypes + decl + assertions + "\n(check-sat)\n"
    return formula
  }
}
