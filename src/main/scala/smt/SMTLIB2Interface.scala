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

import uclid.Utils

import scala.collection.mutable.{Map => MutableMap}

import scala.language.postfixOps

class SMTLIB2Interface(args: List[String]) extends Context {
  var typeMap : SynonymMap = SynonymMap.empty
  var sorts : MutableMap[String, Type] = MutableMap.empty
  var variables : MutableMap[String, Type] = MutableMap.empty

  type NameProviderFn = (String, Option[String]) => String
  var expressions : List[Expr] = List.empty
  val solverProcess = new InteractiveProcess(args)

  def generateDeclaration(x: Symbol) : String = {
    def printType(t: Type) : String = {
      t match {
        case BoolType => "Bool"
        case IntType => "Int"
        case MapType(ins,out) =>
          "(" + ins.foldLeft(""){(acc,i) =>
            acc + " " + printType(i)} + ") " + printType(out)
        case ArrayType(ins,out) =>
          if (ins.size > 1) {
            "(Array " + ins.foldLeft("(MyTuple" + ins.size){(acc,i) =>
              acc + " " + printType(i)} + ") " + printType(out) + ")"
          } else {
            "(Array " + printType(ins(0)) + " " + printType(out) + ")"
          }
        case _ =>
          // FIXME: add more types here.
          throw new Utils.UnimplementedException("Add support for more types: " + x.toString())
      }
    }

    return x.typ match {
      case BoolType => "(declare-const %s Bool)".format(x.id)
      case IntType => "(declare-const %s Int)".format(x.id)
      case BitVectorType(n) => "(declare-const %s (_ BitVec %d))".format(x.id, n)
      case SynonymType(s, typ) => "(declare-const %s %s)".format(x.id, s)
      case _ =>
        // FIXME: add more types here.
        throw new Utils.UnimplementedException("Add support for more types: " + x.typ.toString())
    }
  }

  def generateDatatype(p : (String, Type)) : Option[String] = {
    p._2 match {
      case BoolType | IntType => None
      case EnumType(members) =>
        val memStr = Utils.join(members.map(s => "(" + s + ")"), " ")
        val declDatatype = "(declare-datatypes ((%s 0)) ((%s %s)))".format(p._1, p._1, memStr)
        //val declMembers = members.map(m => "(declare-fun %s () %s)".format(m, p._1))
        //val str = Utils.join(declDatatype :: declMembers, "\n")
        Some(declDatatype)
      case _ => throw new Utils.UnimplementedException("TODO: Implement more types in Z3FileInterface.generateDatatype")
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
      case OperatorApplication(op,operands) => e.toString
      case ArraySelectOperation(e, index) =>
        "(select " + translateExpr(e) + " " + mkTuple(index) + ")"
      case ArrayStoreOperation(e, index, value) =>
        "(store " + translateExpr(e) + " " + mkTuple(index) + " " + translateExpr(value) + ")"
      case FunctionApplication(e, args) =>
        Utils.assert(e.isInstanceOf[Symbol], "Did beta substitution happen?")
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
    val (eP, typeMapP) = flattenTypes(e, typeMap)
    val newTypes = typeMapP.fwdMap.filter(p => !sorts.contains(p._1))
    newTypes.foreach {
      (n) => {
        sorts += (n._1 -> n._2)
        generateDatatype(n) match {
          case Some(s) => writeCommand(s)
          case None =>
        }
      }
    }
    typeMap = typeMapP
    val symbolsP = Context.findSymbols(eP)
    val newSymbols = symbolsP.filter(s => !variables.contains(s.id))
    newSymbols.foreach {
      (s) => {
        variables += (s.id -> s.symbolTyp)
        val decl = generateDeclaration(s)
        writeCommand(decl)
      }
    }
    writeCommand("(assert " + translateExpr(eP) +")")
  }

  override def check() : SolverResult = {
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
