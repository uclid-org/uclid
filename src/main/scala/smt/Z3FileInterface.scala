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
 *
 * File-based SMT solver (Z3) interface.
 *
 */

package uclid
package smt

import uclid.Utils

import scala.collection.mutable.{Map => MutableMap}

import scala.language.postfixOps

class Z3FileInterface() extends Context {
  var typeMap : SynonymMap = SynonymMap.empty
  var sorts : MutableMap[String, Type] = MutableMap.empty
  var variables : MutableMap[String, Type] = MutableMap.empty

  type NameProviderFn = (String, Option[String]) => String
  var expressions : List[Expr] = List.empty
  val z3Process = new InteractiveProcess("/usr/bin/z3", List("-smt2", "-in"))

  def generateDeclaration(x: Symbol) : String = {
    def printType(t: Type) : String = {
      t match {
        case BoolType() => "Bool"
        case IntType() => "Int"
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
      case BoolType() => "(declare-const %s Int)".format(x.id)
      case IntType() => "(declare-const %s Bool)".format(x.id)
      case BitVectorType(n) => "(declare-const %s (_ BitVec %d))".format(x.id, n)
      case MapType(ins,out) =>
        "(declare-fun " + x.id + " " + printType(x.typ) + ")"
      case ArrayType(ins,out) =>
        "(declare-const " + x.id + " " + printType(x.typ) + ")"
      case _ =>
        // FIXME: add more types here.
        throw new Utils.UnimplementedException("Add support for more types: " + x.typ.toString())
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
        Utils.assert(e.isInstanceOf[Symbol], "Did beta sub happen?")
        "(" + translateExpr(e) +
          args.foldLeft(""){(acc,i) =>
            acc + " " + translateExpr(i)} + ")"
      case Lambda(_,_) =>
        throw new Exception("yo lambdas in assertions should have been beta-reduced")
      case IntLit(value) => value.toString()
      case BitVectorLit(_,_) =>
        throw new Utils.UnimplementedException("Bitvectors unimplemented")
      case BooleanLit(value) =>
        value match { case true => "true"; case false => "false" }
    }
  }

  def writeCommand(str : String) {
    println(str)
    z3Process.writeInput(str + "\n")
  }

  def readResponse() : Option[String] = {
    val msg = z3Process.readOutput()    
    msg
  }

  override def assert (e: Expr) {
    val (eP, typeMapP) = flattenTypes(e, typeMap)
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
    z3Process.finishInput()
    Thread.sleep(5)
    z3Process.kill()
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