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
import scala.collection.mutable.ListBuffer
import com.typesafe.scalalogging.Logger
import scala.language.postfixOps

class SMTLIB2Interface(args: List[String]) extends Context {
  type VarMap = MutableMap[String, (String, Type)]
  type LetMap = MutableMap[Expr, String]
  val logger = Logger(classOf[SMTLIB2Interface])

  var typeMap : SynonymMap = SynonymMap.empty
  var variables : VarMap = MutableMap.empty
  var letVariables : LetMap = MutableMap.empty
  var enumLiterals : MutableSet[EnumLit] = MutableSet.empty
  var stack : List[(VarMap, LetMap, MutableSet[EnumLit])] = List.empty

  type NameProviderFn = (String, Option[String]) => String
  var expressions : List[Expr] = List.empty
  val solverProcess = new InteractiveProcess(args)

  var counterId = 0
  def getTypeName(suffix: String) : String = {
    counterId += 1
    "_type_" + suffix + "_" + counterId.toString() + "_"
  }
  def getVariableName(v: String) : String = {
    counterId += 1
    "_var_" + v + counterId.toString() + "_"
  }
  def getLetVariableName(v: String) : String = {
    counterId += 1
    "_let_" + v + counterId.toString() + "_"
  }

  def generateDeclaration(name: String, t: Type) = {
    val typeName = generateDatatype(t)
    val cmd = "(declare-const %s %s)".format(name, typeName)
    writeCommand(cmd)
  }

  def generateDatatype(t : Type) : String = {
    logger.debug("generateDatatype: {}", t.toString())
    typeMap.get(t) match {
      case Some(synTyp) =>
        synTyp.name
      case None =>
        t match {
          case EnumType(members) =>
            val typeName = getTypeName(t.typeNamePrefix)
            val memStr = Utils.join(members.map(s => "(" + s + ")"), " ")
            val declDatatype = "(declare-datatype %s (%s))".format(typeName, memStr)
            typeMap = typeMap.addSynonym(typeName, t)
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
            val arrayTypeName = "(Array %s %s)".format(indexTypeName, elementTypeName)
            typeMap = typeMap.addSynonym(arrayTypeName, t)
            arrayTypeName
          case productType : ProductType =>
            val typeName = getTypeName(t.typeNamePrefix)
            val mkTupleFn = Context.getMkTupleFunction(typeName)
            val fieldNames = productType.fieldNames.map(f => Context.getFieldName(f))
            val fieldTypes = productType.fieldTypes.map(generateDatatype(_))
            val fieldString = (fieldNames zip fieldTypes).map(p => "(%s %s)".format(p._1.toString(), p._2.toString()))
            val nameString = "((%s 0))".format(typeName)
            val argString = "(" + Utils.join(mkTupleFn :: fieldString, " ") + ")"
            writeCommand("(declare-datatypes %s ((%s %s)))".format(nameString, typeName, argString))
            typeMap = typeMap.addSynonym(typeName, t)
            typeName
          case BoolType => 
            typeMap = typeMap.addSynonym("Bool", t)
            "Bool"            
          case IntType =>
            typeMap = typeMap.addSynonym("Int", t)
            "Int"
          case BitVectorType(n) => 
            val typeStr = "(_ BitVec %d)".format(n)
            typeMap = typeMap.addSynonym(typeStr, t)
            typeStr
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

  def translateExpr(eIn: Expr) : String = {
    val e = Context.rewriteReplace(eIn)

    def mkTuple(index: List[Expr], stripSizeOne : Boolean) : String = {
      if (index.size > 1 || !stripSizeOne) {
        val tupleType = TupleType(index.map(_.typ))
        val tupleTypeName = generateDatatype(tupleType)
        "(" +
          Context.getMkTupleFunction(tupleTypeName) + " " +
          Utils.join(index.map(_.toString()), " ") +
        ")"
      }
      else {
        translateExpr(index(0))
      }
    }

    e match {
      case Symbol(id,_) => variables.get(id).get._1
      case EnumLit(id, _) => id
      case OperatorApplication(op,operands) =>
        val ops = operands.map(arg => translateExpr(arg))
        "(" + op.toString() + " " + Utils.join(ops, " ") + ")"
      case ArraySelectOperation(e, index) =>
        "(select " + translateExpr(e) + " " + mkTuple(index, true) + ")"
      case ArrayStoreOperation(e, index, value) =>
        "(store " + translateExpr(e) + " " + mkTuple(index, true) + " " + translateExpr(value) + ")"
      case FunctionApplication(e, args) =>
        Utils.assert(e.isInstanceOf[Symbol], "Beta substitution has not happened.")
        "(" + translateExpr(e) +
          args.foldLeft(""){(acc,i) =>
            acc + " " + translateExpr(i)} + ")"
      case MakeTuple(args) =>
        mkTuple(args, false)
      case Lambda(_,_) =>
        throw new Utils.AssertionError("Lambdas in should have been beta-reduced by now.")
      case IntLit(value) => value.toString()
      case BitVectorLit(value, width) =>
        "(_ bv" + value.toString() + " " + width.toString() + ")"
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
    val symbols = Context.findSymbols(e)
    val symbolsP = symbols.filter(s => !variables.contains(s.id))
    symbolsP.foreach {
      (s) => {
        val sIdP = getVariableName(s.id)
        variables += (s.id -> (sIdP, s.symbolTyp))
        generateDeclaration(sIdP, s.symbolTyp)
      }
    }
    writeCommand("(assert " + translateExpr(e) +")")
  }

  override def preassert(e: Expr) {
    logger.debug("preassert")
    val types  = Context.findTypes(e)
    types.filter(typ => !typeMap.contains(typ)).foreach {
      newType => {
        logger.debug("type: {}", newType.toString())
        generateDatatype(newType)
      }
    }
  }

  override def check() : SolverResult = {
    logger.debug("check")
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
    logger.debug("push")
    val e : (VarMap, LetMap, MutableSet[EnumLit]) = (variables.clone(), letVariables.clone(), enumLiterals.clone())
    stack = e :: stack
    writeCommand("(push 1)")
  }

  override def pop() {
    logger.debug("pop")
    val e = stack.head
    variables = e._1
    letVariables = e._2
    enumLiterals = e._3
    stack = stack.tail
    writeCommand("(pop 1)")
  }

  def toSMT2(e : Expr, assumptions : List[Expr], name : String) : String = {
    throw new Utils.UnimplementedException("toSMT2 is not yet implemented.")
  }
}
