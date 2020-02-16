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

trait SMTLIB2Base {
  val smtlib2BaseLogger = Logger(classOf[SMTLIB2Base])
  
  type VarMap = MutableMap[String, Symbol]
  type LetMap = MutableMap[Expr, String]
  var variables : VarMap = MutableMap.empty
  var letVariables : LetMap = MutableMap.empty
  var enumLiterals : MutableSet[EnumLit] = MutableSet.empty
  var stack : List[(VarMap, LetMap, MutableSet[EnumLit])] = List.empty
  var typeMap : SynonymMap = SynonymMap.empty

  var counterId = 0
  def getTypeName(suffix: String) : String = {
    counterId += 1
    "_type_" + suffix + "_" + counterId.toString() + "_"
  }
  def getVariableName(v: String) : String = {
//    counterId += 1
 //   "_var_" + v + counterId.toString() + "_"
  v
  }
  def getLetVariableName() : String = {
    counterId += 1
    "_let_" + counterId.toString() + "_"
  }
  def generateInputDataTypes(t : Type) : (List[String]) = {
    t match {
      case MapType(inputTyp, outputType) =>
        inputTyp.foldRight(List.empty[String]) {
          (typ, acc) => {
            acc :+ generateDatatype(typ)._1;
          }
        }
      case _ =>
        List.empty[String]
    }
  }
  def generateDatatype(t : Type) : (String, List[String]) = {
    smtlib2BaseLogger.debug("generateDatatype: {}", t.toString())
    val (resultName, newTypes) = typeMap.get(t) match {
      case Some(synTyp) =>
        (synTyp.name, List.empty)
      case None =>
        t match {
          case EnumType(members) =>
            val typeName = getTypeName(t.typeNamePrefix)
            val memStr = Utils.join(members.map(s => "(" + s + ")"), " ")
            val declDatatype = "(declare-datatype %s (%s))".format(typeName, memStr)
            typeMap = typeMap.addSynonym(typeName, t)
            (typeName, List(declDatatype))
          case ArrayType(indexTypes, elementType) =>
            val (indexTypeName, newTypes1) = if (indexTypes.size == 1) {
              generateDatatype(indexTypes(0))
            } else {
              val indexTuple = TupleType(indexTypes)
              generateDatatype(indexTuple)
            }
            val (elementTypeName, newTypes2) = generateDatatype(elementType)
            val arrayTypeName = "(Array %s %s)".format(indexTypeName, elementTypeName)
            typeMap = typeMap.addSynonym(arrayTypeName, t)
            (arrayTypeName, newTypes1 ++ newTypes2)
          case productType : ProductType =>
            val typeName = getTypeName(t.typeNamePrefix)
            val mkTupleFn = Context.getMkTupleFunction(typeName)
            val fieldNames = productType.fieldNames.map(f => Context.getFieldName(f))
            val (fieldTypes, newTypes1) = productType.fieldTypes.foldRight(List.empty[String], List.empty[String]) {
              (fld, acc) => {
                val (fldNameI, newTypesI) = generateDatatype(fld)
                (fldNameI :: acc._1, newTypesI ++ acc._2)
              }
            }
            val fieldString = (fieldNames zip fieldTypes).map(p => "(%s %s)".format(p._1.toString(), p._2.toString()))
            val nameString = "((%s 0))".format(typeName)
            val argString = "(" + Utils.join(mkTupleFn :: fieldString, " ") + ")"
            val newType = "(declare-datatypes %s ((%s %s)))".format(nameString, typeName, argString)
            typeMap = typeMap.addSynonym(typeName, t)
            (typeName, newType :: newTypes1)
          case BoolType => 
            typeMap = typeMap.addSynonym("Bool", t)
            ("Bool", List.empty)
          case IntType =>
            typeMap = typeMap.addSynonym("Int", t)
            ("Int", List.empty)
          case BitVectorType(n) => 
            val typeStr = "(_ BitVec %d)".format(n)
            typeMap = typeMap.addSynonym(typeStr, t)
            (typeStr, List.empty)
          case MapType(inTypes, outType) =>
            val typeStr = generateDatatype(outType)._1
            val inputTypeStrs = inTypes.foldRight(List.empty[String]) {
              (typ, acc) => {
                acc :+ generateDatatype(typ)._1;
              }
            }
            (typeStr, List.empty)
          case UninterpretedType(typeName) => 
            // TODO: sorts with arity greater than 1? Does uclid allow such a thing?
            val declDatatype = "(declare-sort %s)".format(typeName)
            typeMap = typeMap.addSynonym(typeName, t)
            (typeName, List(declDatatype))
          case _ => 
            throw new Utils.UnimplementedException("TODO: Implement more types in SMTLIB2Interface.generateDatatype: " + t.toString());
        }
    }
    (resultName, newTypes)
  }

  case class TranslatedExpr(order : Int, expr : String, name : Option[String]) {
    def exprString() : String = {
      name match {
        case Some(str) => str
        case None => expr
      }
    }
  }
  type ExprMap = Map[Expr, TranslatedExpr]

  def exprString(trExprs : List[TranslatedExpr]) = {
    Utils.join(trExprs.map(tr => tr.exprString()), " ")
  }
  def translateOptionalTuple(index: List[Expr], memoIn : ExprMap, shouldLetify : Boolean) : (TranslatedExpr, ExprMap) = {
    if (index.size > 1) { translateExpr(MakeTuple(index), memoIn, shouldLetify) }
    else { translateExpr(index(0), memoIn, shouldLetify) }
  }
  def translateExprs(es : List[Expr], memoIn : ExprMap, shouldLetify : Boolean) : (List[TranslatedExpr], ExprMap) = {
    smtlib2BaseLogger.info("-> start translateExprs <-")
    val s = es.foldRight((List.empty[TranslatedExpr], memoIn)){ 
      (arg, acc) => {
        val (tExpr, accP) = translateExpr(arg, acc._2, shouldLetify)
        (tExpr :: acc._1, accP)
      }
    }
    smtlib2BaseLogger.info("-> end translateExprs <-")
    s
  }
  def translateExpr(eIn: Expr, memo : ExprMap, shouldLetify : Boolean) : (TranslatedExpr, ExprMap) = {
    val t1 = System.nanoTime().toDouble
    val memoLookup = memo.get(eIn)
    // UclidMain.println(eIn.toString().slice(0,5))
    val t2 = System.nanoTime().toDouble
    smtlib2BaseLogger.info("-->> finish LOOKUP: {}", (t2 - t1) / 1e9)
    val (resultExpr, resultMemo) = memoLookup match {
      case Some(resultExpr) => (resultExpr, memo)
      case None =>
        val (exprStr, memoP, letify) : (String, ExprMap, Boolean) = Context.rewriteBVReplace(eIn) match {
          case Symbol(id,_) =>
            smtlib2BaseLogger.info("-->> symbol <<-- {}", id)
            // Utils.assert(variables.contains(id), "Not found in map: " + id)
            if (variables.contains(id)) {
              (variables.get(id).get.toString, memo, false)
            } else {
              // Quantified variable.
              // TODO be able to check this.
              (id, memo, false)
            }
          case EnumLit(id, _) =>
            smtlib2BaseLogger.info("-->> enum <<--")
            (id, memo, false)
          case ConstArray(expr, typ) =>
            val (eP, memoP) = translateExpr(expr, memo, shouldLetify)
            val (typName, newTypes) = generateDatatype(typ)
            assert (newTypes.size == 0)
            val str = "((as const %s) %s)".format(typName, eP.exprString())
            (str, memoP, shouldLetify)
          case OperatorApplication(op,operands) =>
            smtlib2BaseLogger.info("-->> opapp <<--")
            val (ops, memoP) = translateExprs(operands, memo, shouldLetify)
            ("(" + op.toString() + " " + exprString(ops) + ")", memoP, shouldLetify)
          case ArraySelectOperation(e, index) =>
            smtlib2BaseLogger.info("-->> arraysel <<--")
            val (trArray, memoP1) = translateExpr(e, memo, shouldLetify)
            val (trIndex, memoP2) = translateOptionalTuple(index, memoP1, shouldLetify)
            ("(select " + trArray.exprString() + " " + trIndex.exprString() + ")", memoP2, shouldLetify)
          case ArrayStoreOperation(e, index, value) =>
            smtlib2BaseLogger.info("-->> arraystore <<--")
            val (trArray, memoP1) = translateExpr(e, memo, shouldLetify)
            val (trIndex, memoP2) = translateOptionalTuple(index, memoP1, shouldLetify)
            val (trValue, memoP3) = translateExpr(value, memoP2, shouldLetify)
            ("(store " + trArray.exprString() + " " + trIndex.exprString() + " " + trValue.exprString() +")", memoP3, true)
          case FunctionApplication(e, args) =>
            smtlib2BaseLogger.info("-->> fapp <<--")
            Utils.assert(e.isInstanceOf[Symbol], "Beta substitution has not happened.")
            val (trFunc, memoP1) = translateExpr(e, memo, shouldLetify)
            val (trArgs, memoP2) = translateExprs(args, memoP1, shouldLetify)
            if (args.length == 0) {
              (trFunc.exprString(), memoP2, false)
            } else {
              ("(" + trFunc.exprString() + " " + exprString(trArgs) + ")", memoP2, true)
            }
          case MakeTuple(args) =>
            smtlib2BaseLogger.info("-->> tup <<--")
            val tupleType = TupleType(args.map(_.typ))
            val (tupleTypeName, newTypes) = generateDatatype(tupleType)
            val (trArgs, memoP1) = translateExprs(args, memo, shouldLetify)
            ("(" + Context.getMkTupleFunction(tupleTypeName) + " " + exprString(trArgs) + ")", memoP1, true)
          case Lambda(_,_) =>
            smtlib2BaseLogger.info("-->> lambda <<--")
            throw new Utils.AssertionError("Lambdas in should have been beta-reduced by now.")
          case IntLit(value) =>
            smtlib2BaseLogger.info("-->> intlit <<--")
            (value.toString(), memo, false)
          case BitVectorLit(value, width) =>
            smtlib2BaseLogger.info("-->> bvlit <<--")
            ("(_ bv" + value.toString() + " " + width.toString() + ")", memo, false)
          case BooleanLit(value) =>
            smtlib2BaseLogger.info("-->> boollit <<--")
            (value match { case true => "true"; case false => "false" }, memo, false)
        }
        val translatedExpr = if (/*letify && shouldLetify*/false) {
          TranslatedExpr(memoP.size, exprStr, Some(getLetVariableName()))
        } else {
          TranslatedExpr(memoP.size, exprStr, None)
        }
        (translatedExpr, memoP + (eIn -> translatedExpr))
    }
    (resultExpr, resultMemo)
  }
  def translateExpr(e : Expr, shouldLetify : Boolean) : String = {
    val (trExpr, memoP) = translateExpr(e, Map.empty, shouldLetify)
    val resultString = if (/*shouldLetify*/false) {
      if (memoP.size == 0) {
        trExpr.exprString()
      } else {
        val letExprsIn = memoP.filter(p => p._2.name.isDefined).map(p => (p._2.order, p._2.name.get, p._2.expr)).toList
        val letExprsSorted = letExprsIn.sortWith((p1, p2) => p1._1 < p2._1).map(p => (p._2, p._3))
        def recurse(lets : List[(String, String)], expr : String) : List[String] = {
          lets match {
            case Nil => List(expr)
            case hd :: tl =>
              val aString : String = "(let ((" + hd._1 + " " + hd._2 + ")) "
              val bString : List[String] = recurse(tl, expr)
              val cString : List[String] = List(")")
              (aString :: bString) ++ cString
          }
        }
        val strings : List[String] = recurse(letExprsSorted, trExpr.exprString())
        val rString = (strings.foldLeft(new StringBuilder())((acc, s) => acc ++= s)).toString()
        rString
      }
    } else {
      trExpr.expr
    }
    smtlib2BaseLogger.info("RESULT size [2]: {}", resultString.size)
    resultString
  }
}

class SMTLIB2Model(stringModel : String) extends Model {
  val model =  SExprParser.parseModel(stringModel)

  override def evaluate(e : Expr) : Expr = {
    throw new Utils.UnimplementedException("evaluate not implemented yet.")
  }

  override def evalAsString(e : Expr)  : String = {
    var definitions = model.functions.filter(fun => fun.asInstanceOf[DefineFun].id.toString() contains e.toString())
    Utils.assert(definitions.size < 2, "More than one definition found!")
    definitions.size match {
      case 0 =>
        e.toString()
      case 1 =>
        definitions(0).asInstanceOf[DefineFun].e.toString()
      case _ =>
        throw new Utils.RuntimeError("Found more than one definition in the assignment model!")
    }

  }

  override def toString() : String = {
    model.toString()
  }
}

class SMTLIB2Interface(args: List[String]) extends Context with SMTLIB2Base {
  val smtlibInterfaceLogger = Logger(classOf[SMTLIB2Interface])

  type NameProviderFn = (String, Option[String]) => String
  var expressions : List[Expr] = List.empty
  val solverProcess = new InteractiveProcess(args, true)

  def generateDeclaration(sym: Symbol) = {
    val (typeName, newTypes) = generateDatatype(sym.typ)
    Utils.assert(newTypes.size == 0, "No new types are expected here.")
    val inputTypes = generateInputDataTypes(sym.typ).mkString(" ")
    val cmd = "(declare-fun %s (%s) %s)".format(sym, inputTypes, typeName)
    writeCommand(cmd)
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
        val sym = Symbol(getVariableName(s.id), s.symbolTyp)
        variables += (s.id -> sym)
        generateDeclaration(sym)
      }
    }
    val smtlib2 = translateExpr(e, true)
    smtlibInterfaceLogger.debug("assert: {}", smtlib2)
    writeCommand("(assert " + smtlib2 +")")
  }

  override def preassert(e: Expr) {
    var declCommands = new ListBuffer[String]()
    Context.findTypes(e).filter(typ => !typeMap.contains(typ)).foreach {
      newType => {
        val (typeName, newTypes) = generateDatatype(newType)
        newTypes.foreach(typ => declCommands.append(typ))
      }
    }
    
    // This is a bit of a hack: sometimes types depend on each other and the order
    // of declaration matters. The examples that gave us trouble are cases where a
    // record depends on an enum, but the enum is declared after. The smt-lib
    // declarations for these cases are "declare-datatypes" and
    // "declare-datatype", respectively. Sorting the type declarations by
    // alphabetical order will circumvent these problems without adding
    // declaration dependency tracking. (Before this we were printing in a random
    // order given by how scala's set type enumerates)

    declCommands.sorted.foreach(decl => writeCommand(decl))
  }

  override def check() : SolverResult = {
    smtlibInterfaceLogger.debug("check")
    Utils.assert(solverProcess.isAlive(), "Solver process is not alive!")
    writeCommand("(check-sat)")
    if (filePrefix == "") {
      readResponse() match {
        case Some(strP) =>
          val str = strP.stripLineEnd
          str match {
            case "sat" => SolverResult(Some(true), getModel())
            case "unsat" => SolverResult(Some(false), None)
            case _ =>
              throw new Utils.AssertionError("Unexpected result from SMT solver: " + str.toString())
          }
        case None =>
          throw new Utils.AssertionError("Unexpected EOF result from SMT solver.")
      }
    } else {
      val smtOutput = solverProcess.toString()
      Utils.writeToFile(f"$filePrefix%s-$curAssertName%s-$curAssertLabel%s-$counten%04d.smt", smtOutput + "\n(get-info :all-statistics)\n")
      counten += 1
      return SolverResult(None, None)
    }
  }

  def getModel() : Option[Model] = {
    Utils.assert(solverProcess.isAlive(), "Solver process is not alive! Cannot retrieve model.")
    writeCommand("(get-model)")
    readResponse() match {
      case Some(strModel) =>
        smtlibInterfaceLogger.debug("model: {}", strModel)
        val str = strModel.stripLineEnd
        val Pattern = "(?s)(.*model.*)".r
        str match {
          case Pattern(_) =>
            Some(new SMTLIB2Model(str))
          case _ =>
            None
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
    smtlibInterfaceLogger.debug("push")
    val e : (VarMap, LetMap, MutableSet[EnumLit]) = (variables.clone(), letVariables.clone(), enumLiterals.clone())
    stack = e :: stack
    writeCommand("(push 1)")
  }

  override def pop() {
    smtlibInterfaceLogger.debug("pop")
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

  override def addOption(opt : String, value : Context.SolverOption) = {
    // TODO: add the implementation here.
  }
}
