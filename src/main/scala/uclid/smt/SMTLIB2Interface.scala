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

trait SMTLIB2Base {
  val smtlib2BaseLogger = Logger(classOf[SMTLIB2Base])
  
  type VarSet = MutableSet[Symbol]
  type LetMap = MutableMap[Expr, String]
  type OracleVarSet = MutableSet[OracleSymbol]
  var oracleVariables : OracleVarSet = MutableSet.empty
  var variables : VarSet = MutableSet.empty
  var letVariables : LetMap = MutableMap.empty
  var enumLiterals : MutableSet[EnumLit] = MutableSet.empty
  var stack : List[(VarSet, LetMap, MutableSet[EnumLit])] = List.empty
  var typeMap : SynonymMap = SynonymMap.empty
  var disableLetify : Boolean;


  var counterId = 0
  def getTypeName(suffix: String) : String = {
    counterId += 1
    "_type_" + suffix + "_" + counterId.toString() + "_"
  }
  def getLetVariableName() : String = {
    counterId += 1
    "_let_" + counterId.toString() + "_"
  }
  def generateInputDataTypes(t : Type) : (List[String]) = {
    t match {
      case MapType(inputTyp, _) =>
        inputTyp.foldLeft(List.empty[String]) {
          (acc, typ) => {
            acc :+ generateDatatype(typ)._1;
          }
        }
      case _ =>
        List.empty[String]
    }
  }
  def generateDatatype(t : Type) : (String, List[String]) = {
    smtlib2BaseLogger.debug("generateDatatype: {}; contained = {}", t.toString(), typeMap.contains(t).toString())
    val (resultName, newTypes) = typeMap.get(t) match {
      case Some(synTyp) =>
        (synTyp.name, List.empty)
      case None =>
        t match {
          case EnumType(members) =>
            val typeName = getTypeName(t.typeNamePrefix)
            val memStr = Utils.join(members.map(s => "[" + s + "]"), " ")
            val declDatatype = "(declare-datatype [%s 0] (%s))".format(typeName, memStr)
            typeMap = typeMap.addSynonym(typeName, t)
            // throw new RuntimeException("need a stack trace!")
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
            val typeName = getTypeName(productType.typeNamePrefix)
            val mkTupleFn = Context.getMkTupleFunction(typeName)
            val fieldNames = productType.fieldNames.map(f => Context.getFieldName(f))
            val (fieldTypes, newTypes1) = productType.fieldTypes.foldRight(List.empty[String], List.empty[String]) {
              (fld, acc) => {
                val (fldNameI, newTypesI) = generateDatatype(fld)
                (fldNameI :: acc._1, newTypesI ++ acc._2)
              }
            }
            val fieldString = (fieldNames zip fieldTypes).map(p => "(%s %s)".format(p._1.toString(), p._2.toString()))
            val nameString = "([%s 0])".format(typeName)
            val argString = "[" + Utils.join(mkTupleFn :: fieldString, " ") + "]"
            val newType = "(declare-datatypes %s ((%s)))".format(nameString, argString)
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
          case FltType(e,s) => 
            val typeStr = "(_ FloatingPoint "+ e.toString +" "+ s.toString+")"
            typeMap = typeMap.addSynonym(typeStr, t)
            (typeStr, List.empty)
          case MapType(inTypes, outType) =>
            val (typeStr, newTypes1) = generateDatatype(outType)
            val (_, newTypes) = inTypes.foldRight((List.empty[String], newTypes1)) {
              (typ, acc) => {
                val (typeStr, newTypes2) = generateDatatype(typ)
                (acc._1 :+ typeStr, acc._2 ++ newTypes2)
              }
            }
            (typeStr, newTypes)
          case UninterpretedType(typeName) => 
            // TODO: sorts with arity greater than 1? Does uclid allow such a thing?
            val declDatatype = "(declare-sort %s 0)".format(typeName)
            typeMap = typeMap.addSynonym(typeName, t)
            (typeName, List(declDatatype))
          case _ => 
            throw new Utils.UnimplementedException("TODO: Implement more types in SMTLIB2Interface.generateDatatype: " + t.toString());
        }
    }
    smtlib2BaseLogger.debug("generateDatatype: {}; newTypes: {}", t.toString(), newTypes.toString())
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
  /**
   * Translates an smt operator to its string representation.
   *
   * @param opIn The smt operator to be translated.
   */
  def translateOp(opIn: Operator) : String = {
    opIn match {
      case ForallOp(vs, patterns) =>
        val vsP = vs.map(sym => Symbol(translateExpr(sym, false), sym.typ))
        ForallOp(vsP, patterns).toString()
      case ExistsOp(vs, patterns) =>
        val vsP = vs.map(sym => Symbol(translateExpr(sym, false), sym.typ))
        ExistsOp(vsP, patterns).toString()
      case _ => opIn.toString()
    }
  }
  def translateExprs(es : List[Expr], memoIn : ExprMap, shouldLetify : Boolean) : (List[TranslatedExpr], ExprMap) = {
    es.foldRight((List.empty[TranslatedExpr], memoIn)){ 
      (arg, acc) => {
        val (tExpr, accP) = translateExpr(arg, acc._2, shouldLetify)
        (tExpr :: acc._1, accP)
      }
    }
  }
  def translateExpr(eIn: Expr, memo : ExprMap, shouldLetify : Boolean) : (TranslatedExpr, ExprMap) = {
    val memoLookup = memo.get(eIn)
    val (resultExpr, resultMemo) = memoLookup match {
      case Some(resultExpr) => (resultExpr, memo)
      case None =>
        val (exprStr, memoP, letify) : (String, ExprMap, Boolean) = Context.rewriteBVReplace(eIn) match {
          case Symbol(id,_) =>
            (id, memo, false)
          case SynthSymbol(id,_, _, _, _) =>
            (id, memo, false)
          case OracleSymbol(id,_, _) =>
            (id, memo, false)
          case EnumLit(id, _) =>
            (id, memo, false)
          case ConstArray(expr, typ) =>
            val (eP, memoP) = translateExpr(expr, memo, shouldLetify)
            val (typName, newTypes) = generateDatatype(typ)
            assert (newTypes.size == 0)
            val str = "((as const %s) %s)".format(typName, eP.exprString())
            (str, memoP, shouldLetify)
          case OperatorApplication(RecordUpdateOp(fld), operands) =>
            val productType = operands(0).typ.asInstanceOf[ProductType]
            val typeName = typeMap.get(operands(0).typ).get.name
            val mkTupleFn = Context.getMkTupleFunction(typeName)
            val fieldIndex = productType.fieldIndex(fld)
            val indices = productType.fieldIndices

            var (value, memoP1) = translateExpr(operands(1), memo, shouldLetify)

            val newFields = indices.map{ (i) =>
              if (i == fieldIndex) {
                value.exprString()
              }
              else {
                val sel = OperatorApplication(RecordSelectOp(productType.fieldNames(i)), List(operands(0)))
                val (value, memoP2) = translateExpr(sel, memoP1, shouldLetify)
                memoP1 = memoP2
                value.exprString()
              }
            }.mkString(" ")
            
            ("(" + mkTupleFn + " " + newFields + ")", memoP1, shouldLetify)
          case OperatorApplication(op,operands) =>
            // TODO: Do not letify quantified statements
            // If we decide to letify them, the quantifiers will be to be on the outside
            val (ops, memoP) = translateExprs(operands, memo, shouldLetify && (!op.isInstanceOf[ForallOp] && !op.isInstanceOf[ExistsOp]))
            ("(" + translateOp(op) + " " + exprString(ops) + ")", memoP, shouldLetify)
          case ArraySelectOperation(e, index) =>
            val (trArray, memoP1) = translateExpr(e, memo, shouldLetify)
            val (trIndex, memoP2) = translateOptionalTuple(index, memoP1, shouldLetify)
            ("(select " + trArray.exprString() + " " + trIndex.exprString() + ")", memoP2, shouldLetify)
          case ArrayStoreOperation(e, index, value) =>
            val (trArray, memoP1) = translateExpr(e, memo, shouldLetify)
            val (trIndex, memoP2) = translateOptionalTuple(index, memoP1, shouldLetify)
            val (trValue, memoP3) = translateExpr(value, memoP2, shouldLetify)
            ("(store " + trArray.exprString() + " " + trIndex.exprString() + " " + trValue.exprString() +")", memoP3, true)
          case FunctionApplication(e, args) =>
            smtlib2BaseLogger.info("-->> fapp <<--")
            Utils.assert(e.isInstanceOf[Symbol] || e.isInstanceOf[SynthSymbol] || e.isInstanceOf[OracleSymbol], "Beta substitution has not happened.")
            val (trFunc, memoP1) = translateExpr(e, memo, shouldLetify)
            val (trArgs, memoP2) = translateExprs(args, memoP1, shouldLetify)
            if (args.length == 0) {
              (trFunc.exprString(), memoP2, false)
            } else {
              ("(" + trFunc.exprString() + " " + exprString(trArgs) + ")", memoP2, true)
            }
          case MakeTuple(args) =>
            val tupleType = TupleType(args.map(_.typ))
            val (tupleTypeName, newTypes) = generateDatatype(tupleType)
            assert (newTypes.size == 0)
            val (trArgs, memoP1) = translateExprs(args, memo, shouldLetify)
            ("(" + Context.getMkTupleFunction(tupleTypeName) + " " + exprString(trArgs) + ")", memoP1, true)
          case Lambda(_,_) =>
            throw new Utils.AssertionError("Lambdas in should have been beta-reduced by now.")
          case IntLit(value) =>
            (value.toString(), memo, false)
          case BitVectorLit(value, width) =>
            ("(_ bv" + value.toString() + " " + width.toString() + ")", memo, false)
          case FloatLit(integral,fractional, exp, sig) =>
          {
            if(integral >= 0)
              ("((_ to_fp "+exp.toString+ " "+ sig.toString+ ") roundNearestTiesToEven "+integral.toString() + "." + fractional.toString + ")", memo, false)
            else
              ("((_ to_fp "+exp.toString+ " "+ sig.toString+ ") roundNearestTiesToEven (-"+integral.toString() + "." + fractional.toString + "))", memo, false)
          }
  
          case BooleanLit(value) =>
            (value match { case true => "true"; case false => "false" }, memo, false)
        }
        val translatedExpr = if (letify && shouldLetify & !disableLetify) {
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
    val resultString = if (shouldLetify && !disableLetify) {
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
    val definitions = model.functions.filter(fun => fun.asInstanceOf[DefineFun].id.toString() contains e.toString())
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

class SMTLIB2Interface(args: List[String], var disableLetify: Boolean=false) extends Context with SMTLIB2Base {
  val smtlibInterfaceLogger = Logger(classOf[SMTLIB2Interface])

  type NameProviderFn = (String, Option[String]) => String
  var expressions : List[Expr] = List.empty
  val solverProcess = new InteractiveProcess(args, true)
  var synthDeclCommands : String = ""

  def generateDeclaration(sym: Symbol) = {
    val (typeName, newTypes) = generateDatatype(sym.typ)
    Utils.assert(newTypes.size == 0, "No new types are expected here.")
    val inputTypes = generateInputDataTypes(sym.typ).mkString(" ")
    val cmd = "(declare-fun %s (%s) %s)".format(sym, inputTypes, typeName)
    writeCommand(cmd)
  }

  /**
   *  Helper function that finds the list of all Oracle Symbols in an expression.
   */
  def findOracleSymbols(e : Expr) : Set[OracleSymbol] = {
    def symbolFinder(e : Expr) : Set[OracleSymbol] = {
      e match {
        case sym : OracleSymbol => Set(sym)
        case _ => Set.empty[OracleSymbol]
      }
    }
    Context.accumulateOverExpr(e, symbolFinder _, MutableMap.empty)
  }

  def generateOracleDeclaration(sym: OracleSymbol) = {
    val (typeName, newTypes) = generateDatatype(sym.typ)
    Utils.assert(newTypes.size == 0, "No new types are expected here.")

    val inputTypes = generateInputDataTypes(sym.typ)
    val inputNames = sym.symbolTyp.args.map( a => a._1.toString())
    val sig =  (inputNames zip inputTypes).map(a => a._2 ).mkString(" ")
    var cmd = ""
    cmd = "(declare-oracle-fun %s %s (%s) %s)\n".format(sym, sym.binary,  sig, typeName)
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
    val symbolsP = symbols.filter(s => !variables.contains(s))
    symbolsP.foreach {
      (s) => {
        variables += s
        generateDeclaration(s)
      }
    }
    val oracleSymbols = findOracleSymbols(e)
    val oracleSymbolsP = oracleSymbols.filter(s => !oracleVariables.contains(s))
    oracleSymbolsP.foreach {
      (s) => {
        oracleVariables += s
        generateOracleDeclaration(s)
      }
    }

    val smtlib2 = translateExpr(e, true)
    smtlibInterfaceLogger.debug("assert: {}", smtlib2)
    writeCommand("(assert " + smtlib2 +")")
  }

  override def preassert(e: Expr) {
    val declCommands = new ListBuffer[String]()
    Context.findTypes(e).filter(typ => !typeMap.contains(typ)).foreach {
      newType => {
        val (_, newTypes) = generateDatatype(newType)
        newTypes.foreach(typ => declCommands.append(typ))
      }
    }

    val algebraic = declCommands.filter(d => d.startsWith("(declare-datatype"))
    if (algebraic.length > 0) {
      val pattern = """\[[^\]]+\]""".r
  
      val names = algebraic.foldLeft("") { 
        case (acc, d) => { 
          val tmp = (pattern findAllIn d toList)
          acc + "(%s)".format(tmp.head.slice(1, tmp.head.length - 1))
        }
      }
  
      val fields = algebraic.foldLeft("") { 
        case (acc, d) => {
          val tmp = (pattern findAllIn d toList).tail.map{d => "(%s)".format(d.slice(1, d.length - 1))}.mkString(" ")
          acc + "(%s)".format(tmp)
        }
      }
  
      val decl = "(declare-datatypes (%s) (%s))".format(names, fields)
      writeCommand(decl)
      synthDeclCommands += decl
    }

    val other = declCommands.filterNot(d => d.startsWith("(declare-datatype"))
    other.foreach{
      decl => {
        writeCommand(decl)
      }
    }
  }

  override def check(produceModel: Boolean = true) : SolverResult = {
    smtlibInterfaceLogger.debug("check")
    Utils.assert(solverProcess.isAlive(), "Solver process is not alive!")
    writeCommand("(check-sat)")
    if (filePrefix == "") {
      readResponse() match {
        case Some(strP) =>
          val str = strP.stripLineEnd
          str match {
            case "sat" => SolverResult(Some(true), if(produceModel) getModel() else None)
            case "unsat" => SolverResult(Some(false), None)
            case _ =>
              throw new Utils.AssertionError("Unexpected result from SMT solver: " + str.toString())
          }
        case None =>
          throw new Utils.AssertionError("Unexpected EOF result from SMT solver.")
      }
    } else {
      // val smtOutput = solverProcess.toString()
      // Utils.writeToFile(f"$filePrefix%s-$curAssertName%s-$curAssertLabel%s-$counten%04d.smt", smtOutput)
      counten += 1
      return SolverResult(None, None)
    }
  }

  def getModel() : Option[Model] = {
    
  
    def readAndCountParen(buf : StringBuilder) : Integer = {
      val resp  = readResponse() match {
        case Some(str) => str
        case None => 
          throw new Utils.AssertionError("Unexpected EOF result from SMT solver.")
      }
      var open = 0
      resp.foreach(c => {
        buf += c
        c match {
          case '(' => open += 1
          case ')' => open -= 1
          case _ => 
        }
      })
      open
    }

    Utils.assert(solverProcess.isAlive(), "Solver process is not alive! Cannot retrieve model.")
    writeCommand("(get-model)")

    // Read output until we have a closing parentheses
    val buf = new StringBuilder
    var openParen = 0
    openParen += readAndCountParen(buf)

    while (openParen != 0) {
      Utils.assert(openParen >= 0, "Malformed output from SMT solver; too many closing parentheses")
      openParen += readAndCountParen(buf)
    }

    val strModel = buf.toString
    smtlibInterfaceLogger.debug("model: {}", strModel)
    val str = strModel.stripLineEnd
    val Pattern = "(?s)(.*)".r
    str match {
      case Pattern(_) =>
        Some(new SMTLIB2Model(str))
      case _ =>
        throw new Utils.AssertionError(s"Unexpected output from SMT solver:\n${str}")
    }
  }

  override def finish() {
    solverProcess.finishInput()
    Thread.sleep(5)
    solverProcess.kill()
  }

  override def push() {
    smtlibInterfaceLogger.debug("push")
    val e : (VarSet, LetMap, MutableSet[EnumLit]) = (variables.clone(), letVariables.clone(), enumLiterals.clone())
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

  override def checkSynth() : SolverResult = {
    throw new Utils.UnimplementedException("Can't use an SMT solver for synthesis!")
  }

  override def toString() : String = {
    solverProcess.toString()
  }

  override def addOption(opt : String, value : Context.SolverOption) = {
    // TODO: add the implementation here.
  }
}
