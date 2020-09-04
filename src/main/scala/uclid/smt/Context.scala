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
 * Author: Pramod Subramanyan
 *
 * Abstract solver context.
 *
 */
package uclid
package smt

import scala.collection.mutable.{Set => MutableSet}
import scala.collection.mutable.{Map => MutableMap}

case class SynonymMap(fwdMap: Map[String, Type], val revMap: Map[Type, SynonymType]) {
  def addSynonym(name: String, typ: Type) = {
    SynonymMap(fwdMap + (name -> typ), revMap + (typ -> SynonymType(name, typ)))
  }
  def get(name: String) : Option[Type] = fwdMap.get(name)
  def get(typ: Type) : Option[SynonymType] = revMap.get(typ)
  def contains(name: String) : Boolean = fwdMap.contains(name)
  def contains(typ: Type) : Boolean = revMap.contains(typ)
}

object SynonymMap {
  def empty = SynonymMap(Map.empty, Map.empty)
}

// Solver command.
sealed abstract class Command
case class DeclSortCmd(id: Symbol, typ: Type) extends Command
case class DeclVarCmd(id: Symbol, typ: Type) extends Command
case class PushCmd() extends Command
case class PopCmd() extends Command
case class AssertCmd(e: Expr) extends Command
case class CheckCmd() extends Command
case class GetModelCmd() extends Command

abstract class Model {
  def evaluate(e : Expr) : Expr = {
    throw new Utils.UnimplementedException("evaluate not implemented yet.")
  }
  def evalAsString(e : Expr) : String = {
    throw new Utils.UnimplementedException("evalAsString not implemented yet.")
  }
}

case class SolverResult(result : Option[Boolean], model: Option[Model]) {
  def isValue(expected : Boolean) : Boolean = {
    result match {
      case Some(b) => b == expected
      case None => false
    }
  }
  def isTrue = isValue(true)
  def isFalse = isValue(false)
  def isDefined = result.isDefined
  def isUndefined = result.isEmpty
  def isModelDefined = model.isDefined
  def evalAsString(e : Expr) : Option[String] = { model.flatMap((m) => Some(m.evalAsString(e))) }
}


abstract trait Context {
  /** Random string generator. */
  val strGen = (new scala.util.Random()).alphanumeric
  /** Set of known names. */
  var names : MutableSet[String] = MutableSet.empty
  /** Create a new (unique) name. */
  def uniqueNamer(base: String, tag: Option[String]) : String = {
    def attempt(addRnd: Boolean) : String = {
      base + (tag match {
        case Some(t) => t
        case None => ""
      }) + (if (addRnd) strGen.take(5) else "")
    }
    var name : String = attempt(false)
    while (names.contains(name)) {
      name = attempt(true)
    }
    names += name
    return name
  }

  var counten = 1
  var filePrefix = ""
  var curAssertName = ""
  var curAssertLabel = ""

  /** Flatten a type and add it to the type synonym map. */
  def flatten(typ: Type, synMap: SynonymMap) : (Type, SynonymMap) = {
    // Define a couple of helper functions.
    /* Recurse on a list of types. */
    def flattenTypeList(typeList: List[Type], synMap: SynonymMap) : (List[Type], SynonymMap) = {
      typeList.foldRight(List.empty[Type], synMap) {
        (iTyp, acc) => {
          val (newType, newAcc) = flatten(iTyp, acc._2)
          (newType :: acc._1, newAcc)
        }
      }
    }
    /* Recurse on a list of fields: (String, Type) tuples. */
    def flattenFieldList(fieldList: List[(String, Type)], synMap: SynonymMap) : (List[(String, Type)], SynonymMap) = {
      fieldList.foldRight(List.empty[(String, Type)], synMap) {
        (fld, acc) => {
          val (newType, newAcc) = flatten(fld._2, acc._2)
          ((fld._1, newType) :: acc._1, newAcc)
        }
      }
    }

    // Now for the actual implementation.
    synMap.get(typ) match {
      case Some(t) => (t, synMap)
      case None =>
        typ match {
          case BoolType | IntType | BitVectorType(_) =>
            (typ, synMap)
          case unintTyp : UninterpretedType =>
            // add to map
            val typeName = uniqueNamer("UninterpretedType", Some(unintTyp.name))
            val synMapP = synMap.addSynonym(typeName, unintTyp)
            (synMapP.get(typeName).get, synMapP)
          case tupleTyp : TupleType =>
            // create new type
            val (newTypes, synMapP1) = flattenTypeList(tupleTyp.types, synMap)
            val newTupleTyp = TupleType(newTypes)
            // add to map
            val typeName = uniqueNamer("TupleType", None)
            val synMapP = synMapP1.addSynonym(typeName, newTupleTyp)
            (synMapP.get(typeName).get, synMapP)
          case recordType : RecordType =>
            // create new type
            val (newFields, synMapP1) = flattenFieldList(recordType.fields_, synMap)
            val newRecordType = RecordType(newFields)
            // add to map
            val typeName = uniqueNamer("RecordType", None)
            val synMapP = synMapP1.addSynonym(typeName, newRecordType)
            (synMapP.get(typeName).get, synMapP)
          case mapType : MapType =>
            // create new type
            val (newInTypes, synMapP1) = flattenTypeList(mapType.inTypes, synMap)
            val (newOutType, synMapP2) = flatten(mapType.outType, synMapP1)
            val newMapType = MapType(newInTypes, newOutType)
            // add to map
            val typeName = uniqueNamer("MapType", None)
            val synMapP = synMapP2.addSynonym(typeName, newMapType)
            (synMapP.get(typeName).get, synMapP)
          case arrayType : ArrayType =>
            // create new type
            val (newInTypes, synMapP1) = flattenTypeList(arrayType.inTypes, synMap)
            val (newOutType, synMapP2) = flatten(arrayType.outType, synMapP1)
            val newArrayType = ArrayType(newInTypes, newOutType)
            // add to map
            val typeName = uniqueNamer("RecordType", None)
            val synMapP = synMapP2.addSynonym(typeName, newArrayType)
            (synMapP.get(typeName).get, synMapP)
          case enumType : EnumType =>
            // add to map
            val typeName = uniqueNamer("EnumType", None)
            val synMapP = synMap.addSynonym(typeName, enumType)
            (synMapP.get(typeName).get, synMapP)
          case synTyp : SynonymType =>
            val (newType, synMapP1) = flatten(synTyp.typ, synMap)
            val synMapP = synMapP1.addSynonym(synTyp.name, newType)
            (newType, synMapP)
          case UndefinedType =>
            throw new Utils.AssertionError("Undefined types are not expected here.")
        }
    }
  }

  // Interface to the symbolic simulator.
  def push(): Unit
  def pop(): Unit
  def assert(e: Expr): Unit
  def preassert(e: Expr): Unit
  def check(produceModel: Boolean = true) : SolverResult
  def checkSynth() : SolverResult
  def finish(): Unit

  def addOption(option: String, value: Context.SolverOption): Unit
}

object Context
{
  sealed abstract class SolverOption {}
  case class BoolOption(b : Boolean) extends SolverOption {
    override def toString() : String = b.toString()
  }
  case class IntOption(i : Int) extends SolverOption {
    override def toString() : String = i.toString()
  }
  case class DoubleOption(d : Double) extends SolverOption {
    override def toString() : String = d.toString()
  }
  case class StringOption(s : String) extends SolverOption {
    override def toString() : String = s
  }

  def convertReplace(w : Int, hi : Int, lo : Int, arg0 : Expr, arg1 : Expr) : Expr = {
    val slice0 = (w-1, hi+1)
    val slice2 = (lo-1, 0)

    // Convert a valid slice into Some(bvexpr) and an invalid slice into none.
    def getSlice(slice : (Int, Int), arg : Expr) : Option[Expr] = {
      if (slice._1 >= slice._2) {
        Utils.assert(slice._1 < w && slice._1 >= 0, "Invalid slice: " + slice.toString)
        Utils.assert(slice._2 < w && slice._2 >= 0, "Invalid slice: " + slice.toString)
        val extractOp = OperatorApplication(BVExtractOp(slice._1, slice._2), List(arg))
        Some(extractOp)
      } else {
        None
      }
    }
    // Now merge the slices.
    val slices : List[Expr] = List(getSlice(slice0, arg0), Some(arg1), getSlice(slice2, arg0)).flatten
    val repl = slices.tail.foldLeft(slices.head) {
      (r0, r1) => {
        Utils.assert(r0.typ.isInstanceOf[BitVectorType], "Expected a bitvector.")
        Utils.assert(r1.typ.isInstanceOf[BitVectorType], "Expected a bitvector.")
        val r0Width = r0.typ.asInstanceOf[BitVectorType].width
        val r1Width = r1.typ.asInstanceOf[BitVectorType].width
        OperatorApplication(BVConcatOp(r0Width + r1Width), List(r0, r1))
      }
    }
    return repl
  }

  def rewriteExpr(e : Expr, rewrite : (Expr => Expr), memo : MutableMap[Expr, Expr]) : Expr = {
    memo.get(e) match {
      case Some(eP) => eP
      case None =>
        val eP = e match {
          case Symbol(_, _) | IntLit(_) | BitVectorLit(_, _) | BooleanLit(_) | BooleanLit(_) | EnumLit(_, _) | ConstArray(_, _) | SynthSymbol (_, _, _, _, _) =>
            rewrite(e)
          case OperatorApplication(op, operands) =>
            val operandsP = operands.map(arg => rewriteExpr(arg, rewrite, memo))
            rewrite(OperatorApplication(op, operandsP))
          case ArraySelectOperation(array, index) =>
            val arrayP = rewriteExpr(array, rewrite, memo)
            val indexP = index.map(ind => rewriteExpr(ind, rewrite, memo))
            rewrite(ArraySelectOperation(arrayP, indexP))
          case ArrayStoreOperation(array, index, value) =>
            val arrayP = rewriteExpr(array, rewrite, memo)
            val indexP = index.map(ind => rewriteExpr(ind, rewrite, memo))
            val valueP = rewriteExpr(value, rewrite, memo)
            rewrite(ArrayStoreOperation(arrayP, indexP, valueP))
          case FunctionApplication(func, args) =>
            val funcP = rewriteExpr(func, rewrite, memo)
            val argsP = args.map(arg => rewriteExpr(arg, rewrite, memo))
            rewrite(FunctionApplication(funcP, argsP))
          case MakeTuple(args) =>
            val argsP = args.map(arg => rewriteExpr(arg, rewrite, memo))
            rewrite(MakeTuple(argsP))
          case Lambda(ids, expr) =>
            val idsP = ids.map(id => rewriteExpr(id, rewrite, memo).asInstanceOf[Symbol])
            val exprP = rewriteExpr(expr, rewrite, memo)
            rewrite(Lambda(idsP, exprP))
        }
        memo.put(e, eP)
        eP
    }
  }
  def rewriteBVReplace(e : Expr) : Expr = {
    def rewriter(e : Expr) : Expr = {
      e match {
        case OperatorApplication(BVReplaceOp(w, hi, lo), operands) =>
          convertReplace(w, hi, lo, operands(0), operands(1))
        case _ =>
          e
      }
    }
    rewriteExpr(e, rewriter, MutableMap.empty)
  }

  /**
   *  Helper function that finds the list of all symbols in an expression.
   */
  def findSymbols(e : Expr) : Set[Symbol] = {
    def symbolFinder(e : Expr) : Set[Symbol] = {
      e match {
        case sym : Symbol => Set(sym)
        case _ => Set.empty[Symbol]
      }
    }
    accumulateOverExpr(e, symbolFinder _, MutableMap.empty)
  }

  def accumulateOverExpr[T](e : Expr, apply : (Expr => Set[T]), memo : MutableMap[Expr, Set[T]]) : Set[T] = {
    memo.get(e) match {
      case Some(result) =>
        result
      case None =>
        val eResult = apply(e)
        val results = e match {
          case Symbol(_, _) | IntLit(_) | BitVectorLit(_,_) | BooleanLit(_) | EnumLit(_, _) | SynthSymbol(_, _, _, _, _) =>
            eResult
          case ConstArray(expr, _) =>
            eResult ++ accumulateOverExpr(expr, apply, memo)
          case OperatorApplication(_,operands) =>
            eResult ++ accumulateOverExprs(operands, apply, memo)
          case ArraySelectOperation(e, index) =>
            eResult ++ accumulateOverExpr(e, apply, memo) ++ accumulateOverExprs(index, apply, memo)
          case ArrayStoreOperation(e, index, value) =>
            eResult ++ accumulateOverExpr(e, apply, memo) ++ accumulateOverExprs(index, apply, memo) ++ accumulateOverExpr(value, apply, memo)
          case FunctionApplication(e, args) =>
            eResult ++ accumulateOverExpr(e, apply, memo) ++ accumulateOverExprs(args, apply, memo)
          case MakeTuple(args) =>
            eResult ++ accumulateOverExprs(args, apply, memo)
          case Lambda(_,_) =>
            throw new Utils.AssertionError("Lambdas should have been beta-reduced by now.")
        }
        memo.put(e, results)
        results
    }
  }
  def accumulateOverExprs[T](es : List[Expr], apply : (Expr => Set[T]), memo : MutableMap[Expr, Set[T]]) : Set[T] = {
    val empty : Set[T] = Set.empty
    es.foldLeft(empty)((acc, e) => acc ++ accumulateOverExpr(e, apply, memo))
  }

  def findFreeSymbols(e : smt.Expr, memo : MutableMap[Expr, Set[Symbol]]) : Set[Symbol] = {
    memo.get(e) match {
      case Some(result) => result
      case None =>
        val s : Set[Symbol] = e match {
          case s : Symbol => Set(s)
          case _ => Set.empty
        }
        memo.put(e, s)
        s
    }
  }

  /**
   * Helper function that finds all the types that appear in an expression.
   */
  def findTypes(e : Expr) : Set[Type] = {
    def typeFinder(e : Expr) : Set[Type] = {
      Set(e.typ)
    }
    accumulateOverExpr(e, typeFinder _, MutableMap.empty)
  }

  def getMkTupleFunction(typeName: String) : String = {
    "_make_" + typeName
  }
  def getFieldName(field: String) : String = {
    "_field_" + field
  }

  def mergeCounts(m1 : Map[Expr, Int], m2 : Map[Expr, Int]) : Map[Expr, Int] = {
    val keys = m1.keys ++ m2.keys
    keys.map(k => {
      val cnt = m1.get(k).getOrElse(0) +  m2.get(k).getOrElse(0)
      k -> cnt
    }).toMap
  }

  def foldOverExpr[T](init : T, f : ((T, Expr) => T), e : Expr) : T = {
    val subResult = e match {
      case Symbol(_, _) | IntLit(_) | BitVectorLit(_, _) | BooleanLit(_) | EnumLit(_, _) | SynthSymbol(_, _, _, _, _) =>
        init
      case OperatorApplication(_, operands) =>
        foldOverExprs(init, f, operands)
      case ArraySelectOperation(e, index) =>
        foldOverExprs(foldOverExpr(init, f, e), f, index)
      case ArrayStoreOperation(e, index, value) =>
        foldOverExprs(foldOverExpr(foldOverExpr(init, f, e), f, value), f, index)
      // FIXME: more cases here.
    }
    f(subResult, e)
  }
  def foldOverExprs[T](init : T, f : ((T, Expr) => T), es : List[Expr]) : T = {
    es.foldLeft(init)((acc, e) => foldOverExpr(acc, f, e))
  }

}
