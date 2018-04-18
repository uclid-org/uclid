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
            val typeName = synTyp.name
            val (newType, synMapP1) = flatten(synTyp.typ, synMap)
            val synMapP = synMapP1.addSynonym(synTyp.name, newType)
            (newType, synMapP)
        }
    }
  }

  // Interface to the symbolic simulator.
  def push()
  def pop()
  def assert(e: Expr)
  def preassert(e: Expr)
  def check() : SolverResult
  def finish()
}

object Context
{
  /**
   *  Helper function that finds the list of all symbols in an expression.
   */
  def findSymbols(e : Expr) : Set[Symbol] = { findSymbols(e, Set.empty[Symbol]) }

  def findSymbols(e : Expr, syms : Set[Symbol]) : Set[Symbol] = {
    e match {
      case sym : Symbol =>
        return syms + sym
      case OperatorApplication(op,operands) =>
        return operands.foldLeft(syms)((acc,i) => findSymbols(i, acc))
      case ArraySelectOperation(e, index) =>
        return index.foldLeft(findSymbols(e, syms))((acc, i) => findSymbols(i, acc))
      case ArrayStoreOperation(e, index, value) =>
        return index.foldLeft(findSymbols(value, findSymbols(e, syms)))((acc,i) => findSymbols(i, acc))
      case FunctionApplication(e, args) =>
        return args.foldLeft(findSymbols(e, syms))((acc,i) => findSymbols(i, acc))
      case MakeTuple(args) =>
        return args.foldLeft(syms)((acc, i) => findSymbols(i, acc))
      case IntLit(_) => syms
      case BitVectorLit(_,_) => syms
      case BooleanLit(_) => syms
      case EnumLit(_, _) => syms
      case Lambda(_,_) =>
        throw new Utils.AssertionError("Lambdas should have been beta-reduced by now.")
    }
  }

  /**
   * Helper function that finds all enum literals in an expression.
   */
  def findEnumLits(e : Expr) : Set[EnumLit] = findEnumLits(e, Set.empty[EnumLit])

  def findEnumLits(e: Expr, eLits: Set[EnumLit]) : Set[EnumLit] = {
    e match {
      case Symbol(_, _) => eLits
      case OperatorApplication(op, operands) =>
        findEnumLits(operands, eLits)
      case ArraySelectOperation(e, index) =>
        findEnumLits(index, findEnumLits(e, eLits))
      case ArrayStoreOperation(e, index, value) =>
        findEnumLits(index, findEnumLits(e, findEnumLits(value, eLits)))
      case FunctionApplication(e, args) =>
        findEnumLits(args, findEnumLits(e, eLits))
      case MakeTuple(args) =>
        findEnumLits(args, eLits)
      case IntLit(_) | BitVectorLit(_, _) | BooleanLit(_) => eLits
      case enumLit : EnumLit => eLits + enumLit
      case Lambda(_, _) =>
        throw new Utils.AssertionError("Lambdas should have been beta-reduced by now.")
    }
  }
  def findEnumLits(es : List[Expr], eLits: Set[EnumLit]) : Set[EnumLit] = {
    es.foldLeft(eLits)((acc, e) => findEnumLits(e, acc))
  }

  def getMkTupleFunction(typeName: String) : String = {
    "_make_" + typeName
  }
  def getFieldName(field: String) : String = {
    "_field_" + field
  }
}