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
 * Author: Pramod Subramanyan
 *
 * Abstract solver context.
 *
 */
package uclid
package smt

import scala.collection.mutable.{Set => MutableSet}

case class SynonymMap(fwdMap: Map[String, Type], val revMap: Map[Type, Type]) {
  def addPrimitiveType(typ: Type) = {
    SynonymMap(fwdMap, revMap + (typ -> typ))
  }
  def addSynonym(name: String, typ: Type) = {
    SynonymMap(fwdMap + (name -> typ), revMap + (typ -> SynonymType(name, typ)))
  }
  def get(name: String) : Option[Type] = fwdMap.get(name)
  def get(typ: Type) : Option[Type] = revMap.get(typ)
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
          case BoolType() | IntType() | BitVectorType(_) =>
            synMap.addPrimitiveType(typ)
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

  /** Replace the types of all symbols in these expressions with their corresponding
   *  flattened types.
   */
  def flattenTypes(e : Expr, tMap : SynonymMap) : (Expr, SynonymMap) = {
    def flattenTypesInList(es : List[Expr], tMapIn : SynonymMap) : (List[Expr], SynonymMap) = {
      es.foldRight((List.empty[Expr], tMapIn)) {
        (arg, acc) => {
          val (argP, tMapP1) = flattenTypes(arg, acc._2)
          (argP :: acc._1, tMapP1)
        }
      }
    }
    e match {
      case intLit : IntLit => (intLit, tMap)
      case bvLit : BitVectorLit => (bvLit, tMap)
      case boolLit : BooleanLit => (boolLit, tMap)
      case enumLit : EnumLit =>
        val (enumTypeP, tMapP) = flatten(enumLit.eTyp, tMap)
        (enumLit, tMapP)
      case sym : Symbol =>
        val (typP, tMapP) = flatten(sym.symbolTyp, tMap)
        (Symbol(sym.id, typP), tMapP)
      case mkTuple : MakeTuple =>
        val (_, tMapP1) = flatten(mkTuple.typ, tMap)
        val (argsP, tMapP2) = flattenTypesInList(mkTuple.args, tMapP1)
        (MakeTuple(argsP), tMapP2)
      case opapp : OperatorApplication =>
        val (_, tMapP1) = flatten(opapp.typ, tMap)
        val (argsP, tMapP2) = flattenTypesInList(opapp.operands, tMapP1)
        (OperatorApplication(opapp.op, argsP), tMapP2)
      case arrSel : ArraySelectOperation =>
        val (eP, tMapP1) = flattenTypes(arrSel.e, tMap)
        val (indexP, tMapP2) = flattenTypesInList(arrSel.index, tMapP1)
        (ArraySelectOperation(eP, indexP), tMapP2)
      case arrStore : ArrayStoreOperation =>
        val (eP, tMapP1) = flattenTypes(arrStore.e, tMap)
        val (indexP, tMapP2) = flattenTypesInList(arrStore.index, tMapP1)
        val (valueP, tMapP3) = flattenTypes(arrStore.value, tMapP2)
        (ArrayStoreOperation(eP, indexP, valueP), tMapP3)
      case funcApp : FunctionApplication =>
        val (eP, tMapP1) = flattenTypes(funcApp.e, tMap)
        val (argsP, tMapP2) = flattenTypesInList(funcApp.args, tMapP1)
        (FunctionApplication(eP, argsP), tMapP2)
      case lambda : Lambda =>
        val (idsP, tMapP1) = flattenTypesInList(lambda.ids, tMap)
        val (exprP, tMapP2) = flattenTypes(lambda.e, tMapP1)
        (Lambda(idsP.map(id => id.asInstanceOf[Symbol]), exprP), tMapP2)
    }
  }

  // Interface to the symbolic simulator.
  def push()
  def pop()
  def assert(e: Expr)
  def check() : SolverResult
  def finish()
}

object Context 
{
  /**
   *  Helper function that finds the list of all symbols in an expression.
   */
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
      case IntLit(_) => syms
      case BitVectorLit(_,_) => syms
      case BooleanLit(_) => syms
      case EnumLit(_, _) => syms
      case Lambda(_,_) =>
        throw new Utils.AssertionError("lambdas in assertions should have been beta-reduced")
    }
  }

  def findSymbols(e : Expr) : Set[Symbol] = { findSymbols(e, Set()) }
}


