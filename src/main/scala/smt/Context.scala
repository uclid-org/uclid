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
case class DeclVarCmd(id: Symbol, typ: Type) extends Command
case class DeclSortCmd(id: Symbol, typ: Type) extends Command
case class PushCmd() extends Command
case class PopCmd() extends Command
case class CheckCmd(e: Expr) extends Command

class Context {
  var typeMap : SynonymMap = SynonymMap.empty
  var sorts : List[(String, Type)] = List.empty
  var variables : List[(String, Type)] = List.empty
  var commands : List[Command] = List.empty

  type NameProviderFn = (String, Option[String]) => String

  /** Flatten a type and add it to the type synonym map. */
  def flatten(typ: Type, nameProvider: NameProviderFn, synMap: SynonymMap) : (Type, SynonymMap) = {
    // Define a couple of helper functions.
    /* Recurse on a list of types. */
    def flattenTypeList(typeList: List[Type], synMap: SynonymMap) : (List[Type], SynonymMap) = {
      typeList.foldRight(List.empty[Type], synMap) {
        (iTyp, acc) => {
          val (newType, newAcc) = flatten(iTyp, nameProvider, acc._2)
          (newType :: acc._1, newAcc)
        }
      }
    }
    /* Recurse on a list of fields: (String, Type) tuples. */
    def flattenFieldList(fieldList: List[(String, Type)], synMap: SynonymMap) : (List[(String, Type)], SynonymMap) = {
      fieldList.foldRight(List.empty[(String, Type)], synMap) {
        (fld, acc) => {
          val (newType, newAcc) = flatten(fld._2, nameProvider, acc._2)
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
            val typeName = nameProvider("UninterpretedType", Some(unintTyp.name))
            val synMapP = synMap.addSynonym(typeName, unintTyp)
            (synMapP.get(typeName).get, synMapP)
          case tupleTyp : TupleType =>
            // create new type
            val (newTypes, synMapP1) = flattenTypeList(tupleTyp.types, synMap)
            val newTupleTyp = TupleType(newTypes)
            // add to map
            val typeName = nameProvider("TupleType", None)
            val synMapP = synMapP1.addSynonym(typeName, newTupleTyp)
            (synMapP.get(typeName).get, synMapP)
          case recordType : RecordType =>
            // create new type
            val (newFields, synMapP1) = flattenFieldList(recordType.fields_, synMap) 
            val newRecordType = RecordType(newFields)
            // add to map
            val typeName = nameProvider("RecordType", None)
            val synMapP = synMapP1.addSynonym(typeName, newRecordType)
            (synMapP.get(typeName).get, synMapP)
          case mapType : MapType =>
            // create new type
            val (newInTypes, synMapP1) = flattenTypeList(mapType.inTypes, synMap)
            val (newOutType, synMapP2) = flatten(mapType.outType, nameProvider, synMapP1)
            val newMapType = MapType(newInTypes, newOutType)
            // add to map
            val typeName = nameProvider("MapType", None)
            val synMapP = synMapP2.addSynonym(typeName, newMapType)
            (synMapP.get(typeName).get, synMapP)
          case arrayType : ArrayType =>
            // create new type
            val (newInTypes, synMapP1) = flattenTypeList(arrayType.inTypes, synMap)
            val (newOutType, synMapP2) = flatten(arrayType.outType, nameProvider, synMapP1)
            val newArrayType = ArrayType(newInTypes, newOutType)
            // add to map
            val typeName = nameProvider("RecordType", None)
            val synMapP = synMapP2.addSynonym(typeName, newArrayType)
            (synMapP.get(typeName).get, synMapP)
          case enumType : EnumType =>
            // add to map
            val typeName = nameProvider("EnumType", None)
            val synMapP = synMap.addSynonym(typeName, enumType)
            (synMapP.get(typeName).get, synMapP)
          case synTyp : SynonymType =>
            val typeName = synTyp.name
            val (newType, synMapP1) = flatten(synTyp.typ, nameProvider, synMap)
            val synMapP = synMapP1.addSynonym(synTyp.name, newType)
            (newType, synMapP)
        }
    }
  }

  def replaceTypes(e : Expr, nameProvider : NameProviderFn, tMap : SynonymMap) : (Expr, SynonymMap) = {
    def replaceTypesInList(es : List[Expr], tMapIn : SynonymMap) : (List[Expr], SynonymMap) = {
      es.foldRight((List.empty[Expr], tMapIn)) {
        (arg, acc) => {
          val (argP, tMapP1) = replaceTypes(arg, nameProvider, acc._2)
          (argP :: acc._1, tMapP1)
        }
      }
    }
    e match {
      case intLit : IntLit => (intLit, tMap)
      case bvLit : BitVectorLit => (bvLit, tMap)
      case boolLit : BooleanLit => (boolLit, tMap)
      case enumLit : EnumLit =>
        val (enumTypeP, tMapP) = flatten(enumLit.eTyp, nameProvider, tMap)
        (enumLit, tMapP)
      case sym : Symbol =>
        val (typP, tMapP) = flatten(sym.symbolTyp, nameProvider, tMap)
        (Symbol(sym.id, typP), tMapP)
      case mkTuple : MakeTuple =>
        val (_, tMapP1) = flatten(mkTuple.typ, nameProvider, tMap)
        val (argsP, tMapP2) = replaceTypesInList(mkTuple.args, tMapP1)
        (MakeTuple(argsP), tMapP2)
      case opapp : OperatorApplication =>
        val (_, tMapP1) = flatten(opapp.typ, nameProvider, tMap)
        val (argsP, tMapP2) = replaceTypesInList(opapp.operands, tMapP1)
        (OperatorApplication(opapp.op, argsP), tMapP2)
      case arrSel : ArraySelectOperation =>
        val (eP, tMapP1) = replaceTypes(arrSel.e, nameProvider, tMap)
        val (indexP, tMapP2) = replaceTypesInList(arrSel.index, tMapP1)
        (ArraySelectOperation(eP, indexP), tMapP2)
      case arrStore : ArrayStoreOperation =>
        val (eP, tMapP1) = replaceTypes(arrStore.e, nameProvider, tMap)
        val (indexP, tMapP2) = replaceTypesInList(arrStore.index, tMapP1)
        val (valueP, tMapP3) = replaceTypes(arrStore.value, nameProvider, tMapP2)
        (ArrayStoreOperation(eP, indexP, valueP), tMapP3)
      case funcApp : FunctionApplication =>
        val (eP, tMapP1) = replaceTypes(funcApp.e, nameProvider, tMap)
        val (argsP, tMapP2) = replaceTypesInList(funcApp.args, tMapP1)
        (FunctionApplication(eP, argsP), tMapP2)
      case lambda : Lambda =>
        val (idsP, tMapP1) = replaceTypesInList(lambda.ids, tMap)
        val (exprP, tMapP2) = replaceTypes(lambda.e, nameProvider, tMapP1)
        (Lambda(idsP.map(id => id.asInstanceOf[Symbol]), exprP), tMapP2)
    }
  }
}





