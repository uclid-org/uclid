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
 * Author : Pramod Subramanyan, Kevin Cheang
 *
 * The EnumTypeRenamerPass rewrites all enum types into bitvector types.
 *
 */
package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.immutable.Map

object Logic {
  val LIA = "LIA"
  val BV = "BV"
}

// Makes a pass to save enumerative type names into the renameMapAnnotation
// class EnumTypeAnalysisPass() extends ReadOnlyPass[MutableMap[Expr, BigInt]] {
  // type T = MutableMap[Expr, BigInt]
class EnumTypeAnalysisPass() extends ReadOnlyPass[ExprRenameMapAnnotation] {
  type T = ExprRenameMapAnnotation

  var enumRename : BigInt = BigInt(-1)

  override  def applyOnStateVars(d : TraversalDirection.T, stVars : StateVarsDecl, in : T, context : Scope) : T = {
    if (!stVars.typ.isInstanceOf[EnumType]) return in
    stVars.ids.foldLeft(in) {
      (ann, member) => {
        if (!in.enumVarTypeMap.exists(_._1 == member)) {
          ExprRenameMapAnnotation(ann.renameMap, ann.enumVarTypeMap + (member -> stVars.typ), ann.enumTypeRangeMap)
        } else {
          in
        }
      }
    }
  }

  override def applyOnEnumType(d : TraversalDirection.T, enumT : EnumType, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down && !in.renameMap.exists(_._1 == enumT.ids(0))) {
      val minEnumVal = enumRename + 1
      val inP = enumT.ids.foldLeft(in) {
        (ann, member) => {
          enumRename = enumRename + 1
          ExprRenameMapAnnotation(ann.renameMap + (member -> enumRename), ann.enumVarTypeMap, ann.enumTypeRangeMap)
        }
      }
      val maxEnumVal = enumRename
      ExprRenameMapAnnotation(inP.renameMap, inP.enumVarTypeMap, inP.enumTypeRangeMap + (enumT -> (minEnumVal, maxEnumVal)))
    } else {
      in
    }
  }
}

class EnumTypeAnalysis() extends ASTAnalyzer("EnumTypeAnalysis", new EnumTypeAnalysisPass()) {
  override def reset() {
    in = Some(ExprRenameMapAnnotation(MutableMap.empty, MutableMap.empty, MutableMap.empty))
  }
  
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val renameMapAnnotation = visitModule(module, ExprRenameMapAnnotation(MutableMap.empty, MutableMap.empty, MutableMap.empty), context)
    _out = Some(renameMapAnnotation)
    return Some(Module(module.id, module.decls, module.cmds, module.notes :+ renameMapAnnotation))
  }
}

// Make a pass to convert all enumerative types to numeric type(s) (bitvector / integer)
class EnumTypeRenamerPass(logic : String) extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val enumTypeAnalysis = manager.pass("EnumTypeAnalysis").asInstanceOf[EnumTypeAnalysis]
  lazy val enumMap : MutableMap[Expr, BigInt] = enumTypeAnalysis.out.get.renameMap
  lazy val enumBVWidth : Int = enumTypeAnalysis.out.get.bvSize

  def replaceEnumMembers(e : Expr, ctx : Scope) : Option[Expr] = {
    if (!e.isInstanceOf[Identifier]) return Some(e)
    val eId = e.asInstanceOf[Identifier]
    if (!ctx.map.get(eId).get.isInstanceOf[Scope.EnumIdentifier]) return Some(e)
    logic match {
      case Logic.BV => 
        Some(BitVectorLit(enumMap(eId), enumBVWidth))
      case Logic.LIA =>
        Some(IntLit(enumMap(eId)))
      case _ =>
        throw new Utils.UnimplementedException("Logic type %s not supported.".format(logic))
    }
  }

  override def rewriteExpr(e : Expr, ctx : Scope) : Option[Expr] = {
    replaceEnumMembers(e, ctx)
  }

  def enumTypeToNumericType(typ : Type) : Option[Type] = {
    typ match {
      case EnumType(_) =>
        logic match {
          case Logic.BV =>
            Some(BitVectorType(enumBVWidth))
          case Logic.LIA =>
            Some(IntegerType())
          case _ =>
            throw new Utils.UnimplementedException("Logic type %s not supported.".format(logic))
        }
      case _ =>
        Some(typ)
    }
  }

  override def rewriteType(typ: Type, ctx : Scope) : Option[Type] = {
    enumTypeToNumericType(typ)
  }
}

class EnumTypeRenamer(logic : String) extends ASTRewriter("EnumTypeRenamer", new EnumTypeRenamerPass(logic))

// Make a pass to add module level constraints to enumerative types (currently only support bitvector bounding)
class EnumTypeRenamerConsPass(logic : String) extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val enumTypeAnalysis = manager.pass("EnumTypeAnalysis").asInstanceOf[EnumTypeAnalysis]
  lazy val enumVarTypeMap = enumTypeAnalysis.out.get.enumVarTypeMap
  lazy val enumTypeRangeMap = enumTypeAnalysis.out.get.enumTypeRangeMap
  lazy val bvSize = enumTypeAnalysis.out.get.bvSize

  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val newAxioms = enumVarTypeMap.map(vt => {
      val minEnumVal = enumTypeRangeMap(vt._2)._1
      val maxEnumVal = enumTypeRangeMap(vt._2)._2
      val lowerBound = OperatorApplication(BVLEOp(bvSize), List(BitVectorLit(minEnumVal, bvSize), vt._1))
      val upperBound = OperatorApplication(BVLEOp(bvSize), List(vt._1, BitVectorLit(maxEnumVal, bvSize)))
      val cons = OperatorApplication(ConjunctionOp(), List(lowerBound, upperBound))
      AxiomDecl(Some(Identifier(vt._1.toString() + "_enum_cons")), cons, List.empty)
    }).toList
    val declsP : List[Decl] = module.decls ++ newAxioms
    val moduleP = Module(module.id, declsP, module.cmds, module.notes)
    Some(moduleP)
  }

}

class EnumTypeRenamerCons(logic : String) extends ASTRewriter("EnumTypeRenamerCons", new EnumTypeRenamerConsPass(logic))
