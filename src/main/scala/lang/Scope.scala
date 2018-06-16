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

 * Class to track scope/context for UCLID ASTs.
 *
 */

package uclid
package lang

import scala.collection.mutable.{Set => MutableSet}

object Scope {
  sealed abstract class NamedExpression(val id : Identifier, val typ: Type) {
    val isReadOnly = false
  }
  sealed abstract class ReadOnlyNamedExpression(id : Identifier, typ: Type) extends NamedExpression(id, typ) {
    override val isReadOnly = true
  }
  case class ModuleDefinition(mod : lang.Module) extends ReadOnlyNamedExpression(mod.id, mod.moduleType)
  case class Instance(instD: InstanceDecl) extends ReadOnlyNamedExpression(instD.instanceId, instD.moduleType)
  case class TypeSynonym(typId : Identifier, sTyp: Type) extends ReadOnlyNamedExpression(typId, sTyp)
  case class StateVar(varId : Identifier, varTyp: Type) extends NamedExpression(varId, varTyp)
  case class InputVar(inpId : Identifier, inpTyp: Type) extends ReadOnlyNamedExpression(inpId, inpTyp)
  case class OutputVar(outId : Identifier, outTyp: Type) extends NamedExpression(outId, outTyp)
  case class SharedVar(varId : Identifier, varTyp : Type) extends NamedExpression(varId, varTyp)
  case class ConstantLit(cId : Identifier, lit : NumericLit) extends ReadOnlyNamedExpression(cId, lit.typeOf)
  case class ConstantVar(cId : Identifier, cTyp : Type) extends ReadOnlyNamedExpression(cId, cTyp)
  case class Function(fId : Identifier, fTyp: Type) extends ReadOnlyNamedExpression(fId, fTyp)
  case class Grammar(gId : Identifier, gTyp : Type) extends ReadOnlyNamedExpression(gId, gTyp)
  case class Define(dId : Identifier, dTyp : Type, defDecl: DefineDecl) extends ReadOnlyNamedExpression(dId, dTyp)
  case class Procedure(pId : Identifier, pTyp: Type) extends ReadOnlyNamedExpression(pId, pTyp)
  case class ProcedureInputArg(argId : Identifier, argTyp: Type) extends ReadOnlyNamedExpression(argId, argTyp)
  case class ProcedureOutputArg(argId : Identifier, argTyp: Type) extends NamedExpression(argId, argTyp)
  case class ProcedureLocalVar(vId : Identifier, vTyp : Type) extends NamedExpression(vId, vTyp)
  case class BlockVar(vId : Identifier, vTyp : Type) extends NamedExpression(vId, vTyp)
  case class FunctionArg(argId : Identifier, argTyp : Type) extends ReadOnlyNamedExpression(argId, argTyp)
  case class LambdaVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)
  case class ForIndexVar(iId : Identifier, iTyp : Type) extends ReadOnlyNamedExpression(iId, iTyp)
  case class SpecVar(varId : Identifier, expr: Expr) extends ReadOnlyNamedExpression(varId, BooleanType())
  case class AxiomVar(varId : Identifier, expr : Expr) extends ReadOnlyNamedExpression(varId, BooleanType())
  case class EnumIdentifier(enumId : Identifier, enumTyp : EnumType) extends ReadOnlyNamedExpression(enumId, enumTyp)
  case class ForallVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)
  case class ExistsVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)
  case class VerifResultVar(vId : Identifier, cmd : GenericProofCommand) extends ReadOnlyNamedExpression(vId, UndefinedType())

  type IdentifierMap = Map[Identifier, NamedExpression]
  def addToMap(map : Scope.IdentifierMap, expr: Scope.NamedExpression) : Scope.IdentifierMap = {
    map + (expr.id -> expr)
  }
  def addTypeToMap(map : Scope.IdentifierMap, typ : Type, module : Option[Module]) : Scope.IdentifierMap = {
    typ match {
      case enumTyp : EnumType =>
        enumTyp.ids.foldLeft(map)((m, id) => {
          m.get(id) match {
            case Some(namedExpr) =>
              namedExpr match {
                case EnumIdentifier(eId, eTyp) =>
                  Utils.checkParsingError(eTyp == enumTyp,
                      "Identifier " + eId.name + " redeclared as a member of a different enum",
                      eTyp.pos, module.flatMap(_.filename))
                  m
                case _ =>
                  Utils.raiseParsingError("Redeclaration of identifier " + id.name, id.pos, module.flatMap(_.filename))
                  m
              }
            case None =>
              m + (id -> EnumIdentifier(id, enumTyp))
          }
        })
      case prodType : ProductType =>
        prodType.fields.foldLeft(map)((m, f) => addTypeToMap(m, f._2, module))
      case mapType : MapType =>
        val m1 = mapType.inTypes.foldLeft(map)((m, a) => addTypeToMap(m, a, module))
        addTypeToMap(m1, mapType.outType, module)
      case arrayType : ArrayType =>
        val m1 = arrayType.inTypes.foldLeft(map)((m, i) => addTypeToMap(m, i, module))
        addTypeToMap(m1, arrayType.outType, module)
      case _ => map
    }
  }
  /** Create an empty context. */
  def empty : Scope = Scope(Map.empty[Identifier, Scope.NamedExpression], None, None, None, ModuleEnvironment, false)
}

sealed abstract class ExpressionEnvironment {
  def isVerificationContext : Boolean = false
  def isModuleLevel : Boolean = false
  def isProcedural : Boolean = false
}
case object ModuleEnvironment extends ExpressionEnvironment {
  override def isModuleLevel = true
}
case object SequentialEnvironment extends ExpressionEnvironment {
}
case object ProceduralEnvironment extends ExpressionEnvironment {
  override def isProcedural = true
}
case object RequiresEnvironment extends ExpressionEnvironment {
  override def isVerificationContext = true
}
case object EnsuresEnvironment extends ExpressionEnvironment {
  override def isVerificationContext = true
}
case object AssertEnvironment extends ExpressionEnvironment {
  override def isVerificationContext = true
}
case object AssumeEnvironment extends ExpressionEnvironment {
  override def isVerificationContext = true
}
case object ProceduralAssertEnvironment extends ExpressionEnvironment {
  override def isVerificationContext = true
  override def isProcedural = true
}
case object ProceduralAssumeEnvironment extends ExpressionEnvironment {
  override def isVerificationContext = true
  override def isProcedural = true
}
case object SpecEnvironment extends ExpressionEnvironment {
  override def isModuleLevel = true
  override def isVerificationContext = true
}
case object AxiomEnvironment extends ExpressionEnvironment {
  override def isModuleLevel = true
  override def isVerificationContext = true
}

case class Scope (
    map: Scope.IdentifierMap, module : Option[Module], procedure : Option[ProcedureDecl], cmd : Option[GenericProofCommand],
    environment : ExpressionEnvironment, inLTLSpec : Boolean)
{
  /** Check if a variable name exists in this context. */
  def doesNameExist(name: Identifier) = map.contains(name)
  /** Check if a variable is read-only. */
  def isNameReadOnly(name: Identifier) = {
    map.get(name) match {
      case Some(namedExpr) => namedExpr.isReadOnly
      case None => true
    }
  }
  /** Return the NamedExpression. */
  def get(id: Identifier) : Option[Scope.NamedExpression] = map.get(id)
  /** Does procedure exist? */
  def doesProcedureExist(id : Identifier) : Boolean = {
    map.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.Procedure(pId, typ) => true
          case _ => false
        }
      case None => false
    }
  }

  /** Return the filename. */
  def filename : Option[String] = {
    module.flatMap((m) => m.filename)
  }
  lazy val inputs = map.filter(_._2.isInstanceOf[Scope.InputVar]).map(_._2.asInstanceOf[Scope.InputVar]).toSet
  lazy val vars = map.filter(_._2.isInstanceOf[Scope.StateVar]).map(_._2.asInstanceOf[Scope.StateVar]).toSet
  lazy val outputs = map.filter(_._2.isInstanceOf[Scope.OutputVar]).map(_._2.asInstanceOf[Scope.OutputVar]).toSet
  lazy val specs = map.filter(_._2.isInstanceOf[Scope.SpecVar]).map(_._2.asInstanceOf[Scope.SpecVar]).toSet
  lazy val moduleDefinitionMap = map.filter(_._2.isInstanceOf[Scope.ModuleDefinition]).map {
    d => {
      val moduleDefn = d._2.asInstanceOf[Scope.ModuleDefinition]
      (moduleDefn.id -> moduleDefn.mod)
    }
  }.toMap

  /** Return a new context with the inLTLSpec flag set. */
  def withLTLSpec : Scope = {
    Scope(map, module, procedure, cmd, environment, true)
  }
  /** Return new context with the inLTLSpec flag reset. */
  def withoutLTLSpec : Scope = {
    Scope(map, module, procedure, cmd, environment, false)
  }
  /** Return a new context with the inVerificationContext set. */
  def withEnvironment (vctx : ExpressionEnvironment) : Scope = {
    Scope(map, module, procedure, cmd, vctx, inLTLSpec)
  }
  /** Return a new context with this identifier added to the current context. */
  def +(expr: Scope.NamedExpression) : Scope = {
    Scope(map + (expr.id -> expr), module, procedure, cmd, environment, inLTLSpec)
  }
  def +(typ : Type) : Scope = {
    Scope(Scope.addTypeToMap(map, typ, module), module, procedure, cmd, environment, inLTLSpec)
  }

  /** Add a reference to this module (don't expand the module's declarations). */
  def +&(m : Module) : Scope = {
    Scope(map + (m.id -> Scope.ModuleDefinition(m)), module, procedure, cmd, environment, inLTLSpec)
  }

  /** Return a new context with the declarations in this module added to it. */
  def +(m: Module) : Scope = {
    Utils.assert(module.isEmpty, "A module was already added to this Context.")
    val m1 = m.decls.foldLeft(map){ (mapAcc, decl) =>
      decl match {
        case instD : InstanceDecl =>
          Scope.addToMap(mapAcc, Scope.Instance(instD))
        case ProcedureDecl(id, sig, _, _, _, _, _) => Scope.addToMap(mapAcc, Scope.Procedure(id, sig.typ))
        case TypeDecl(id, typ) => Scope.addToMap(mapAcc, Scope.TypeSynonym(id, typ))
        case StateVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.StateVar(id, typ)))
        case InputVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.InputVar(id, typ)))
        case OutputVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.OutputVar(id, typ)))
        case SharedVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.SharedVar(id, typ)))
        case ConstantLitDecl(id, lit) => Scope.addToMap(mapAcc, Scope.ConstantLit(id, lit))
        case ConstantsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.ConstantVar(id, typ)))
        case GrammarDecl(id, sig, _) => Scope.addToMap(mapAcc, Scope.Grammar(id, sig.typ))
        case FunctionDecl(id, sig) => Scope.addToMap(mapAcc, Scope.Function(id, sig.typ))
        case SynthesisFunctionDecl(id, sig, _, _, _) => Scope.addToMap(mapAcc, Scope.Function(id, sig.typ)) // FIXME
        case DefineDecl(id, sig, expr) => Scope.addToMap(mapAcc, Scope.Define(id, sig.typ, DefineDecl(id, sig, expr)))
        case SpecDecl(id, expr, _) => Scope.addToMap(mapAcc, Scope.SpecVar(id, expr))
        case AxiomDecl(sId, expr) => sId match {
          case Some(id) => Scope.addToMap(mapAcc, Scope.AxiomVar(id, expr))
          case None => mapAcc
        }
        case InitDecl(_) | NextDecl(_) => mapAcc
      }
    }
    val m2 = m.decls.foldLeft(m1){(mapAcc, decl) =>
      decl match {
        case ProcedureDecl(id, sig, _, _, _, _, _) =>
          val m1 = sig.inParams.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = sig.outParams.foldLeft(m1)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          m2
        case FunctionDecl(id, sig) =>
          val m1 = sig.args.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = Scope.addTypeToMap(m1, sig.retType, Some(m))
          m2
        case GrammarDecl(id, sig, _) =>
          val m1 = sig.args.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = Scope.addTypeToMap(m1, sig.retType, Some(m))
          m2
        case SynthesisFunctionDecl(id, sig, _, _, _) =>
          val m1 = sig.args.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = Scope.addTypeToMap(m1, sig.retType, Some(m))
          m2
        case DefineDecl(id, sig, _) =>
          val m1 = sig.args.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = Scope.addTypeToMap(m1, sig.retType, Some(m))
          m2
        case TypeDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case StateVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case InputVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case OutputVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case SharedVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case ConstantLitDecl(id, lit) => Scope.addTypeToMap(mapAcc, lit.typeOf, Some(m))
        case ConstantsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case InstanceDecl(_, _, _, _, _) | SpecDecl(_, _, _) | AxiomDecl(_, _) | InitDecl(_) | NextDecl(_) => mapAcc
      }
    }
    Scope(m2, Some(m), None, None, environment, false)
  }
  /** Return a new context with the declarations in this procedure added to it. */
  def +(proc: ProcedureDecl) : Scope = {
    Utils.assert(procedure.isEmpty, "A procedure was already added to this context.")
    val map1 = proc.sig.inParams.foldLeft(map){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureInputArg(arg._1, arg._2))
    }
    val map2 = proc.sig.outParams.foldLeft(map1){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureOutputArg(arg._1, arg._2))
    }
    val map3 = proc.decls.foldLeft(map2){
      (mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ProcedureLocalVar(arg.id, arg.typ))
    }
    return Scope(map3, module, Some(proc), None, ProceduralEnvironment, false)
  }
  /** Return a new context with the declarations in this lambda expression added to it. */
  def +(lambda: Lambda) : Scope = {
    val newMap = lambda.ids.foldLeft(map){
      (mapAcc, id) => Scope.addToMap(mapAcc, Scope.LambdaVar(id._1, id._2))
    }
    return Scope(newMap, module, procedure, cmd, environment, inLTLSpec)
  }
  /** Return a new context with the function's arguments included. */
  def +(sig : FunctionSig) : Scope = {
    val newMap = sig.args.foldLeft(map){
      (mapAcc, id) => Scope.addToMap(mapAcc, Scope.FunctionArg(id._1, id._2))
    }
    return Scope(newMap, module, procedure, cmd, environment, inLTLSpec)
  }
  /** Return a new context with quantifier variables added. */
  def +(opapp : OperatorApplication) : Scope = {
    this + (opapp.op)
  }
  /** Return a new context with the quantifier variables adder. */
  def +(op : Operator) : Scope = {
    op match {
      case ForallOp(vs) =>
        Scope(
          vs.foldLeft(map)((mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ForallVar(arg._1, arg._2))),
          module, procedure, cmd, environment, inLTLSpec)
      case ExistsOp(vs) =>
        Scope(
          vs.foldLeft(map)((mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ForallVar(arg._1, arg._2))),
          module, procedure, cmd, environment, inLTLSpec)
      case _ => this
    }
  }
  /** Return a new context for this block. */
  def +(vars : List[BlockVarsDecl]) : Scope = {
    val declaredVars = vars.flatMap(vs => vs.ids.map(v => (v, vs.typ)))
    val mapP = declaredVars.foldLeft(map)((mapAcc, arg) => Scope.addToMap(mapAcc, Scope.BlockVar(arg._1, arg._2)))
    Scope(mapP, module, procedure, cmd, environment, inLTLSpec)
  }

  /** Return a new context for this command. */
  def +(command : GenericProofCommand) : Scope = {
    val mapP = command.resultVar match {
      case Some(id) => map + (id -> Scope.VerifResultVar(id, command))
      case None => map
    }
    Scope(mapP, module, procedure, Some(command), environment, inLTLSpec)
  }
  /** Return the type of an identifier in this context. */
  def typeOf(id : Identifier) : Option[Type] = {
    map.get(id).flatMap((e) => Some(e.typ))
  }

  def isQuantifierVar(id : Identifier) : Boolean = {
    (map.get(id).flatMap{
      (p) => p match {
        case Scope.ForallVar(_, _) | Scope.ExistsVar(_, _) => Some(true)
        case _ => Some(false)
      }
    }) match {
      case Some(t) => t
      case None => false
    }
  }
}

class ContextualNameProvider(prefix : String) {
  var names : MutableSet[Identifier] = MutableSet.empty
  def toName(name : Identifier, tag : String, index : Option[Int]) : Identifier = {
    val nameP = (prefix, tag) match {
      case ("", "") => name.toString()
      case ("", tg) => name.toString() + "__" + tg
      case (pref, "") => prefix + "__" + name.toString()
      case (pref, tg) => prefix + "__" + name.toString() + "__" + tag
    }
    val nameQ : String = index match {
      case Some(i) => nameP + "__" + i.toString()
      case None => nameP
    }
    Identifier(nameQ)
  }
  def apply(ctx : Scope, name: Identifier, tag : String) : Identifier = {
    var newId = toName(name, tag, None)
    var index = 1
    while (ctx.doesNameExist(newId) || names.contains(newId)) {
      newId = toName(name, tag, Some(index))
      index = index + 1
    }
    names.add(newId)
    return newId
  }
}