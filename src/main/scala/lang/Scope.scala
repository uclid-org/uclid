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
  case class Instance(instId : Identifier, moduleId : Identifier, modTyp : Type) extends ReadOnlyNamedExpression(instId, modTyp)
  case class TypeSynonym(typId : Identifier, sTyp: Type) extends ReadOnlyNamedExpression(typId, sTyp)
  case class StateVar(varId : Identifier, varTyp: Type) extends NamedExpression(varId, varTyp)
  case class InputVar(inpId : Identifier, inpTyp: Type) extends ReadOnlyNamedExpression(inpId, inpTyp)
  case class OutputVar(outId : Identifier, outTyp: Type) extends NamedExpression(outId, outTyp)
  case class SharedVar(varId : Identifier, varTyp : Type) extends NamedExpression(varId, varTyp)
  case class ConstantVar(cId : Identifier, cTyp : Type) extends ReadOnlyNamedExpression(cId, cTyp)
  case class Function(fId : Identifier, fTyp: Type) extends ReadOnlyNamedExpression(fId, fTyp)
  case class Procedure(pId : Identifier, pTyp: Type) extends ReadOnlyNamedExpression(pId, pTyp)
  case class ProcedureInputArg(argId : Identifier, argTyp: Type) extends ReadOnlyNamedExpression(argId, argTyp)
  case class ProcedureOutputArg(argId : Identifier, argTyp: Type) extends NamedExpression(argId, argTyp)
  case class ProcedureLocalVar(vId : Identifier, vTyp : Type) extends NamedExpression(vId, vTyp)
  case class LambdaVar(vId : Identifier, vTyp : Type) extends ReadOnlyNamedExpression(vId, vTyp)
  case class ForIndexVar(iId : Identifier, iTyp : Type) extends ReadOnlyNamedExpression(iId, iTyp)
  case class SpecVar(varId : Identifier, expr: Expr) extends ReadOnlyNamedExpression(varId, BoolType())
  case class AxiomVar(varId : Identifier, expr : Expr) extends ReadOnlyNamedExpression(varId, BoolType())
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
                      "Identifier " + eId.name + " redeclared as a member of a different enum.",
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
      case _ =>
        map
    }
  }
  /** Create an empty context. */
  def empty : Scope = Scope(Map.empty[Identifier, Scope.NamedExpression], None, None, None, ComputeContext, false)
}

sealed abstract class ExpressionContext
case object ComputeContext extends ExpressionContext
case object RequiresContext extends ExpressionContext
case object EnsuresContext extends ExpressionContext
case object AssertContext extends ExpressionContext
case object AssumeContext extends ExpressionContext
case object SpecContext extends ExpressionContext
case object AxiomContext extends ExpressionContext

case class Scope (
    map: Scope.IdentifierMap, module : Option[Module], procedure : Option[ProcedureDecl], cmd : Option[GenericProofCommand], 
    inVerificationContext : ExpressionContext, inLTLSpec : Boolean) 
{
  /** Check if a variable name exists in this context. */
  def doesNameExist(name: Identifier) = map.contains(name)
  /** Check if a variable is readonly. */
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
    Scope(map, module, procedure, cmd, inVerificationContext, true)
  }
  /** Return new context with the inLTLSpec flag reset. */
  def withoutLTLSpec : Scope = {
    Scope(map, module, procedure, cmd, inVerificationContext, false)
  }
  /** Return a new context with the inVerificationContext set. */
  def withVerificationContext (vctx : ExpressionContext) : Scope = {
    Scope(map, module, procedure, cmd, vctx, inLTLSpec)
  }
  /** Return a new context with this identifier added to the current context. */
  def +(expr: Scope.NamedExpression) : Scope = {
    Scope(map + (expr.id -> expr), module, procedure, cmd, inVerificationContext, inLTLSpec)
  }
  def +(typ : Type) : Scope = {
    Scope(Scope.addTypeToMap(map, typ, module), module, procedure, cmd, inVerificationContext, inLTLSpec)
  }

  /** Add a reference to this module (don't expand the module's declarations). */
  def +&(m : Module) : Scope = {
    Scope(map + (m.id -> Scope.ModuleDefinition(m)), module, procedure, cmd, inVerificationContext, inLTLSpec)
  }

  /** Return a new context with the declarations in this module added to it. */
  def +(m: Module) : Scope = {
    Utils.assert(module.isEmpty, "A module was already added to this Context.")
    val m1 = m.decls.foldLeft(map){ (mapAcc, decl) =>
      decl match {
        case instD : InstanceDecl =>
          Scope.addToMap(mapAcc, Scope.Instance(instD.instanceId, instD.moduleId, instD.moduleType))
        case ProcedureDecl(id, sig, _, _, _, _, _) => Scope.addToMap(mapAcc, Scope.Procedure(id, sig.typ))
        case TypeDecl(id, typ) => Scope.addToMap(mapAcc, Scope.TypeSynonym(id, typ))
        case StateVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.StateVar(id, typ)))
        case InputVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.InputVar(id, typ)))
        case OutputVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.OutputVar(id, typ)))
        case SharedVarsDecl(ids, typ) => ids.foldLeft(mapAcc)((acc, id) => Scope.addToMap(acc, Scope.SharedVar(id, typ)))
        case ConstantDecl(id, typ) => Scope.addToMap(mapAcc, Scope.ConstantVar(id, typ))
        case FunctionDecl(id, sig) => Scope.addToMap(mapAcc, Scope.Function(id, sig.typ))
        case SynthesisFunctionDecl(id, sig, _, _, _) => Scope.addToMap(mapAcc, Scope.Function(id, sig.typ))
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
        case SynthesisFunctionDecl(id, sig, _, _, _) =>
          val m1 = sig.args.foldLeft(mapAcc)((mapAcc2, operand) => Scope.addTypeToMap(mapAcc2, operand._2, Some(m)))
          val m2 = Scope.addTypeToMap(m1, sig.retType, Some(m))
          m2
        case TypeDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case StateVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case InputVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case OutputVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case SharedVarsDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case ConstantDecl(id, typ) => Scope.addTypeToMap(mapAcc, typ, Some(m))
        case InstanceDecl(_, _, _, _, _) | SpecDecl(_, _, _) | AxiomDecl(_, _) | InitDecl(_) | NextDecl(_) => mapAcc
      }
    }
    Scope(m2, Some(m), None, None, inVerificationContext, false)
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
    return Scope(map3, module, Some(proc), None, inVerificationContext, false)
  }
  /** Return a new context with the declarations in this lambda expression added to it. */
  def +(lambda: Lambda) : Scope = {
    val newMap = lambda.ids.foldLeft(map){
      (mapAcc, id) => Scope.addToMap(mapAcc, Scope.LambdaVar(id._1, id._2))
    }
    return Scope(newMap, module, procedure, cmd, inVerificationContext, inLTLSpec)
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
          module, procedure, cmd, inVerificationContext, inLTLSpec)
      case ExistsOp(vs) =>
        Scope(
          vs.foldLeft(map)((mapAcc, arg) => Scope.addToMap(mapAcc, Scope.ForallVar(arg._1, arg._2))),
          module, procedure, cmd, inVerificationContext, inLTLSpec)
      case _ => this
    }
  }

  /** Return a new context for this command. */
  def +(command : GenericProofCommand) : Scope = {
    val mapP = command.resultVar match {
      case Some(id) => map + (id -> Scope.VerifResultVar(id, command))
      case None => map
    }
    Scope(mapP, module, procedure, Some(command), inVerificationContext, inLTLSpec)
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

class ContextualNameProvider(ctx : Scope, prefix : String) {
  var index = 1
  def apply(name: Identifier, tag : String) : Identifier = {
    var newId = Identifier(prefix + "$" + tag + "$" + name + "_" + index.toString)
    index = index + 1
    while (ctx.doesNameExist(newId)) {
      newId = Identifier(prefix + "$" + tag + "$" + name + "_" + index.toString)
      index = index + 1
    }
    return newId
  }
}