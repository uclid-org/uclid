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
 * Authors: Pramod Subramanyan

 * Finds Stateless axioms and imports them.
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger

/**
  * StatelessAxiomFinder: finds all axioms that do not refer to state variables,
  * inputs or outputs and collects them for instantiation in the main module.
  *
  * The List[(Identifier, AxiomDecl)] accumulates the axioms and the
  * names of the modules the axioms come from.
  *
  * The Boolean is used to turn off the instantiation for modules that appear
  * after the main module. See test-extid-axiom.ucl for more details.
  *
  * @param mainModuleName is the name of the main module.
  */
class StatelessAxiomFinderPass(mainModuleName: Identifier)
  extends ReadOnlyPass[(Boolean, List[(Identifier, AxiomDecl)])]
{
  lazy val logger = Logger(classOf[StatelessAxiomFinderPass])

  type T = (Boolean, List[(Identifier, AxiomDecl)])
  def isStatelessExpression(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)    | Scope.InputVar(_, _)  |
               Scope.OutputVar(_, _)   | Scope.SharedVar(_, _) |
               Scope.FunctionArg(_, _) | Scope.Define(_, _, _) |
               Scope.Instance(_)       | Scope.Group(_, _, _)       =>
             false
          case Scope.ConstantVar(_, _)    | Scope.Function(_, _)       |
               Scope.LambdaVar(_ , _)     | Scope.ForallVar(_, _)      |
               Scope.ExistsVar(_, _)      | Scope.EnumIdentifier(_, _) |
               Scope.OracleFunction(_,_,_) |
               Scope.ConstantLit(_, _)    | Scope.SynthesisFunction(_, _, _, _, _) |
               Scope.GroupVar(_, _) =>
             true
          case Scope.ModuleDefinition(_)      | Scope.Grammar(_, _, _)          |
               Scope.TypeSynonym(_, _)        | Scope.Procedure(_, _)           |
               Scope.ProcedureInputArg(_ , _) | Scope.ProcedureOutputArg(_ , _) |
               Scope.ForIndexVar(_ , _)       | Scope.SpecVar(_ , _, _)         |
               Scope.AxiomVar(_ , _, _)       | Scope.VerifResultVar(_, _)      |
               Scope.BlockVar(_, _)           | Scope.SelectorField(_)          |
               Scope.NonTerminal(_, _, _)     | Scope.Macro(_, _, _)           =>
             throw new Utils.RuntimeError("Can't have this identifier in assertion: " + namedExpr.toString())
        }
      case None =>
        throw new Utils.RuntimeError("Unknown identifiers should have been detected by now.")
    }
  }
  def isStatelessExpr(e: Expr, context : Scope) : Boolean = {
    e match {
      case id : Identifier =>
        isStatelessExpression(id, context)
      case unit: UninterpretedTypeLiteral =>
        isStatelessExpression(unit.toIdentifier, context)
      case _ : ExternalIdentifier =>
        true
      case _ : Literal =>
        true
      case rec : Tuple =>
        rec.values.forall(e => isStatelessExpr(e, context))
      case OperatorApplication(ArraySelect(inds), args) =>
        inds.forall(ind => isStatelessExpr(ind, context)) &&
        args.forall(arg => isStatelessExpr(arg, context))
      case OperatorApplication(ArrayUpdate(inds, value), args) =>
        inds.forall(ind => isStatelessExpr(ind, context)) &&
        args.forall(arg => isStatelessExpr(arg, context)) &&
        isStatelessExpr(value, context)
      case OperatorApplication(RecordUpdate(id, expr), args) =>
        isStatelessExpr(expr, context) &&
        args.forall(a => isStatelessExpr(a, context))
      case OperatorApplication(FiniteForallOp(_, gId), _) =>
        val opapp = e.asInstanceOf[OperatorApplication]
        isStatelessExpr(gId, context) &&
        opapp.operands.forall(arg => isStatelessExpr(arg, context + opapp.op))
      case OperatorApplication(FiniteExistsOp(_, gId), _) =>
        val opapp = e.asInstanceOf[OperatorApplication]
        isStatelessExpr(gId, context) &&
        opapp.operands.forall(arg => isStatelessExpr(arg, context + opapp.op))
      case opapp : OperatorApplication =>
        opapp.operands.forall(arg => isStatelessExpr(arg, context + opapp.op))
      case a : ConstArray =>
        isStatelessExpr(a.exp, context)
      case r : ConstRecord => 
        r.fieldvalues.forall(f => isStatelessExpr(f._2, context))
      case fapp : FuncApplication =>
        isStatelessExpr(fapp.e, context) && fapp.args.forall(a => isStatelessExpr(a, context))
      case lambda : Lambda =>
        isStatelessExpr(lambda.e, context + lambda)
      case QualifiedIdentifier(_, _) | IndexedIdentifier(_, _) | QualifiedIdentifierApplication(_, _) => 
        throw new Utils.UnimplementedException("ERROR: SMT expr generation for QualifiedIdentifier and IndexedIdentifier is currently not supported")
      case LetExpr(_, _) => 
        throw new Utils.UnimplementedException("ERROR: SMT expr generation for LetExpr is currently not supported")
    }
  }
  def rewriteIdentifierToExternalId(moduleName : Identifier, id : Identifier, context : Scope) : Expr = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)           | Scope.InputVar(_, _)            |
               Scope.OutputVar(_, _)          | Scope.SharedVar(_, _)           |
               Scope.ModuleDefinition(_)      | Scope.Instance(_)               |
               Scope.TypeSynonym(_, _)        | Scope.Procedure(_, _)           |
               Scope.ProcedureInputArg(_ , _) | Scope.ProcedureOutputArg(_ , _) |
               Scope.SpecVar(_ , _, _)        | Scope.AxiomVar(_ , _, _)        |
               Scope.LambdaVar(_ , _)         | Scope.ForallVar(_, _)           |
               Scope.ExistsVar(_, _)          | Scope.EnumIdentifier(_, _)      |
               Scope.VerifResultVar(_, _)     | Scope.FunctionArg(_, _)         |
               Scope.Define(_, _, _)          | Scope.Grammar(_, _, _)          |
               Scope.ConstantLit(_, _)        | Scope.BlockVar(_, _)            |
               Scope.ForIndexVar(_ , _)       | Scope.SelectorField(_)          |
               Scope.NonTerminal(_, _, _)     | Scope.Macro(_, _, _)            |
               Scope.Group(_, _, _)           | Scope.GroupVar(_, _)           =>
              id
          case Scope.ConstantVar(_, _)    | Scope.Function(_, _)  | Scope.OracleFunction(_,_,_) | Scope.SynthesisFunction(_, _, _, _, _) =>
             ExternalIdentifier(moduleName, id)
        }
      case None =>
        throw new Utils.RuntimeError("Unknown identifiers should have been detected by now.")
    }
  }
  def rewriteToExternalIds(moduleName : Identifier, e : Expr, context : Scope) : Expr = {
    def rewrite(e : Expr, ctx : Scope) = rewriteToExternalIds(moduleName, e, ctx)
    e match {
      case id : Identifier =>
        rewriteIdentifierToExternalId(moduleName, id, context)
      case unit: UninterpretedTypeLiteral =>
        rewriteIdentifierToExternalId(moduleName, unit.toIdentifier, context)
      case ei : ExternalIdentifier =>
        ei
      case lit : Literal =>
        lit
      case rec : Tuple =>
        val valuesP = rec.values.map(rewrite(_, context))
        Tuple(valuesP)
      case OperatorApplication(ArraySelect(inds), es) =>
        val indsP = inds.map(ind => rewrite(ind, context))
        val esP = es.map(e => rewrite(e, context))
        OperatorApplication(ArraySelect(indsP), esP)
      case OperatorApplication(ArrayUpdate(inds, value), es) =>
        val indsP = inds.map(ind => rewrite(ind, context))
        val esP = es.map(e => rewrite(e, context))
        val valueP = rewrite(value, context)
        OperatorApplication(ArrayUpdate(indsP, valueP), esP)
      case OperatorApplication(RecordUpdate(id, expr), es) =>
        val esP = es.map(e => rewrite(e, context))
        val exprP = rewrite(expr, context)
        OperatorApplication(RecordUpdate(id, exprP), esP)
      case opapp : OperatorApplication =>
        val operandsP = opapp.operands.map(arg => rewrite(arg, context + opapp.op))
        OperatorApplication(opapp.op, operandsP)
      case a : ConstArray =>
        val eP = rewrite(a.exp, context)
        ConstArray(eP, a.typ)
      case r : ConstRecord =>
        val fsP = r.fieldvalues.map(f => (f._1, rewrite(f._2, context)))
        ConstRecord(fsP)
      case fapp : FuncApplication =>
        val eP = rewrite(fapp.e, context)
        val argsP = fapp.args.map(rewrite(_, context))
        FuncApplication(eP, argsP)
      case lambda : Lambda =>
        val expP = rewrite(lambda.e, context + lambda)
        Lambda(lambda.ids, expP)
      case _ : QualifiedIdentifier | _ : IndexedIdentifier | _ : QualifiedIdentifierApplication => throw new Utils.UnimplementedException("ERROR: QualifiedIdentifier and IndexedIdentifier are currently not supported")
      case _ : LetExpr => 
        throw new Utils.UnimplementedException("ERROR: SMT expr generation for LetExpr is currently not supported")
    }
  }
  override def applyOnModule(d : TraversalDirection.T, module: Module, in : T, context : Scope) : T = {
    logger.debug("visiting: %s".format(module.id.toString()))
    if (d == TraversalDirection.Up && module.id == mainModuleName) {
      (false, in._2)
    } else {
      in
    }
  }
  override def applyOnAxiom(d : TraversalDirection.T, axiom : AxiomDecl, in : T, context : Scope) : T = {
    if (in._1 && d == TraversalDirection.Down && isStatelessExpr(axiom.expr, context)) {
      logger.debug("Making a new axiom for %s %s".format(axiom.expr.toString, axiom.params.toString))
      val moduleName = context.module.get.id
      val exprP = rewriteToExternalIds(moduleName, axiom.expr, context)
      val name = axiom.id match {
        case Some(id) => "_" + id.toString()
        case None => ""
      }
      val nameP = Identifier("$axiom_" + moduleName.toString + name + "_" + in._2.size.toString)
      val axiomP = AxiomDecl(Some(nameP), exprP, axiom.params)
      (in._1, (moduleName, axiomP) :: in._2)
    } else {
      in
    }
  }
}

class StatelessAxiomFinder(mainModuleName: Identifier) extends ASTAnalyzer(
    "StatelessAxiomFinder", new StatelessAxiomFinderPass(mainModuleName))
{
  override def reset() {
    in = Some((true, List.empty))
  }
}

class StatelessAxiomImporterPass(mainModuleName : Identifier) extends RewritePass
{
  lazy val manager : PassManager = analysis.manager
  lazy val statelessAxiomFinder = manager.pass("StatelessAxiomFinder").asInstanceOf[StatelessAxiomFinder]
  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    if (module.id == mainModuleName) {
    val axioms = statelessAxiomFinder.out.get._2
      val otherModuleAxioms = axioms.filter(p => p._1 != mainModuleName).map(p => p._2)
      val declsP = otherModuleAxioms ++ module.decls
      val moduleP = Module(module.id, declsP, module.cmds, module.notes)
      Some(moduleP)
    } else {
      Some(module)
    }
  }
}

class StatelessAxiomImporter(mainModuleName : Identifier) extends ASTRewriter(
    "StatelessAxiomImporter", new StatelessAxiomImporterPass(mainModuleName))
