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
 * Authors: Pramod Subramanyan

 * All sorts of type inference and type checking functionality is in here.
 *
 */

package uclid
package lang

class StatelessAxiomFinderPass extends ReadOnlyPass[List[(Identifier, AxiomDecl)]] {
  def isStatelessExpression(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)  | Scope.InputVar(_, _)  | Scope.OutputVar(_, _) => 
             false
          case Scope.ConstantVar(_, _)    | Scope.Function(_, _)       |
               Scope.LambdaVar(_ , _)     | Scope.ForallVar(_, _)      |
               Scope.ExistsVar(_, _)      | Scope.EnumIdentifier(_, _) => 
             true
          case Scope.ModuleDefinition(_)        | Scope.Instance(_, _, _)          | 
               Scope.TypeSynonym(_, _)          | Scope.Procedure(_, _)            | 
               Scope.ProcedureInputArg(_ , _)   | Scope.ProcedureOutputArg(_ , _)  |
               Scope.ProcedureLocalVar(_ , _)   | Scope.ForIndexVar(_ , _)         | 
               Scope.SpecVar(_ , _)             | Scope.AxiomVar(_ , _)            => 
             throw new Utils.RuntimeError("Can't have this identifier in assertion.") 
        }
      case None =>
        throw new Utils.RuntimeError("Unknown identifiers should have been detected by now.")
    }
  }
  def isStatelessExpr(e: Expr, context : Scope) : Boolean = {
    e match {
      case id : Identifier =>
        isStatelessExpression(id, context)
      case ei : ExternalIdentifier => 
        true
      case lit : Literal => 
        true
      case rec : Tuple =>
        rec.values.forall(e => isStatelessExpr(e, context))
      case opapp : OperatorApplication =>
        opapp.operands.forall(arg => isStatelessExpr(arg, context + opapp.op))
      case arrSel : ArraySelectOperation =>
        isStatelessExpr(arrSel.e, context) && arrSel.index.forall(i => isStatelessExpr(i, context))
      case arrUpd : ArrayStoreOperation =>
        isStatelessExpr(arrUpd.e, context) && 
        arrUpd.index.forall(i => isStatelessExpr(i, context)) &&
        isStatelessExpr(arrUpd.value, context)
      case fapp : FuncApplication =>
        isStatelessExpr(fapp.e, context) && fapp.args.forall(a => isStatelessExpr(a, context))
      case ite : ITE =>
        isStatelessExpr(ite.e, context) && isStatelessExpr(ite.t, context) && isStatelessExpr(ite.f, context)
      case lambda : Lambda =>
        isStatelessExpr(lambda.e, context + lambda)
    }
  }
  def rewriteIdentifierToExternalId(moduleName : Identifier, id : Identifier, context : Scope) : Expr = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)  | Scope.InputVar(_, _)  | Scope.OutputVar(_, _) | 
               Scope.ModuleDefinition(_)        | Scope.Instance(_, _, _)            | 
               Scope.TypeSynonym(_, _)          | Scope.Procedure(_, _)              | 
               Scope.ProcedureInputArg(_ , _)   | Scope.ProcedureOutputArg(_ , _)    |
               Scope.ProcedureLocalVar(_ , _)   | Scope.ForIndexVar(_ , _)           | 
               Scope.SpecVar(_ , _)             | Scope.AxiomVar(_ , _)              |
               Scope.LambdaVar(_ , _)           | Scope.ForallVar(_, _)              |
               Scope.ExistsVar(_, _)            | Scope.EnumIdentifier(_, _) => 
              id
          case Scope.ConstantVar(_, _)    | Scope.Function(_, _) =>
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
      case ei : ExternalIdentifier => 
        ei
      case lit : Literal => 
        lit
      case rec : Tuple =>
        val valuesP = rec.values.map(rewrite(_, context))
        Tuple(valuesP)
      case opapp : OperatorApplication =>
        val operandsP = opapp.operands.map(arg => rewrite(arg, context + opapp.op))
        OperatorApplication(opapp.op, operandsP)
      case arrSel : ArraySelectOperation =>
        val eP = rewrite(arrSel.e, context)
        val indicesP = arrSel.index.map(i => rewrite(i, context))
        ArraySelectOperation(eP, indicesP)
      case arrUpd : ArrayStoreOperation =>
        val eP = rewrite(arrUpd.e, context)
        val indicesP = arrUpd.index.map(i => rewrite(i, context))
        val valueP = rewrite(arrUpd.value, context)
        ArrayStoreOperation(eP, indicesP, valueP)
      case fapp : FuncApplication =>
        val eP = rewrite(fapp.e, context)
        val argsP = fapp.args.map(rewrite(_, context))
        FuncApplication(eP, argsP)
      case ite : ITE =>
        val condP = rewrite(ite.e, context)
        val tExpP = rewrite(ite.t, context)
        val fExpP = rewrite(ite.f, context)
        ITE(condP, tExpP, fExpP)
      case lambda : Lambda =>
        val expP = rewrite(lambda.e, context + lambda)
        Lambda(lambda.ids, expP)
    }
  }
  override def applyOnAxiom(d : TraversalDirection.T, axiom : AxiomDecl, in : List[(Identifier, AxiomDecl)], context : Scope) : List[(Identifier, AxiomDecl)] = {
    if (d == TraversalDirection.Down && isStatelessExpr(axiom.expr, context)) {
      val moduleName = context.module.get.id
      val exprP = rewriteToExternalIds(moduleName, axiom.expr, context)
      val name = axiom.id match {
        case Some(id) => "_" + id.toString()
        case None => ""
      }
      val nameP = Identifier("$axiom_" + moduleName.toString + name + "_" + in.size.toString)
      val axiomP = AxiomDecl(Some(nameP), exprP)
      (moduleName, axiomP) :: in
    } else {
      in
    }
  }
}

class StatelessAxiomFinder extends ASTAnalyzer("StatelessAxiomFinder", new StatelessAxiomFinderPass()) {
  override def reset() {
    in = Some(List.empty)
  }
  override def finish() {
    // val axioms = out.get
    // axioms.foreach(p => println(p._1.toString + " --> " + p._2.toString))
  }
}

class StatelessAxiomImporterPass(mainModuleName : Identifier) extends RewritePass
{
  lazy val manager : PassManager = analysis.manager
  lazy val statelessAxiomFinder = manager.pass("StatelessAxiomFinder").asInstanceOf[StatelessAxiomFinder]
  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    if (module.id == mainModuleName) {
      val axioms = statelessAxiomFinder.out.get
      val otherModuleAxioms = axioms.filter(p => p._1 != mainModuleName).map(p => p._2)
      val declsP = otherModuleAxioms ++ module.decls
      val moduleP = Module(module.id, declsP, module.cmds)
      Some(moduleP)
    } else {
      Some(module)
    }
  }
}

class StatelessAxiomImporter(mainModuleName : Identifier) extends ASTRewriter(
    "StatelessAxiomImporter", new StatelessAxiomImporterPass(mainModuleName))