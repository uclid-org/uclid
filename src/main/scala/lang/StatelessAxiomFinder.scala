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
          case Scope.StateVar(_, _)    | Scope.InputVar(_, _)  |
               Scope.OutputVar(_, _)   | Scope.SharedVar(_, _) |
               Scope.FunctionArg(_, _) | Scope.Define(_, _, _) |
               Scope.Instance(_)       =>
             false
          case Scope.ConstantVar(_, _)    | Scope.Function(_, _)       |
               Scope.LambdaVar(_ , _)     | Scope.ForallVar(_, _)      |
               Scope.ExistsVar(_, _)      | Scope.EnumIdentifier(_, _) |
               Scope.ConstantLit(_, _)    =>
             true
          case Scope.ModuleDefinition(_)      | Scope.Grammar(_, _)             |
               Scope.TypeSynonym(_, _)        | Scope.Procedure(_, _)           |
               Scope.ProcedureInputArg(_ , _) | Scope.ProcedureOutputArg(_ , _) |
               Scope.ProcedureLocalVar(_ , _) | Scope.ForIndexVar(_ , _)        |
               Scope.SpecVar(_ , _)           | Scope.AxiomVar(_ , _)           |
               Scope.VerifResultVar(_, _)     | Scope.BlockVar(_, _)            =>
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
      case lambda : Lambda =>
        isStatelessExpr(lambda.e, context + lambda)
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
               Scope.ProcedureLocalVar(_ , _) | Scope.ForIndexVar(_ , _)        |
               Scope.SpecVar(_ , _)           | Scope.AxiomVar(_ , _)           |
               Scope.LambdaVar(_ , _)         | Scope.ForallVar(_, _)           |
               Scope.ExistsVar(_, _)          | Scope.EnumIdentifier(_, _)      |
               Scope.VerifResultVar(_, _)     | Scope.FunctionArg(_, _)         |
               Scope.Define(_, _, _)          | Scope.Grammar(_, _)             |
               Scope.ConstantLit(_, _)        | Scope.BlockVar(_, _)            =>
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
      val moduleP = Module(module.id, declsP, module.cmds, module.notes)
      Some(moduleP)
    } else {
      Some(module)
    }
  }
}

class StatelessAxiomImporter(mainModuleName : Identifier) extends ASTRewriter(
    "StatelessAxiomImporter", new StatelessAxiomImporterPass(mainModuleName))
