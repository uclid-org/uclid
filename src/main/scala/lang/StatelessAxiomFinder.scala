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
 * Authors: Norman Mu, Pramod Subramanyan

 * All sorts of type inference and type checking functionality is in here.
 *
 */

package uclid
package lang

class StatelessAxiomFinderPass extends ReadOnlyPass[List[AxiomDecl]] {
  def isStatelessExpression(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)  | 
               Scope.InputVar(_, _)  | 
               Scope.OutputVar(_, _) => false

          case Scope.ConstantVar(_, _) | 
               Scope.Function(_, _)    | 
               Scope.LambdaVar(_ , _)  |
               Scope.ForallVar(_, _)   | 
               Scope.ExistsVar(_, _)   => true

          case Scope.ModuleDefinition(_)        |
               Scope.Instance(_, _, _)          | 
               Scope.TypeSynonym(_, _)          |
               Scope.Procedure(_, _)            | 
               Scope.ProcedureInputArg(_ , _)   | 
               Scope.ProcedureOutputArg(_ , _)  |
               Scope.ProcedureLocalVar(_ , _)   |
               Scope.ForIndexVar(_ , _)         | 
               Scope.SpecVar(_ , _)             | 
               Scope.AxiomVar(_ , _)            => throw new Utils.RuntimeError("Should never get here.") 
        }
    }
  }
  def isStatelessExpr(e: Expr, context : Scope) : Boolean = {
    e match {
      case id : Identifier =>
        isStatelessExpression(id, context)
      case ei : ExternalIdentifier => 
        true
      case lit : Literal => 
        false
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
}
