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
 * Compute the types of each module that is referenced in an instance declaration.
 *
 */
package uclid
package lang


class LTLOperatorArgumentCheckerPass extends ReadOnlyPass[Set[ModuleError]] {
  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  def checkBooleans(operands: List[Expr], context : Scope, in : T) : T = {
    var ret = in
    for (op <- operands) {
      var oType = exprTypeChecker.typeOf(op, context)
      if (!oType.isBool) {
        ret = ret + ModuleError("LTL operator expected argument of type boolean but received argument of type %s.".format(oType.toString), op.position)
      }
    }
    ret
  }
  override def applyOnFuncApp(d : TraversalDirection.T, fapp : FuncApplication, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      in
    } else {
      var ret = in
      fapp.e match {
        case Identifier(name : String) => name match {
          case "globally" =>
            var numOps = fapp.args.length
            if (numOps != 1) {
              ret = ret + ModuleError("globally operator expected 1 argument but received %s".format(numOps), fapp.position)
            }
          case "next" =>
            var numOps = fapp.args.length
            if (numOps != 1) {
              ret = ret + ModuleError("next operator expected 1 argument but received %s".format(numOps), fapp.position)
            }
          case "until" =>
            var numOps = fapp.args.length
            if (numOps != 2) {
              ret = ret + ModuleError("until operator expected 2 argument but received %s".format(numOps), fapp.position)
            }
          case "finally" =>
            var numOps = fapp.args.length
            if (numOps != 1) {
              ret = ret + ModuleError("finally operator expected 1 argument but received %s".format(numOps), fapp.position)
            }
          case _ => in
        }
          checkBooleans(fapp.args, context, ret)
      }
    }
  }
}

class LTLOperatorArgumentChecker extends ASTAnalyzer(
  "LTLOperatorArgumentChecker", new LTLOperatorArgumentCheckerPass())
{
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, Set.empty[ModuleError], context)
    if (out.nonEmpty) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    Some(module)
  }
}

class LTLOperatorRewriterPass extends RewritePass {

  override def rewriteFuncApp(fapp: FuncApplication, context: Scope): Option[Expr] = {
    if (context.inLTLSpec) {
      var top : TemporalOperator = null
      fapp.e match {
        case Identifier(name : String) => name match {
          case "globally" =>
            top = new GloballyTemporalOp
          case "next" =>
            top = new NextTemporalOp
          case "until" =>
            top = new UntilTemporalOp
          case "finally" =>
            top = new FinallyTemporalOp
          case "release" =>
            top = new ReleaseTemporalOp
          case _ =>
            Some(fapp)
        }
      }
      Some(OperatorApplication(top, fapp.args))
    } else {
      Some(fapp)
    }
  }
}

class LTLOperatorRewriter extends ASTRewriter("LTLOperatorRewriter", new LTLOperatorRewriterPass()) {
  override def visitSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
    val idP = visitIdentifier(spec.id, context)
    if (spec.params.contains(LTLExprDecorator)) {
      context.inLTLSpec = true
    }
    val exprP = visitExpr(spec.expr, context)
    context.inLTLSpec = false
    val decsP = spec.params.flatMap(visitExprDecorator(_, context))
    val specP = (idP, exprP) match {
      case (Some(id), Some(expr)) => pass.rewriteSpec(SpecDecl(id, expr, decsP), context)
      case _ => None
    }
    ASTNode.introducePos(_setFilename, specP, spec.position)
  }
}


class LTLNegatedNormalFormRewriterPass extends RewritePass {
  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    if (opapp.op.isInstanceOf[NegationOp]) {
      opapp.operands.head match {
        // !globally(a) -> finally(!a)
        case OperatorApplication(op : GloballyTemporalOp, operands) =>
          val negA = OperatorApplication(new NegationOp, List(operands.head))
          Some(OperatorApplication(new FinallyTemporalOp, List(negA)))
        // !next(a) -> next(!a)
        case OperatorApplication(op : NextTemporalOp, operands) =>
          val negA = OperatorApplication(new NegationOp, List(operands.head))
          Some(OperatorApplication(new NextTemporalOp, List(negA)))
        // !until(a, b) -> wuntil(!b, !a && !b)
        case OperatorApplication(op : UntilTemporalOp, operands) =>
          val negA = OperatorApplication(new NegationOp, List(operands.head))
          val negB = OperatorApplication(new NegationOp, List(operands.last))
          val conj = OperatorApplication(new ConjunctionOp, List(negA, negB))
          Some(OperatorApplication(new WUntilTemporalOp, List(negB, conj)))
        // !finally(a) -> globally(!a)
        case OperatorApplication(op : FinallyTemporalOp, operands) =>
          val negA = OperatorApplication(new NegationOp, List(operands.head))
          Some(OperatorApplication(new GloballyTemporalOp, List(negA)))
        // !release(a, b) -> wuntil(!a, !b) && finally(!b)
        case OperatorApplication(op : ReleaseTemporalOp, operands) =>
          val negA = OperatorApplication(new NegationOp, List(operands.head))
          val negB = OperatorApplication(new NegationOp, List(operands.last))
          val wu = OperatorApplication(new WUntilTemporalOp, List(negA, negB))
          val fin = OperatorApplication(new FinallyTemporalOp, List(negB))
          Some(OperatorApplication(new ConjunctionOp, List(wu, fin)))
      }
    }
    Some(opapp)
  }
}

class LTLNegatedNormalFormRewriter extends ASTRewriter(
  "LTLNegatedNormalFormRewriter", new LTLNegatedNormalFormRewriterPass())

// This pass is written under the assumption that inner expressions are visited before outer expressions.
// Thus we can recursively replace inner expressions with z_i variables
class LTLConjunctiveClauseRewriterPass extends RewritePass {
  var clauseCounter = 0
  var clauses = List[OperatorApplication]()

  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    if (context.inLTLSpec) {
      val ret = Identifier("z" + clauseCounter.toString)
      clauseCounter += 1
      val imp = OperatorApplication(new ImplicationOp, List(ret, opapp))
      // We store conjuncts involving temporal operators wrapped in a globally op
      if (opapp.op.isInstanceOf[TemporalOperator]) {
        clauses = OperatorApplication(new GloballyTemporalOp, List(imp)) :: clauses
      } else {
        // Implications on z_i variables are stored alongside other conjuncts but will be converted into assume stmts
        clauses = imp :: clauses
      }
      Some(ret)
    } else {
      Some(opapp)
    }
  }

  // We slightly abuse an Operator Application here to store all conjuncts in a single list
  override def rewriteSpec(spec: SpecDecl, context: Scope): Option[SpecDecl] = {
    if (context.inLTLSpec) {
      var conjuncts : List[Expr] = clauses
      clauses = List[OperatorApplication]()
      Some(SpecDecl(spec.id, OperatorApplication(new ConjunctionOp, conjuncts), spec.params))
    } else {
      Some(spec)
    }
  }
}

class LTLConjunctiveClauseRewriter extends ASTRewriter("LTLConjunctiveClauseRewriter", new LTLConjunctiveClauseRewriterPass()) {
  override def visitSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
    val idP = visitIdentifier(spec.id, context)
    if (spec.params.contains(LTLExprDecorator)) {
      context.inLTLSpec = true
    }
    val exprP = visitExpr(spec.expr, context)
    context.inLTLSpec = false
    val decsP = spec.params.flatMap(visitExprDecorator(_, context))
    val specP = (idP, exprP) match {
      case (Some(id), Some(expr)) => pass.rewriteSpec(SpecDecl(id, expr, decsP), context)
      case _ => None
    }
    ASTNode.introducePos(_setFilename, specP, spec.position)
  }
}


class LTLPropertyRewriterPass extends RewritePass {
  var specCounter = 0

  // Probably need to factor this into its own rewriter pass
  override def rewriteSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
    if (context.inLTLSpec) {
      val failed = Identifier("failed" concat specCounter.toString)
      specCounter += 1
      Some(SpecDecl(spec.id, OperatorApplication(new NegationOp, List(failed)), spec.params))
    } else {
      Some(spec)
    }
  }

  override def rewriteModule(module: Module, context: Scope): Option[Module] = {
    var decls = module.decls
    // Remove LTL SpecDecl
    val LTLSpecs = module.decls.filter(p => p.isInstanceOf[SpecDecl] && p.asInstanceOf[SpecDecl].params.contains(LTLExprDecorator))
    decls = decls.filter(p => !p.isInstanceOf[SpecDecl] || !p.asInstanceOf[SpecDecl].params.contains(LTLExprDecorator))

    // Add conjuncts properties
    for (s <- LTLSpecs) {
      var spec = s.asInstanceOf[SpecDecl]
      for (c <- spec.expr.asInstanceOf[OperatorApplication].operands) {
        c match {
          case OperatorApplication(op: GloballyTemporalOp, operands: List[Expr]) =>
            // convert implications G (zi => Xb) into assert statement circuits placed at beginning of next block
          case OperatorApplication(op: ImplicationOp, operands: List[Expr]) =>
            // convert implications zi => zk && zj into assume(zi => zk && zj) placed at the end of next block
          case _ =>
            // error case here?
        }
      }
    }
    Some(Module(module.id, decls, module.cmds))
  }
}

class LTLPropertyRewriter extends ASTRewriter("LTLPropertyRewriter", new LTLPropertyRewriterPass()) {
  override def visitSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
    val idP = visitIdentifier(spec.id, context)
    if (spec.params.contains(LTLExprDecorator)) {
      context.inLTLSpec = true
    }
    val exprP = visitExpr(spec.expr, context)
    context.inLTLSpec = false
    val decsP = spec.params.flatMap(visitExprDecorator(_, context))
    val specP = (idP, exprP) match {
      case (Some(id), Some(expr)) => pass.rewriteSpec(SpecDecl(id, expr, decsP), context)
      case _ => None
    }
    ASTNode.introducePos(_setFilename, specP, spec.position)
  }
}