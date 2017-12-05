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

class LTLOperatorRewriterPass extends RewritePass {
  def cloneMetadata(src : ASTNode, dst : ASTNode) = {
    dst.filename = src.filename
    dst.pos = src.pos
  }

  override def rewriteFuncApp(fapp: FuncApplication, ctx: Scope): Option[Expr] = {
    if (inSpec) {
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
      cloneMetadata(fapp.e, top)
      var ret : Expr = OperatorApplication(top, fapp.args)
      cloneMetadata(fapp, ret)
      Some(ret)
    } else {
     Some(fapp)
    }
  }
}

class LTLOperatorRewriter extends ASTRewriter("LTLOperatorRewriter", new LTLOperatorRewriterPass()) {
  override def visitSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
    val idP = visitIdentifier(spec.id, context)
    pass.inSpec = true
    val exprP = visitExpr(spec.expr, context)
    pass.inSpec = false
    val decsP = spec.params.map(visitExprDecorator(_, context)).flatten
    val specP = (idP, exprP) match {
      case (Some(id), Some(expr)) => pass.rewriteSpec(SpecDecl(id, expr, decsP), context)
      case _ => None
    }
    return ASTNode.introducePos(_setFilename, specP, spec.position)
  }
}


class LTLOperatorArgumentCheckerPass extends ReadOnlyPass[Set[ModuleError]] {
  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  def checkBooleans(operands: List[Expr], context : Scope, in : T) : T = {
    var ret = in
    for (op <- operands) {
      var oType = exprTypeChecker.typeOf(op, context)
      if (!oType.isBool) {
        ret = ret + ModuleError("globally operator expected argument of type boolean but received argument of type %s.".format(oType.toString), op.position)
      }
    }
    ret
  }
  override def applyOnOperatorApp(d : TraversalDirection.T, opapp : OperatorApplication, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      in
    } else {
      var ret = in
      opapp.op match {
        case GloballyTemporalOp() =>
          var numOps = opapp.operands.length
          if (numOps != 1) {
            ret = ret + ModuleError("globally operator expected 1 argument but received %s".format(numOps), opapp.position)
          }
          checkBooleans(opapp.operands, context, ret)
        case NextTemporalOp() =>
          var numOps = opapp.operands.length
          if (numOps != 1) {
            ret = ret + ModuleError("next operator expected 1 argument but received %s".format(numOps), opapp.position)
          }
          checkBooleans(opapp.operands, context, ret)
        case UntilTemporalOp() =>
          var numOps = opapp.operands.length
          if (numOps != 2) {
            ret = ret + ModuleError("until operator expected 2 argument but received %s".format(numOps), opapp.position)
          }
          checkBooleans(opapp.operands, context, ret)
        case FinallyTemporalOp() =>
          var numOps = opapp.operands.length
          if (numOps != 1) {
            ret = ret + ModuleError("finally operator expected 1 argument but received %s".format(numOps), opapp.position)
          }
          checkBooleans(opapp.operands, context, ret)
        case ReleaseTemporalOp() =>
          var numOps = opapp.operands.length
          if (numOps != 2) {
            ret = ret + ModuleError("release operator expected 2 argument but received %s".format(numOps), opapp.position)
          }
          checkBooleans(opapp.operands, context, ret)
        case _ => in
      }
    }
  }
}

class LTLOperatorArgumentChecker extends ASTAnalyzer(
  "LTLOperatorArgumentChecker", new LTLOperatorArgumentCheckerPass())
{
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, Set.empty[ModuleError], context)
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}


class LTLNegatedNormalFormRewriterPass extends RewritePass {
  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    var ret = opapp
    if (opapp.op.isInstanceOf[NegationOp]) {
      val expr = opapp.operands.head
      if (expr.isInstanceOf[OperatorApplication]) {
        val oa = expr.asInstanceOf[OperatorApplication]
        oa match {
          // !globally(a) -> finally(!a)
          case GloballyTemporalOp() =>
            val negA = new OperatorApplication(new NegationOp, List(oa.operands.head))
            ret = OperatorApplication(new FinallyTemporalOp, List(negA))
          // !next(a) -> next(!a)
          case NextTemporalOp() =>
            val negA = new OperatorApplication(new NegationOp, List(oa.operands.head))
            ret = OperatorApplication(new NextTemporalOp, List(negA))
          // !until(a, b) -> wuntil(!b, !a && !b)
          case UntilTemporalOp() =>
            val negA = new OperatorApplication(new NegationOp, List(oa.operands.head))
            val negB = new OperatorApplication(new NegationOp, List(oa.operands.last))
            val conj = new OperatorApplication(new ConjunctionOp, List(negA, negB))
            ret = OperatorApplication(new WUntilTemporalOp, List(negB, conj))
          // !finally(a) -> globally(!a)
          case FinallyTemporalOp() =>
            val negA = new OperatorApplication(new NegationOp, List(oa.operands.head))
            ret = OperatorApplication(new GloballyTemporalOp, List(negA))
          // !release(a, b) -> wuntil(!a, !b) && finally(!b)
          case ReleaseTemporalOp() =>
            val negA = new OperatorApplication(new NegationOp, List(oa.operands.head))
            val negB = new OperatorApplication(new NegationOp, List(oa.operands.last))
            val wu = new OperatorApplication(new WUntilTemporalOp, List(negA, negB))
            val fin = new OperatorApplication(new FinallyTemporalOp, List(negB))
            ret = OperatorApplication(new ConjunctionOp, List(wu, fin))
        }
      }
    }
    Some(ret)
  }
}

class LTLNegatedNormalFormRewriter extends ASTRewriter(
  "LTLNegatedNormalFormRewriter", new LTLNegatedNormalFormRewriterPass())


//class LTLConjunctiveClauseRewriterPass extends RewritePass {
//  override def rewriteSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
//
//  }
//}
//
//class LTLConjunctiveClauseRewriter extends ASTRewriter(
//  "LTLConjunctiveClauseRewriter", new LTLConjunctiveClauseRewriterPass())
//
//
//class LTLPropertyRewriterPass extends RewritePass {
//  override def rewriteSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
//
//  }
//}
//
//class LTLPropertyRewriter extends ASTRewriter(
//  "LTLPropertyRewriter", new LTLPropertyRewriterPass())