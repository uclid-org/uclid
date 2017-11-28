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
  // does this belong somewhere else?
  def cloneMetadata(src : ASTNode, dst : ASTNode) = {
    dst.filename = src.filename
    dst.pos = src.pos
  }

  override def rewriteSpec(spec : SpecDecl, ctx : Scope) : Option[SpecDecl] = {
    var specP = spec
    for (p <- spec.params) {
      p match {
        case LTLExprDecorator =>
          // somehow signify to other passes that inside this specdecl expr, it is okay to start using "globally" etc as identifiers
          specP = DoLTLStuff(specP)
        case _ =>
      }
    }
    Some(specP)
  }

  override def rewriteFuncApp(fapp: FuncApplication, ctx: Scope): Option[Expr] = {
    var ret : Expr = null
    fapp.e match {
      case Identifier(name : String) => name match {
        case "globally" =>
          var top : GloballyTemporalOp = new GloballyTemporalOp
          cloneMetadata(fapp.e, top)
          var ret = OperatorApplication(top, fapp.args)
        case "next" =>
          var top : NextTemporalOp = new NextTemporalOp
          cloneMetadata(fapp.e, top)
          var ret = OperatorApplication(top, fapp.args)
        case "until" =>
          // should we change until immediately to equivalent form using w-until?
          var top : UntilTemporalOp = new UntilTemporalOp
          cloneMetadata(fapp.e, top)
          var ret = OperatorApplication(top, fapp.args)
        case "finally" =>
          var top : FinallyTemporalOp = new FinallyTemporalOp
          cloneMetadata(fapp.e, top)
          var ret = OperatorApplication(top, fapp.args)
      }
    }
    cloneMetadata(fapp, ret)
    Some(ret)
  }
}

class LTLOperatorRewriter extends ASTRewriter(
  "LTLOperatorRewriter", new LTLOperatorRewriterPass())


class LTLOperatorArgumentCheckerPass extends ReadOnlyPass[List[ModuleError]] {
  type T = List[ModuleError]
  override def applyOnOperatorApp(d : TraversalDirection.T, opapp : OperatorApplication, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      in
    } else {
      opapp.op match {
        case TemporalOperator =>
          // catch arity, type errors
        case _ =>
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
  override def rewriteInstance(instD : InstanceDecl, context : Scope) : Option[InstanceDecl] = {
    // todo: work out full negations of LTL operators
    // depends on choice of until vs w-until
  }
}

class LTLNegatedNormalFormRewriter extends ASTRewriter(
  "LTLNegatedNormalFormRewriter", new LTLNegatedNormalFormRewriterPass())


class LTLPropertyRewriterPass extends RewritePass {
  override def rewriteInstance(instD : InstanceDecl, context : Scope) : Option[InstanceDecl] = {

  }
}

class LTLPropertyRewriter extends ASTRewriter(
  "LTLPropertyRewriter", new LTLPropertyRewriterPass())