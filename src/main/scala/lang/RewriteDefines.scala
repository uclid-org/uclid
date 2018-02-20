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
 * Author : Pramod Subramanyan
 *
 * Rewrite (inline) usage of 'define' statements.
 */

package uclid
package lang

case class DefDepAccumulator(defineId : Option[Identifier], depGraph : Map[Identifier, Set[Identifier]]) {
  def insideDefine(dId : Identifier) : DefDepAccumulator = {
    Utils.assert(defineId.isEmpty, "Should not already be inside a define declaration.")
    DefDepAccumulator(Some(dId), depGraph)
  }
  def outsideDefine : DefDepAccumulator = {
    Utils.assert(defineId.isDefined, "Expected to be inside a define declaration.")
    DefDepAccumulator(None, depGraph)
  }

  def addEdgeTo(gId: Identifier) : DefDepAccumulator = {
    val thisDefId = defineId match {
      case None     => Identifier("$top")
      case Some(id) => id
    }
    val depGraphP = depGraph.get(thisDefId) match {
      case None        => depGraph + (thisDefId -> Set(gId))
      case Some(nodes) => depGraph + (thisDefId -> (nodes + gId))
    }
    DefDepAccumulator(defineId, depGraphP)
  }
}

case object DefDepAccumulator {
  def empty : DefDepAccumulator = DefDepAccumulator(None, Map.empty)
}

class DefDepGraphPass extends ReadOnlyPass[DefDepAccumulator] {
  type T = DefDepAccumulator

  override def applyOnDefine(d : TraversalDirection.T, defDecl : DefineDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      in.addEdgeTo(defDecl.id).insideDefine(defDecl.id)
    } else {
      in.outsideDefine
    }
  }

  override def applyOnFuncApp(d : TraversalDirection.T, fapp : FuncApplication, in : T, context : Scope) : T = {
    in.defineId match {
      case None     => in
      case Some(id) => 
        fapp.e match {
          case id : Identifier =>
            context.map.get(id) match {
              case Some(Scope.Define(id, _, _)) => in.addEdgeTo(id)
              case _ => in
            }
          case _ => in
        }
    }
  }
}

class DefDepGraphChecker extends ASTAnalyzer("DefDepGraphChecker", new DefDepGraphPass()) {
  override def visit(module : Module, context : Scope) : Option[Module] = {
    def recursionError(proc : Identifier, stack : List[Identifier]) : ModuleError = {
      val cleanStack = stack.filter(id => id != Identifier("$top")).map(_.toString)
      val msg = "Recursion involving define declarations: " + Utils.join(cleanStack.toList, ", ")
      ModuleError(msg, proc.position)
    }

    val defDepGraphAcc = visitModule(module, DefDepAccumulator.empty, context)
    val defDepGraph = defDepGraphAcc.depGraph
    val errors = Utils.findCyclicDependencies(defDepGraph, List(Identifier("$top")), recursionError)
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
    Some(module)
  }
}

class RewriteDefinesPass extends RewritePass {
  var changed = false

  def rewrite(defDecl : DefineDecl, args : List[Expr], ctx : Scope) : Option[Expr] = {
    val rewriteMap : Map[Expr, Expr] = (defDecl.sig.args zip args).map(p => p._1._1 -> p._2).toMap
    val exprRewriter = new ExprRewriter("DefineRewriter", rewriteMap)
    exprRewriter.visitExpr(defDecl.expr, ctx)
  }

  override def rewriteFuncApp(fapp : FuncApplication, ctx : Scope) : Option[Expr] = {
    fapp.e match {
      case id : Identifier =>
        ctx.map.get(id) match {
          case Some(Scope.Define(id, sig, defDecl)) =>
            changed = true
            rewrite(defDecl, fapp.args, ctx)
          case _ => Some(fapp)
        }
      case _ => Some(fapp)
    }
  }
}

class RewriteDefines extends ASTRewriter("RewriteDefines", new RewriteDefinesPass()) {
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val rewriterPass = pass.asInstanceOf[RewriteDefinesPass]
    var moduleP : Option[Module] = Some(module)
    do {
      rewriterPass.changed = false
      moduleP = visitModule(moduleP.get, context)
    } while (rewriterPass.changed && moduleP.isDefined)
    moduleP
  }
}