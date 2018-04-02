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
