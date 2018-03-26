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

 * Statement scheduler.
 *
 */
package uclid
package lang

class PrimedVariableCollectorPass extends ReadOnlyPass[(Map[Identifier, Identifier], Option[ContextualNameProvider])]
{
  type T = (Map[Identifier, Identifier], Option[ContextualNameProvider])
  override def applyOnModule(d : TraversalDirection.T, module : Module , in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      val nameProvider = new ContextualNameProvider(context, "_prime_")
      (in._1, Some(nameProvider))
    } else {
      (in._1, None)
    }
  }
  override def applyOnLHS(d : TraversalDirection.T, lhs : Lhs, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      lhs match {
        case LhsNextId(id) =>
          in._1.get(id) match {
            case Some(idP) => in
            case None =>
              val newId = in._2.get(id, "lhs")
              val mapP = (in._1 + (id -> newId))
              (mapP, in._2)
          }
        case _ => in
      }
    } else {
      in
    }
  }
  override def applyOnProcedureCall(d : TraversalDirection.T, callStmt : ProcedureCallStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up && context.environment == SequentialEnvironment) {
      val procId = callStmt.id
      val module = context.module.get
      val proc = module.procedures.find(p => p.id == procId).get
      val mapIn = in._1
      val nameProvider = in._2.get
      val mapOut = proc.modifies.foldLeft(mapIn)((acc, m) => (acc + (m -> nameProvider(m, "modifies"))))
      (mapOut, in._2)
    } else {
      in
    }
  }
}

class PrimedVariableCollector() extends ASTAnalyzer("PrimedVariableCollector", new PrimedVariableCollectorPass())
{
  var primeVarMap : Option[Map[Identifier, Identifier]] = None
  override def visit(module : Module, context : Scope) : Option[Module] = {
    primeVarMap = Some(visitModule(module, (Map.empty, None), context)._1)
    Some(module)
  }
}

class PrimedVariableEliminatorPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val primedVariableCollector = manager.pass("PrimedVariableCollector").asInstanceOf[PrimedVariableCollector]

  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    val primeVarMap = primedVariableCollector.primeVarMap.get
    val ctxP = context + module
    val primeDecls = primeVarMap.map {
      p => {
        val typ = ctxP.typeOf(p._1).get
        StateVarsDecl(List(p._2), typ)
      }
    }
    val moduleP = Module(module.id, module.decls ++ primeDecls, module.cmds, module.notes)
    Some(moduleP)
  }
  def getInitialAssigns() : List[AssignStmt] = {
    val primeVarMap = primedVariableCollector.primeVarMap.get
    primeVarMap.map(p => (AssignStmt(List(LhsId(p._2)), List(p._1)))).toList
  }
  def getFinalAssigns() : List[AssignStmt] = {
    val primeVarMap = primedVariableCollector.primeVarMap.get
    primeVarMap.map(p => (AssignStmt(List(LhsId(p._1)), List(p._2)))).toList
  }
  override def rewriteInit(init : InitDecl, context : Scope) : Option[InitDecl] = {
    val initP = InitDecl(init.body ++ getInitialAssigns())
    Some(initP)
  }
  override def rewriteNext(next : NextDecl, context : Scope) : Option[NextDecl] = {
    val nextP = NextDecl(getInitialAssigns() ++ next.body ++ getFinalAssigns())
    Some(nextP)
  }
  override def rewriteLHS(lhs : Lhs, context : Scope) : Option[Lhs] = {
    lazy val primeVarMap = primedVariableCollector.primeVarMap.get
    lhs match {
      case LhsNextId(id) => Some(LhsId(primeVarMap.get(id).get))
      case _ => Some(lhs)
    }
  }
  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    lazy val primeVarMap = primedVariableCollector.primeVarMap.get
    opapp.op match {
      case GetNextValueOp() =>
        val id = opapp.operands(0).asInstanceOf[Identifier]
        primeVarMap.get(id) match {
          case Some(idP) => Some(idP)
          case None => Some(id)
        }
      case _ => Some(opapp)
    }
  }
  override def rewriteInstance(instD : InstanceDecl, context : Scope) : Option[InstanceDecl] = {
    lazy val primeVarMap = primedVariableCollector.primeVarMap.get
    val modType = instD.modType.get
    val writeableArgs = (modType.outputs ++ modType.sharedVars).map(p => p._1).toSet
    val argsP = instD.arguments.map {
      case (argId, exprOption) => {
        exprOption match {
          case Some(expr) =>
            if (writeableArgs.contains(argId)) {
              // Output arguments must strictly be identifiers.
              Utils.assert(expr.isInstanceOf[Identifier], "Module outputs and shared variables must be identifiers.")
              val varId = expr.asInstanceOf[Identifier]
              primeVarMap.get(varId) match {
                case Some(varIdP) => (argId, Some(varIdP))
                case None => (argId, exprOption)
              }
            } else {
              (argId, exprOption)
            }
          case None =>
            (argId, exprOption)
        }
      }
    }
    val instP = InstanceDecl(instD.instanceId, instD.moduleId, argsP, instD.instType, instD.modType)
    Some(instP)
  }
}

class PrimedVariableEliminator extends ASTRewriter(
    "PrimedVariableEliminator", new PrimedVariableEliminatorPass())