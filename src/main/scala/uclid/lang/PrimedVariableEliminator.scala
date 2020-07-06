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

import com.typesafe.scalalogging.Logger

class PrimedVariableCollectorPass extends ReadOnlyPass[(Map[Identifier, Identifier])]
{
  type T = Map[Identifier, Identifier]
  def addToMap(id : Identifier, in : T, tag : String) : T = {
    in.get(id) match {
      case Some(_) => in
      case None =>
        val newId = NameProvider.get(id.toString + "_" + tag)
        val mapP = (in + (id -> newId))
        mapP
    }
  }
  override def applyOnLHS(d : TraversalDirection.T, lhs : Lhs, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      lhs match {
        case LhsNextId(id) => addToMap(id, in, "lhs")
        case _ => in
      }
    } else {
      in
    }
  }
  override def applyOnHavoc(d : TraversalDirection.T, havocStmt : HavocStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      havocStmt.havocable match {
        case HavocableNextId(id) => addToMap(id, in, "havoc")
        case _ => in
      }
    } else {
      in
    }
  }
}

class PrimedVariableCollector() extends ASTAnalyzer("PrimedVariableCollector", new PrimedVariableCollectorPass())
{
  var primeVarMap : Option[Map[Identifier, Identifier]] = None
  var reverseMap : Option[Map[Identifier, Identifier]] = None
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val fwdMap = visitModule(module, Map.empty, context)
    val revMap = fwdMap.foldLeft(Map.empty[Identifier, Identifier]) {
      (acc, p) => acc + (p._2 -> p._1)
    }
    primeVarMap = Some(fwdMap)
    reverseMap = Some(revMap)
    Some(module)
  }
}

class PrimedVariableEliminatorPass extends RewritePass {
  val logger = Logger(classOf[PrimedVariableEliminatorPass])
  lazy val manager : PassManager = analysis.manager
  lazy val primedVariableCollector = manager.pass("PrimedVariableCollector").asInstanceOf[PrimedVariableCollector]

  def getInitialAssigns() : List[AssignStmt] = {
    val primeVarMap = primedVariableCollector.primeVarMap.get
    primeVarMap.map(p => {
      (AssignStmt(List(LhsId(p._2)), List(p._1)))
    }).toList
  }
  def getFinalAssigns() : List[AssignStmt] = {
    val primeVarMap = primedVariableCollector.primeVarMap.get
    primeVarMap.map(p => (AssignStmt(List(LhsId(p._1)), List(p._2)))).toList
  }
  def getPrimeVarDecls(context : Scope) : List[BlockVarsDecl] = {
    val primeVarMap = primedVariableCollector.primeVarMap.get
    (primeVarMap.filter(p => context.get(p._1) match {
      // remove all instances modified
      case Some(Scope.Instance(_)) | Some(Scope.InstanceArray(_)) => false
      case _ => true
    }).map {
      p => {
        val typ = context.get(p._1) match {
          case None => {
            val namedExpr = context.map.find(namedExpr => {
              namedExpr._2.isInstanceOf[Scope.ModuleDefinition] &&
              namedExpr._2.asInstanceOf[Scope.ModuleDefinition].mod.vars.find(v => v._1.name == p._1.name) != None
            }).get._2
            val instVarMod = namedExpr.asInstanceOf[Scope.ModuleDefinition].mod
            instVarMod.vars.find(v => v._1 == p._1).get._2
          }
          case _ => context.typeOf(p._1).get
        }
        BlockVarsDecl(List(p._2), typ)
      }
    }).toList
  }
  override def rewriteInit(init : InitDecl, context : Scope) : Option[InitDecl] = {
    val primeDecls = getPrimeVarDecls(context)
    val initP = InitDecl(BlockStmt(primeDecls, getInitialAssigns() ++ List(init.body)))
    Some(initP)
  }
  override def rewriteNext(next : NextDecl, context : Scope) : Option[NextDecl] = {
    val primeDecls = getPrimeVarDecls(context)
    val nextP = NextDecl(BlockStmt(primeDecls, getInitialAssigns() ++ List(next.body) ++ getFinalAssigns()))
    Some(nextP)
  }
  override def rewriteHavoc(havocStmt : HavocStmt, context : Scope) : Option[Statement] = {
    havocStmt.havocable match {
      case HavocableNextId(id) => 
        val primeVarMap = primedVariableCollector.primeVarMap.get
        logger.debug("primeVarMap: {}", primeVarMap.toString())
        Some(HavocStmt(HavocableId(primeVarMap.get(id).get)))
      case _ =>
        Some(havocStmt)
    }
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
    val argsP = instD.arguments
    val instP = InstanceDecl(instD.instanceId, instD.moduleId, argsP, instD.instType, instD.modType)
    Some(instP)
  }
  override def rewriteInstanceArray(instD : InstanceArrayDecl, context : Scope) : Option[InstanceArrayDecl] = {
    val argsP = instD.arguments
    val instP = InstanceArrayDecl(instD.instanceId, instD.inTypes, instD.moduleId, argsP, instD.instType, instD.modType)
    Some(instP)
  }
}

class PrimedVariableEliminator extends ASTRewriter(
    "PrimedVariableEliminator", new PrimedVariableEliminatorPass())
