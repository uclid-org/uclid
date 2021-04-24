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
 * Author : Kevin Cheang
 *
 * The ModSetAnalysisPass collects all the mod sets for procedures
 *
 */
package uclid
package lang

class ModSetAnalysisPass() extends ReadOnlyPass[Map[Identifier, Set[Identifier]]] {
  // Map from procedure id to its inferred modifies set
  type T = Map[Identifier, Set[Identifier]]

  /** Recursively computes the modifies set for a statement by looking at the
   *  left hand side assignments and havoc statements.
   *
   *  @param stmt The statement to infer
   *  @param varIdSet A Set of state variables to include in the modifies set.
   *                  This is usually the set of output and state variables.
   */
  def collectStatementModifies(stmt: Statement, varIdSet: Set[Identifier]): Set[Identifier] = {
    stmt match {
        case HavocStmt(havocableEntity) => {
            havocableEntity match {
                case HavocableId(id) => if (varIdSet.contains(id)) Set(id) else Set.empty
                case _ => Set.empty
            }
        }
        case AssignStmt(lhss, _) => lhss.map(lhs => lhs.ident).filter(ident => varIdSet.contains(ident)).foldLeft(List.empty[Identifier])((acc, ident) => ident :: acc).toSet
        case BlockStmt(_, stmts) => stmts.foldLeft(Set.empty[Identifier])((acc, stmt) => acc ++ collectStatementModifies(stmt, varIdSet))
        case IfElseStmt(_, thn, els) => collectStatementModifies(thn, varIdSet) ++ collectStatementModifies(els, varIdSet)
        case ForStmt(_, _, _, body) => collectStatementModifies(body, varIdSet)
        case WhileStmt(_, body, _) => collectStatementModifies(body, varIdSet)
        case CaseStmt(body) => body.map(pair => collectStatementModifies(pair._2, varIdSet)).flatten.toSet
        case ProcedureCallStmt(id, lhss, _, instanceId, _) => {
          if (instanceId.isDefined) {
            throw new Utils.UnimplementedException("Modifies set analysis is unimplemented for instance procedure calls.");
          }
          lhss.map(lhs => lhs.ident)
              .filter(varIdSet.contains(_))
              .foldLeft(List.empty[Identifier])((acc, ident) => ident :: acc)
              .toSet
        }
        case _ => Set.empty
    }
  }

  override def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : T, context : Scope) : T = {
    val stateVarIds = context.vars.map(v => v.varId)
    val outputVarIds = context.outputs.map(v => v.outId)
    val varIdSet = stateVarIds ++ outputVarIds
    val modSet = collectStatementModifies(proc.body, varIdSet)
    in + (proc.id -> modSet)
  }
}

class ModSetAnalysis() extends ASTAnalyzer("ModSetAnalysis", new ModSetAnalysisPass()) {
  override def reset() {
    in = Some(Map.empty[Identifier, Set[Identifier]])
  }

  /** Visit the module and infer the writesets using the left hand side assignments and havocs.
   *  Also updates the output to be a map from the procedure id to the inferred modifies set.
   */
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val modSetMap = visitModule(module, Map.empty[Identifier, Set[Identifier]], context)
    _out = Some(modSetMap)
    return Some(module)
  }
}

class ModSetRewriterPass() extends RewritePass {
    /** Rewrites the modifies set to contain all left hand side and havoced variables
        including the ones nested in procedure calls.
        NOTE: This does not overwrite the entire modifies set! It adds the inferred
        set to the current modifies set if any exists.
     */
    override def rewriteProcedure(proc : ProcedureDecl, ctx : Scope) : Option[ProcedureDecl] = {
        val modSetMap = analysis.manager.pass("ModSetAnalysis").asInstanceOf[ModSetAnalysis].out.get
        val inferredModSet = modSetMap.get(proc.id) match {
            case Some(set) => set.map(ident => ModifiableId(ident))
            case None => Set.empty[ModifiableEntity]
        }
        val calleeModSets = proc.body match {
            case BlockStmt(_, stmts) => {
                stmts.filter(stmt => stmt.isInstanceOf[ProcedureCallStmt])
                     .map(stmt => modSetMap.get(stmt.asInstanceOf[ProcedureCallStmt].id) match {
                        case Some(set) => set.map(ident => ModifiableId(ident)).toList
                        case None => List.empty[ModifiableEntity]
                     }).flatten.toSet
            }
            case _ => Set.empty
        }
        val modSet = proc.modifies
        // combined modifies set containing the original modifies set, inferred modifies set, and modifies set of the callees
        val combinedModSet = modSet ++ inferredModSet ++ calleeModSets
        Some(ProcedureDecl(proc.id, proc.sig, proc.body, proc.requires, proc.ensures, combinedModSet, proc.annotations))
    }
}

class ModSetRewriter() extends ASTRewriter("ModSetRewriter", new ModSetRewriterPass()) {
	override val repeatUntilNoChange = true
}