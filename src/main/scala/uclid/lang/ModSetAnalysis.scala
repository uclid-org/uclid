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

class ModSetRewriterPass() extends RewritePass {
    /*  A map that collects all the modified variables for a procedure.
     *  The key is the procedure identifier and value is the set of mdoified variables.
     */
    var modSetMap: Map[Identifier, Set[ModifiableEntity]] = Map.empty[Identifier, Set[ModifiableEntity]]

    /** Returns whether the variable should be added to the modifies set using the
      * state variable set and current local variable set.
      * We want to include variables that are
      *   (1) contained in the variable set and
      *   (2) not a local variable
      *  @param varIdSet The set of state variables to include in the modifies set.
      *                  This is usually the set of output and state variables.
      *  @param locVarIdSet The set of local variables at the current scope.
      *                     This is used to avoid adding shadowed local variables.
      */
    def isModified(id: Identifier, varIdSet: Set[Identifier], locVarIdSet: Set[Identifier]): Boolean = {
      varIdSet.contains(id) && !locVarIdSet.contains(id)
    }

    /** Returns the modified variables in a statement
     *  @stmt The statement whose write set is being inferred.
     *  @modSetMap The modifies set map inferred by the ModSetAnalysis pass. Should contain a map from procedures to thier inferred modifies sets.
     */
    def getStmtModSet(stmt: Statement, modSetMap: Map[Identifier, Set[ModifiableEntity]], varIdSet: Set[Identifier], locVarIdSet: Set[Identifier]): Set[ModifiableEntity] = stmt match {
      case BlockStmt(vars, stmts) => {
        val locVarIdSetP = vars.foldLeft(locVarIdSet)((acc, bvd) => acc ++ bvd.ids.toSet)
        stmts.foldLeft(Set.empty[ModifiableEntity])((acc, stmt) => acc ++ getStmtModSet(stmt, modSetMap, varIdSet, locVarIdSetP))
      }
      case ProcedureCallStmt(id, _, _, _, _) => modSetMap.get(id) match {
        case Some(set) => set
        case None => Set.empty[ModifiableEntity]
      }
      case IfElseStmt(_, ifblock, elseblock) => getStmtModSet(ifblock, modSetMap, varIdSet, locVarIdSet) ++ getStmtModSet(elseblock, modSetMap, varIdSet, locVarIdSet)
      case ForStmt(_, _, _, body) => getStmtModSet(body, modSetMap, varIdSet, locVarIdSet)
      case WhileStmt(_, body, _) => getStmtModSet(body, modSetMap, varIdSet, locVarIdSet)
      case CaseStmt(body) => body.foldLeft(Set.empty[ModifiableEntity])((acc, pair) => acc ++ getStmtModSet(pair._2, modSetMap, varIdSet, locVarIdSet))
      case HavocStmt(havocableEntity) => {
          havocableEntity match {
              case HavocableId(id) => if (isModified(id, varIdSet, locVarIdSet)) Set(ModifiableId(id)) else Set.empty
              case _ => Set.empty
          }
      }
      case AssignStmt(lhss, _) => {
        lhss.map(lhs => lhs.ident)
            .filter(id => isModified(id, varIdSet, locVarIdSet))
            .foldLeft(List.empty[ModifiableEntity])((acc, id) => ModifiableId(id) :: acc)
            .toSet
      }
      case _ => Set.empty[ModifiableEntity]
    }

    /** Rewrites the modifies set to contain all left hand side and havoced variables
        including the ones nested in procedure calls.
        NOTE: This does not overwrite the entire modifies set! It adds the inferred
        set to the current modifies set if any exists.
     */
    override def rewriteProcedure(proc : ProcedureDecl, ctx : Scope) : Option[ProcedureDecl] = {
        val inferredModSet = modSetMap.get(proc.id) match {
            case Some(set) => set
            case None => Set.empty[ModifiableEntity]
        }
        val stateVarIds = ctx.vars.map(v => v.varId)
        val outputVarIds = ctx.outputs.map(v => v.outId)
        val varIdSet = stateVarIds ++ outputVarIds
        val returnIdSet = proc.sig.outParams.map(_._1).toSet
        val calleeModSets = getStmtModSet(proc.body, modSetMap, varIdSet, returnIdSet)
        val modSet = proc.modifies
        // combined modifies set containing the original modifies set, inferred modifies set
        // and modifies set of the callees
        val combinedModSet = modSet ++ inferredModSet ++ calleeModSets
        // update the modifies sets for all functions
        // this is important for the next iteration of the rewrite pass since it is repeated
        // until a fixed point where no additional modified identifiers are found
        modSetMap = modSetMap + (proc.id -> combinedModSet)
        Some(ProcedureDecl(proc.id, proc.sig, proc.body, proc.requires, proc.ensures, combinedModSet, proc.annotations))
    }
}

class ModSetRewriter() extends ASTRewriter("ModSetRewriter", new ModSetRewriterPass()) {
	override val repeatUntilNoChange = true
}