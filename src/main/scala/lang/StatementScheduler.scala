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
 * Authors: Rohit Sinha, Pramod Subramanyan

 * Statement scheduler.
 *
 */

package uclid
package lang

object StatementScheduler {
  def writeSet(st : Statement, context : Scope) : Set[Identifier] = {
    st match {
      case SkipStmt() => Set.empty
      case AssertStmt(e, _) => Set.empty
      case AssumeStmt(e, _) => Set.empty
      case HavocStmt(h) => 
        h match {
          case HavocableId(id) => Set(id)
          case HavocableFreshLit(f) =>
            throw new Utils.AssertionError("Fresh literals must have been eliminated by now.")
        }
      case AssignStmt(lhss, rhss) => lhss.map(lhs => lhs.ident).toSet
      case IfElseStmt(cond, ifblock, elseblock) =>
        writeSets(ifblock, context) ++ writeSets(elseblock, context)
      case ForStmt(_, _, body) =>
        writeSets(body, context)
      case CaseStmt(bodies) =>
        bodies.foldLeft(Set.empty[Identifier])((acc, b) => writeSets(b._2, context))
      case ProcedureCallStmt(id, callLhss, args) => callLhss.map(_.ident).toSet
      case ModuleCallStmt(id) =>
        val idType = context.typeOf(id)
        Utils.assert(idType.get.isInstanceOf[ModuleType], "Expected type module")
        val moduleType : ModuleType = idType.asInstanceOf[ModuleType]
        moduleType.outputs.map(p => p._1).toSet
    }
  }

  def writeSets(stmts: List[Statement], context : Scope) : (Set[Identifier]) = {
    stmts.foldLeft(Set.empty[Identifier])((acc, st) => acc ++ writeSet(st, context))
  }
}
class StatementScheduler {
  
}