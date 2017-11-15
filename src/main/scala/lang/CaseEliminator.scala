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
 * This file eliminate case statements from the AST and replaces them with ifs.
 * 
 */
package uclid
package lang

class CaseEliminatorPass extends RewritePass {
  def casesToIfs(cases : List[(Expr, List[Statement])]) : List[Statement] = {
    cases match {
      case Nil => 
        List.empty[Statement]
      case head :: rest =>
        List(IfElseStmt(head._1, head._2, casesToIfs(rest)))
    }
  }

  override def rewriteCase(st : CaseStmt, ctx : Scope) : List[Statement] = {
    casesToIfs(st.body)
  }
}

class CaseEliminator extends ASTRewriter(
    "CaseEliminator", new CaseEliminatorPass())
