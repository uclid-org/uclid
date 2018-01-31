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
 * Rewrites each module to have init and next blocks. 
 * It also moves these blocks to the end of the module.
 *
 */
package uclid
package lang

class ModuleCanonicalizerPass extends RewritePass {
  override def rewriteModule(moduleIn : Module, ctx : Scope) : Option[Module] = {
    val initP = moduleIn.init match {
      case None => Some(InitDecl(List.empty))
      case Some(init) => None
    }
    val nextP = moduleIn.next match {
      case None => Some(NextDecl(List.empty))
      case Some(next) => None
    }
    val newDecls = moduleIn.decls ++ List(initP, nextP).flatten
    // FIXME: sort the declarations in the module.
    val modP = Module(moduleIn.id, newDecls, moduleIn.cmds)
    Some(modP)
  }
}

class ModuleCanonicalizer extends ASTRewriter(
    "ModuleCanonicalizer", new ModuleCanonicalizerPass())
