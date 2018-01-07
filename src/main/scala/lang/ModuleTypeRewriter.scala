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

class InstanceModuleNameCheckerPass extends ReadOnlyPass[List[ModuleError]] {
  type T = List[ModuleError]
  override def applyOnInstance(d : TraversalDirection.T, instD : InstanceDecl, in : T, context : Scope) : T = {
    context.moduleDefinitionMap.get(instD.moduleId) match {
      case Some(mod) => in
      case None =>
        val msg = "Unknown module: %s.".format(instD.moduleId.toString)
        ModuleError(msg, instD.moduleId.position) :: in
    }
  }
}

class InstanceModuleNameChecker extends ASTAnalyzer(
    "InstanceModuleNameChecker", new InstanceModuleNameCheckerPass())
{
  override def reset() {
    in = Some(List.empty[ModuleError])
    pass.reset()
  }
}

class InstanceModuleTypeRewriterPass extends RewritePass {
  override def rewriteInstance(instD : InstanceDecl, context : Scope) : Option[InstanceDecl] = {
    val modOption = context.moduleDefinitionMap.get(instD.moduleId)
    Utils.assert(modOption.isDefined, "Unknown modules must have been detected by now: " + instD.toString)
    val mod = modOption.get
    val modType = mod.moduleType
    val instDP = InstanceDecl(instD.instanceId, instD.moduleId, instD.arguments, instD.instType, Some(modType))
    Some(instDP)
  }
}

class InstanceModuleTypeRewriter extends ASTRewriter(
    "InstanceModuleTypeRewriter", new InstanceModuleTypeRewriterPass())