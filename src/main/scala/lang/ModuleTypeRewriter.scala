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
        val msg = "Unknown module: %s".format(instD.moduleId.toString)
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
