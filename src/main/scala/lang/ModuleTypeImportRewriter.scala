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

 * Rewrite type * = moduleId.*; declarations.
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger

class ModuleTypeImportCollectorPass extends ReadOnlyPass[List[ExternalIdentifier]] {
  lazy val logger = Logger(classOf[ModuleTypeImportCollector])
  type T = List[ExternalIdentifier]
  override def applyOnModuleTypesImport(d : TraversalDirection.T, modTypImport : ModuleTypesImportDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      logger.debug("statement: {}", modTypImport.toString())
      val id = modTypImport.id
      context.map.get(id) match {
        case Some(Scope.ModuleDefinition(mod)) =>
          mod.typeDeclarationMap.map(p => ExternalIdentifier(id, p._1)).toList ++ in
        case _ => in
      }
    } else {
      in
    }
  }
}

class ModuleTypeImportCollector extends ASTAnalyzer("ModuleTypeImportCollector", new ModuleTypeImportCollectorPass()) {
  lazy val logger = Logger(classOf[ModuleTypeImportCollector])
  override def reset() {
    in = Some(List.empty)
  }
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val externalIds = visitModule(module, List.empty, context)
    val newImports = externalIds.map(p => TypeDecl(p.id, ExternalType(p.moduleId, p.id)))
    logger.debug("newImports: " + newImports.toString())
    val modP = Module(module.id, newImports ++ module.decls, module.cmds, module.notes)
    return Some(modP)
  }
}
