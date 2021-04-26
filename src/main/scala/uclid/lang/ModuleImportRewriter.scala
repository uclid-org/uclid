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
 * Author: Kevin Cheang
 * Rewrite import moduleId; declarations. This copies all declarations from the module named moduleId to the declaring module.
 *
 */

package uclid
package lang

/** Rewrites the module's import declarations
  */
class ModuleImportRewriterPass() extends RewritePass {
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    // remove the import module declarations
    val declsP = module.decls.filter(decl => !decl.isInstanceOf[ModuleImportDecl])

    // add all imported modules
    val declsPP = module
      .moduleImportDecls
      .foldLeft(declsP)(
        (acc, modImportDecl) => {
          val moduleToImportId = modImportDecl.modId
          ctx.get(moduleToImportId) match {
            case Some(namedExpr) => {
              namedExpr match {
                case Scope.ModuleDefinition(mod) => {
                  // remove the init and next declarations
                  val declsP = mod.decls.filter(decl => !decl.isInstanceOf[InitDecl] && !decl.isInstanceOf[NextDecl])
                  acc ++ declsP
                }
                case _ => throw new Utils.RuntimeError("%s is not a module type. Failed to import into %s.".format(moduleToImportId, module.id))
              }
            }
            case None => throw new Utils.RuntimeError("Module %s not found. Failed to import into %s.".format(moduleToImportId, module.id))
          }
        }
      )

    val moduleP = Module(module.id, declsPP, module.cmds, module.notes)
    Some(moduleP)
  }
}

class ModuleImportRewriter() extends ASTRewriter("ModuleImportRewriter", new ModuleImportRewriterPass())
