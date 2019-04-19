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
 * Rewrite function * = moduleId.*; declarations.
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger

//TODO: Rewrite method that calls `applyOnModuleFunctionsImport` to collect external mappings (just
//        functions) and aggregate the function declarations; if any identifiers clash, throw a 
//        redeclaration error. 
//
//        NOTE: We could also enhance UCLID's type inference system by using the function signature 
//        ( paramater and return types ) to identify a function.

//TODO: Pass the aggregated list to a following step, where all of the functions in the module are
//        checked for declaration in the module or checked in the aggregated list and written as 
//        an external type.
//
//        NOTE: If the identifier is double declared in the current environment and the imported
//          environment, then throw a DoubleDecl error. If not declared in either, then throw 
//          a NotDefined error.
//        

class ModuleFunctionsImportCollectorPass extends ReadOnlyPass[List[FunctionDecl]] {
  lazy val logger = Logger(classOf[ModuleFunctionsImportCollector])
  type T = List[FunctionDecl]
  override def applyOnModuleFunctionsImport(d : TraversalDirection.T, modFuncImport : ModuleFunctionsImportDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      logger.debug("statement: {}", modFuncImport.toString())
      val id = modFuncImport.id
      context.map.get(id) match{
        case Some(Scope.ModuleDefinition(mod)) =>
          mod.functions.map {
            f => {
              ASTNode.introducePos(true, true, f, modFuncImport.position)
            }
          } ++ in
        case _ => in
      }
    } else {
      in
    }
  }
}

class ModuleFunctionsImportCollector extends ASTAnalyzer("ModuleFunctionsImportCollector", new ModuleFunctionsImportCollectorPass()) {
  lazy val logger = Logger(classOf[ModuleFunctionsImportCollector])
  override def reset() {
    in = Some(List.empty)
  }
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val externalIds = visitModule(module, List.empty, context)
    val newImports = externalIds.map {
      p => {
        ASTNode.introducePos(true, true, p, p.position)
      }
    }
    logger.debug("newImports: " + newImports.toString())
    val modP = Module(module.id, newImports ++ module.decls, module.cmds, module.notes)
    return Some(modP)
  }
}
    
