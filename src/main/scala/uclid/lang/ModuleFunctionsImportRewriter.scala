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
 * Author: Pranav Gaddamadugu

 * Rewrite function * = moduleId.*; declarations.
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger
import scala.collection.mutable.HashMap

class ModuleFunctionsImportCollectorPass extends ReadOnlyPass[HashMap[Identifier, Identifier]] {
  lazy val logger = Logger(classOf[ModuleFunctionsImportRewriter])
  type T = HashMap[Identifier, Identifier]
/**
 * This function recursively searches for import dependencies across modules
 * and forms a list of modules that we need to import from.
 *
 * @param id Identifier of the current module
 * @param ctx Scope containing ModuleDefinitions
 */
  def findModuleDependencies(id : Identifier, ctx : Scope) : List[Identifier] = {
    val mod = ctx.map.get(id) match {
      case Some(Scope.ModuleDefinition(module)) => module
      case _ => throw new Utils.AssertionError("Trying to import from a module that doesn't exist; try reordering the input of module files")
    }
    
    val importList : List[Identifier] = mod.funcImportDecls.map(d => d.id)
    val fullList = importList ++ importList.foldLeft(List[Identifier]()) { 
      (list, id) => {
        val dependencies = findModuleDependencies(id, ctx)
        list ++ dependencies
      }
    }
    fullList
  }

/**
 * This function finds and stores the identifier and module identifier of all
 * imported functions.
 *
 * @param d Direction of AST traversal
 * @param modFunImport Import declaration
 * @param in HashMap[Identifier, Identifier]
 * @param context Scope containing ModuleDefinitions
 */
  override def applyOnModuleFunctionsImport(d : TraversalDirection.T, modFunImport : ModuleFunctionsImportDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      logger.debug("statement: {}", modFunImport.toString())
      val id = modFunImport.id
      val dependList = findModuleDependencies(id, context)
      
      // prepend this modules id to moduleList
      val moduleList = id :: dependList

      moduleList.foreach { id =>
        // The module has already been checked in `findModuleDependencies`
        val mod = context.map.get(id).get.asInstanceOf[Scope.ModuleDefinition].mod
        mod.functions.foreach { f => 
          in.get(f.id) match {
            case Some(_) => throw new Utils.AssertionError(s"Redeclaration error in module functions import. Check module: ${mod.id}")
            case None => in += ((f.id, mod.id))
          }
        }
      }
      in
    } else {
      in
    }
  }
}


class ModuleFunctionsImportRewriter extends ASTAnalyzer("ModuleFunctionsImportRewriter", new ModuleFunctionsImportCollectorPass()) {
  lazy val logger = Logger(classOf[ModuleFunctionsImportRewriter])
  override def reset() {
    in = Some(HashMap.empty)
  }

/**
 * This function will traverse a module and append all imported function calls
 * with their appropriate module tag.
 *
 * @param module The module to be visited
 * @param context The context of the current module (technically accumulated
 *    by the PassManager)
 */
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val modScope = manager.moduleList.foldLeft(Scope.empty)((s, m) => s +& m )

    // Add functions from this module
    val initMap = new HashMap[Identifier, Identifier]()
    module.functions.foreach { f => 
      initMap.get(f.id) match {
        case Some(_) => throw new Utils.AssertionError(s"Function redeclaration error in module: ${module.id}")
        case None => initMap += ((f.id, module.id))
      }
    }
    val funcMap = visitModule(module, initMap, modScope).filterNot(p => p._2 ==module.id)
    val rewriterMap = funcMap.map(p => (p._1 -> OperatorApplication(PolymorphicSelect(p._1), List(p._2)))).asInstanceOf[HashMap[Expr, Expr]].toMap
    val rewriter = new ExprRewriter("FunctionRewriter", rewriterMap)
    rewriter.visit(module, context)
  }
}
