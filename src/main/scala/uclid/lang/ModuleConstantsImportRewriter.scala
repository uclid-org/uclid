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
 * Rewrite const * = moduleId.*; declarations.
 *
 */

package uclid 
package lang

import com.typesafe.scalalogging.Logger
import scala.collection.mutable.HashMap

//TODO: Verify that we don't actually need to pull in axioms if we just rewrite
// all constants as 'module' + '.' + const

class ModuleConstantsImportRewriterPass extends RewritePass {}

class ModuleConstantsImportRewriter extends ASTRewriter(
  "ModuleConstantsImportRewriter", new ModuleConstantsImportRewriterPass()) {

  /*
   * Collects all constants and constant literals into map, while checking 
   * for redeclaration errors.
   *
   * @returns Returns a map from constant to moduleId.
   */
  def collectConstantDecls(module : Module, map : HashMap[Identifier, Identifier]) : HashMap[Identifier, Identifier] = {
    module.constLits.map(c => map.get(c._1) match {
      case Some(_) => throw new Utils.AssertionError("Redeclaration error in module constant literals import")
      case None => map += ((c._1, module.id))
    })
    module.constants.map(c => map.get(c._1) match {
      case Some(_) => throw new Utils.AssertionError("Redeclaration error in module constants import")
      case None => map += ((c._1, module.id))
    })
    map
  }

  /*
   * Collects the names of all modules to import constants from.
   * 
   * @returns Returns a list module identifiers.
   */
  def findModuleDependencies(module : Module, modList : List[Module]) : List[Identifier] = {
    val importList : List[Identifier] = module.decls.collect { case importDecl : ModuleConstantsImportDecl => importDecl.id }
    val fullList = importList ++ importList.foldLeft(List[Identifier]()) { (list, id) => {
        val mod = modList.find(m => m.id == id)
        if (mod == None) {
          list
        } else {
          val dependencies = findModuleDependencies(mod.get, modList)
          list ++ dependencies
        }
      }
    }
    fullList
  }

  /*
   * Collects all constants from imported module, while preserving nested imports.
   * @returns Returns a map from constant to moduleId
   */
  def collectAllConstants(module : Module, map : HashMap[Identifier, Identifier], modList : List[Module]) : HashMap[Identifier, Identifier] = {
    val moduleList = findModuleDependencies(module, modList)
    moduleList.map(id => {
      // moduleList should only use available modules
      val mod = modList.find(m => m.id == id)
      if (mod != None) 
        collectConstantDecls(mod.get, map)
      else 
        throw new Utils.TypeError("Module: " + id.toString + ", not found for importing constants", None, None)
    })
    map
  }

  /*
   * Rewrite constants to refer to the moduleId they are imported from.
   *
   * @returns Returns a new module with the rewritten constants.
   *
   */
  override def visitModule(module : Module, initContext : Scope) : Option[Module] = {

    val constMap = collectAllConstants(module, new HashMap(), manager.moduleList)
    val rewriterMap = constMap.map(p => (p._1 -> OperatorApplication(PolymorphicSelect(p._1), List(p._2)))).asInstanceOf[HashMap[Expr, Expr]].toMap
    val rewriter = new ExprRewriter("ConstantRewriter", rewriterMap)



    val context = initContext + module
    val id = visitIdentifier(module.id, context)
    val decls = module.decls.map(visitDecl(_, context)).flatten.map(rewriter.visitDecl(_, context)).flatten
    val initR : (List[Option[GenericProofCommand]], Scope) = (List.empty, initContext)
    val cmds = module.cmds.foldRight(initR)((cmd, acc) => (visitCommand(cmd, acc._2) :: acc._1, acc._2 + cmd))._1.flatten
    val notes = module.notes.map(note => visitNote(note, context)).flatten
    val moduleIn = id.flatMap((i) => Some(Module(i, decls, cmds, notes)))
    val moduleP = moduleIn.flatMap((m) => pass.rewriteModule(m, initContext))

    return (ASTNode.introducePos(true, true, moduleP, module.position) match {
      case Some(m) =>
        module.filename match {
          case Some(fn) => Some(m.withFilename(fn))
          case None     => Some(m)
        }
      case None =>
        None
    })
  }
}


