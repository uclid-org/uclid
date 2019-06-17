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

 * PassManager: runs each AST pass in the order in which they are added to the manager.
 * May eventually add pass dependencies, invalidations and so on to this class.
 *
 */

package uclid
package lang

import scala.collection.mutable.{ListBuffer,Set}
import com.typesafe.scalalogging.Logger

class PassManager(name : => String) {
  lazy val logger = Logger(classOf[PassManager])

  type PassList = ListBuffer[ASTAnalysis]
  var passes : PassList = new PassList()
  var passNames : Set[String] = Set.empty
  var moduleList : List[Module] = List.empty

  def addPass(pass : ASTAnalysis) {
    Utils.assert(!passNames.contains(pass.passName), "Pass with the same name already exists.")
    passNames += pass.passName
    passes += pass
    pass._manager = Some(this)
  }

  // private version of _run, does not reset or finish.

  def _run(module : Module, context : Scope) : Option[Module] = {
    val init : Option[Module] = Some(module)
    passes.foldLeft(init){
      (mod, pass) => {
        logger.debug("{} => running pass: {} on module: {}", 
            name, pass.passName, (if (mod.isDefined) mod.get.id.toString() else "None"))
        mod.flatMap(pass.visit(_, context))
      }
    }
  }
  // run on a single module.
  def run(module : Module, context : Scope) : Option[Module] = {
    passes.foreach{ _.reset() }
    val modP = _run(module, context)
    passes.foreach(_.finish())
    modP
  }

  // run on a list of modules.
  def run(modules : List[Module]) : List[Module] = {
    logger.debug("moduleList: " + (Utils.join(modules.map(m => m.id.toString()), ",")))
    moduleList = modules
    val modulesP = passes.foldLeft(modules) {
      (mods, pass) => {
        pass.reset()
        val initCtx = Scope.empty
        val initModules = List.empty[Module]
        val init = (initCtx, initModules)
        val modsP = mods.foldRight(init) {
          (m, acc) => {
            val ctx = acc._1
            val modules = acc._2
            logger.debug("{} => running pass: {} on module: {}", name, pass.passName, m.id.toString())
            val mP = pass.visit(m, ctx)
            pass.rewind()
            mP match {
              case None => (ctx, modules)
              case Some(modP) => (ctx +& modP, modP::modules)
            }
          }
        }._2
        pass.finish()
        modsP
      }
    }
    modulesP
  }

  def pass(name : String) : ASTAnalysis = passes.find(_.passName == name).get
  def doesPassExist(name : String) = passNames.contains(name)
  def getPass(name : String) : Option[ASTAnalysis] = passes.find((p) => p.passName == name)
}
