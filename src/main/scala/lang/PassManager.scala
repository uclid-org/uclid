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

 * PassManager: runs each AST pass in the order in which they are added to the manager.
 * May eventually add pass dependencies, invalidations and so on to this class. 
 *
 */

package uclid
package lang

import scala.collection.mutable.{ListBuffer,Set} 

class PassManager {
  type PassList = ListBuffer[ASTAnalysis]
  var passes : PassList = new PassList()
  var passNames : Set[String] = Set.empty
  
  def addPass(pass : ASTAnalysis) {
    Utils.assert(!passNames.contains(pass.passName), "Pass with the same name already exists.")
    passNames += pass.passName
    passes += pass
    pass._manager = Some(this)
  }

  // run on a single module.
  def run(module : Module) : Option[Module] = {
    passes.foreach{ _.reset() }
    
    val init : Option[Module] = Some(module)
    return passes.foldLeft(init){
      (mod, pass) => mod.flatMap(pass.visit(_))
    }
  }

  // run on a list of modules.
  def run(modules : List[Module]) : List[Module] = {
    passes.foreach(_.reset())
    modules.foldRight(List.empty[Module]) {
      (m, acc) => run(m) match {
        case Some(m) => m :: acc
        case None => acc
      }
    }
  }

  def pass(name : String) : ASTAnalysis = passes.find(_.passName == name).get
  def doesPassExist(name : String) = passNames.contains(name)
  def getPass(name : String) : Option[ASTAnalysis] = passes.find((p) => p.passName == name)
}