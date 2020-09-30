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
 * Author: Pramod Subramanyan, Shubham Sahai
 *
 * Main file for the UCLID model counter.
 *
 */
package uclid.extensions.modelcounts

import uclid.UclidMain
import uclid.{lang => l}
import uclid.Utils


object UMCMain {
  /** Executes regular UCLID5 on the processed module. */
  def runProcessedModel(module : l.Module) : Unit = {
    val config = UclidMain.Config()
    val mainModuleName = l.Identifier("main")
    val modules = UclidMain.compileModules(List(module), mainModuleName, false)
    val mainModule = UclidMain.instantiate(config, modules, mainModuleName, true)
    mainModule match {
      case Some(m) => UclidMain.execute(m, config)
      case None    =>
        throw new Utils.ParserError("Unable to find main module", None, None)
    }
  }
  
  def checkModel(f: java.io.File, config: UclidMain.Config) {
    val module = UMCParser.parseUMCModel(f)
    println("Parsed module: " + module.id.toString())
    println(module.toString())
    val moduleP = new UMCRewriter(module).process()
    println("\nModule after rewriting: ")
    println(moduleP.toString())
    runProcessedModel(moduleP)
  }
}
