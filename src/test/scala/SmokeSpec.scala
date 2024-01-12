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
 * Author: Federico Mora (based on Elizabeth Polgreen's Oracle Spec)
 *
 * UCLID smoke testing tests
 *
 */

package uclid
package test

import org.scalatest.flatspec.AnyFlatSpec
import java.io.File
import uclid.{lang => l}

object SmokeSpec {
  def runSmokeTesting(filename: String) : (List[String], List[String], List[String]) = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val config = ConfigCons.createConfig(filename).copy(smoke=true)
    val modules = UclidMain.compile(config, lang.Identifier("main"), true)
    val mainModule = UclidMain.instantiate(config, modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    val results = UclidMain.execute(mainModule.get, config)
    return Utils.smokeTestCounter(results)
  }
}
class SmokeSpec extends AnyFlatSpec {
  
  "test-smoke-bmc.ucl" should "give two warnings." in {
    val (reachableLines, unreachableLines, undeterminedLines) = SmokeSpec.runSmokeTesting("./test/test-smoke-bmc.ucl")
    unreachableLines.foreach(l => info(l))
    assertResult(2){unreachableLines.length}
  }  
  "test-smoke-induction.ucl" should "give no warnings." in {
    val (reachableLines, unreachableLines, undeterminedLines) = SmokeSpec.runSmokeTesting("./test/test-smoke-induction.ucl")
    unreachableLines.foreach(l => info(l))
    assertResult(0){unreachableLines.length}
  }  
  "test-smoke-multiple-modules.ucl" should "give one warning." in {
    val (reachableLines, unreachableLines, undeterminedLines) = SmokeSpec.runSmokeTesting("./test/test-smoke-multiple-modules.ucl")
    unreachableLines.foreach(l => info(l))
    assertResult(1){unreachableLines.length}
  }
}
