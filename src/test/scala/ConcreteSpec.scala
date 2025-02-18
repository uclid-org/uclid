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
 * Author: Leiqi Ye
 *
 * UCLID concrte tests
 *
 */

package uclid
package test

import org.scalatest.flatspec.AnyFlatSpec
import java.io.File
import uclid.{lang => l}

object ConcreteSpec {
  def expectedFails(filename: String, nFail : Int) : String = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val config = UclidMain.Config().copy(simulate=true)
    val modules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"), true)
    val mainModule = UclidMain.instantiate(config, modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    val results = UclidMain.execute(mainModule.get, config)
    val outputString = UclidMain.stringOutput.toString()
    assert (results.count((e) => e.result.isFalse) == nFail)
    assert (results.count((e) => e.result.isUndefined) == 0)
    outputString
  }
}
class ConcreteSpec extends AnyFlatSpec {
    "concrete-0.ucl" should "fail one assertion." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-0.ucl", 1)
    }
    "concrete-1.ucl" should "pass." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-1.ucl", 0)
    }
    "concrete-2.ucl" should "pass." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-2.ucl", 0)
    }
    "concrete-3.ucl" should "fail one assertion." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-3.ucl", 1)
    }
    "concrete-4.ucl" should "pass." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-4.ucl", 0)
    }
    "concrete-5.ucl" should "pass." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-5.ucl", 0)
    }
    "concrete-6.ucl" should "fail one assertion." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-6.ucl", 1)
    }
    "concrete-7.ucl" should "pass." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-7.ucl", 0)
    }
    "concrete-8.ucl" should "pass." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-8.ucl", 1)
    }
    "concrete-9.ucl" should "fail one assertion." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-9.ucl", 1)
    }
    "concrete-10.ucl" should "fail one assertion." in {
        ConcreteSpec.expectedFails("./test/concrete/concrete-10.ucl", 1)
    }
}
