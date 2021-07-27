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
 * Author: Elizabeth Polgreen
 *
 * UCLID synthesis tests
 *
 */

package uclid
package test

import org.scalatest.flatspec.AnyFlatSpec
import java.io.File
import uclid.{lang => l}

object SynthesisSpec {
  def expectedFails(filename: String, nFail : Int) : String = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val config = UclidMain.Config().copy(synthesizer=List("cvc4_wait.sh"), sygusFormat = true)
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
class SynthesisSpec extends AnyFlatSpec {
  
  "test-synthesis-0.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-0.ucl", 0)
  }
  "test-synthesis-1.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-1.ucl", 0)
  }
  "test-synthesis-2.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-2.ucl", 0)
  }
  "test-synthesis-3.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-3.ucl", 0)
  }
  "test-synthesis-4.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-4.ucl", 0)
  }
//   "test-synthesis-5.ucl" should "verify all assertions." in {
//     SynthesisSpec.expectedFails("./test/test-synthesis-5.ucl", 0)
//   }
  "test-synthesis-6.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-6.ucl", 0)
  }
  "test-synthesis-7.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-7.ucl", 0)
  }
  "test-synthesis-8.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-8.ucl", 0)
  }
  "test-synthesis-9.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-9.ucl", 0)
  }
  "test-synthesis-11.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-11.ucl", 0)
  }
  "test-synthesis-12.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-12.ucl", 0)
  }
  "test-synthesis-13.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-13.ucl", 0)
  }
  "test-synthesis-grammar-0.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-grammar-0.ucl", 0)
  }
  "test-synthesis-grammar-1.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-grammar-1.ucl", 0)
  }
  "test-synthesis-grammar-4.ucl" should "not execute correctly." in {
    try {
      val filename = "./test/test-synthesis-grammar-4.ucl"
      val config = UclidMain.Config().copy(synthesizer=List("cvc4_wait.sh"), sygusFormat = true)
      val modules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"), true)
      val mainModule = UclidMain.instantiate(config, modules, l.Identifier("main"))
      assert (mainModule.isDefined)
      val results = UclidMain.execute(mainModule.get, config)
      assert(false)
    }
    catch {
      case r : Utils.RuntimeError => 
        assert (r.getMessage().contains("SyGuS grammar type does not match synth-fun"));
    }
  }
  "test-synthesis-grammar-5.ucl" should "not execute correctly." in {
    try {
      val filename = "./test/test-synthesis-grammar-5.ucl"
      val config = UclidMain.Config().copy(synthesizer=List("cvc4_wait.sh"), sygusFormat = true)
      val modules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"), true)
      val mainModule = UclidMain.instantiate(config, modules, l.Identifier("main"))
      assert (mainModule.isDefined)
      val results = UclidMain.execute(mainModule.get, config)
      assert(false)
    }
    catch {
      case r : Utils.RuntimeError => 
        assert (r.getMessage().contains("SyGuS grammar not found"));
    }
  }
  "test-synthesis-grammar-6.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-grammar-6.ucl", 0)
  }
  "test-synthesis-grammar-7.ucl" should "verify all assertions." in {
    SynthesisSpec.expectedFails("./test/test-synthesis-grammar-7.ucl", 0)
  }
}
