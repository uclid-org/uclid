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
 *
 * UCLID verification engine tests.
 *
 */

package uclid
package test

import org.scalatest.FlatSpec
import java.io.File
import uclid.{lang => l}

object SMTLIB2Spec {
  def expectedFails(filename: String, nFail : Int) : String = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val config = UclidMain.Config().copy(smtSolver=List("z3", "-smt2", "-in"))
    val modules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"), true)
    val mainModule = UclidMain.instantiate(config, modules, l.Identifier("main"), false)
    assert (mainModule.isDefined)
    val results = UclidMain.execute(mainModule.get, config)
    val outputString = UclidMain.stringOutput.toString()
    assert (results.count((e) => e.result.isFalse) == nFail)

    assert (results.count((e) => e.result.isUndefined) == 0)
    outputString
  }
}
class SMTLIB2Spec extends FlatSpec {
  "test-int-fib.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-int-fib.ucl", 1)
  }
  "test-array-0.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-array-0.ucl", 0)
  }
  // the test below is commented out because it errors out.
  ignore /*"test-array-1-unsafe.ucl"*/ should "verify all but 4 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-array-1-unsafe.ucl", 4)
  }
}
