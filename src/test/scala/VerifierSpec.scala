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

object VerifierSpec {
  def expectedFails(filename: String, nFail : Int) {
    val modules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"), true)
    val mainModule = UclidMain.instantiate(modules, l.Identifier("main"), false)
    assert (mainModule.isDefined)
    val results = UclidMain.execute(mainModule.get, new UclidMain.Config())
    assert (results.count((e) => e.result.isFalse) == nFail)
    assert (results.count((e) => e.result.isUndefined) == 0);
  }
}

class BasicVerifierSpec extends FlatSpec {
  "test-assert-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-assert-1.ucl", 0)
  }
  "test-array-0.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-array-0.ucl", 0)
  }
  "test-array-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-array-1.ucl", 0)
  }
  "test-array-1-unsafe.ucl" should "verify all but 4 assertions." in {
    VerifierSpec.expectedFails("./test/test-array-1-unsafe.ucl", 4)
  }
  "test-bv-assign.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bv-assign.ucl", 0)
  }
  "test-bv-fib.ucl" should "verify successfully all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-bv-fib.ucl", 1)
  }
  "test-case-mc91.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-case-mc91.ucl", 0)
  }
  "test-forloop.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-forloop.ucl", 0)
  }
  "test-forloop-0.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-forloop-0.ucl", 0)
  }
  "test-forloop-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-forloop-1.ucl", 0)
  }
  "test-ite.ucl" should "verify all but 6 assertions successfully." in {
    VerifierSpec.expectedFails("./test/test-ite.ucl", 6)
  }
  "test-int-fib.ucl" should "verify successfully all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-int-fib.ucl", 1)
  }
  "test-mc91.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-mc91.ucl", 0)
  }
  "test-record-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-1.ucl", 0)
  }
  "test-tuple-record-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-tuple-record-1.ucl", 0)
  }
  "test-types-0.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-types-0.ucl", 0)
  }
  "test-functions-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-functions-1.ucl", 0)
  }
  "test-exprs-1.ucl" should "verify four assertions and fail to verify two assertions." in {
    VerifierSpec.expectedFails("./test/test-exprs-1.ucl", 2)
  }
  "test-enum-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-enum-1.ucl", 0)
  }
  "test-enum-2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-enum-2.ucl", 0)
  }
  "test-type2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-type2.ucl", 0)
  }
  "test-if-star.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-if-star.ucl", 0)
  }
  "test-assume-1.ucl" should "fail to verify five assertions." in {
    VerifierSpec.expectedFails("./test/test-assume-1.ucl", 5)
  }
}
class ProcedureVerifSpec extends FlatSpec {
  "test-inliner.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-inliner.ucl", 0)
  }
  "test-inliner-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-inliner-1.ucl", 0)
  }
  "test-procedure-checker-2.ucl" should "verify all but 7 invariants successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-2.ucl", 7)
  }
}
class QuantiferVerifSpec extends FlatSpec {
  "test-forall-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-forall-0.ucl", 0)
  }
  "test-exists-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-exists-0.ucl", 0)
  }
}
class ModuleVerifSpec extends FlatSpec {
  "test-modules.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-modules.ucl", 0)
  }
  "test-modules-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-modules-1.ucl", 0)
  }
  "test-type-import.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-type-import.ucl", 0)
  }
  "test-const-import-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-import-1.ucl", 0)
  }
  "test-const-import-2.ucl" should "should failed to verify 4 assertions." in {
    VerifierSpec.expectedFails("./test/test-const-import-2.ucl", 4)
  }
  "test-func-import-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-func-import-1.ucl", 0)
  }
  "test-procedure-postcondition.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-procedure-postcondition.ucl", 1)
  }
  "test-mem-inout.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-meminout.ucl", 0)
  }
  "test-axiom-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-axiom-1.ucl", 0)
  }
}
class LTLVerifSpec extends FlatSpec {
  "test-history-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-history-1.ucl", 0)
  }
  "test-ltl-0-safe.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-0-safe.ucl", 0)
  }
  "test-ltl-0-unsafe.ucl" should " fail to verify 3 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-0-unsafe.ucl", 2)
  }
  "test-ltl-1-safe.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-1-safe.ucl", 0)
  }
  "test-ltl-1-unsafe.ucl" should "fail to verify 6 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-1-unsafe.ucl", 10)
  }
  "test-ltl-2-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-2-holds.ucl", 0)
  }
  "test-ltl-2-fails.ucl" should "fail to verify 4 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-2-fails.ucl", 4)
  }
  "test-ltl-3-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-3-holds.ucl", 0)
  }
  "test-ltl-3-fails.ucl" should "failed to verify 2 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-3-fails.ucl", 2)
  }
  "test-ltl-4-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-4-holds.ucl", 0)
  }
  "test-ltl-4-fails.ucl" should "failed to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-ltl-4-fails.ucl", 1)
  }
}
