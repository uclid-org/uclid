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
 *
 * UCLID verification engine tests.
 *
 */

package uclid
package test

import org.scalatest.FlatSpec
import uclid.{lang => l}

object VerifierSpec {
  def expectedFails(filename: String, nFail : Int) {
    val modules = UclidMain.compile(List(filename), lang.Identifier("main"), true)
    val mainModule = UclidMain.instantiate(modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    val results = UclidMain.execute(mainModule.get)
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
  "test-inliner.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-inliner.ucl", 0)
  }
  "test-inliner-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-inliner-1.ucl", 0)
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
  "test-type2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-type2.ucl", 0)
  }
  "test-if-star.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-if-star.ucl", 0)
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
  "test-const-import.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-import.ucl", 0)
  }
  "test-procedure-postcondition.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-procedure-postcondition.ucl", 1)
  }
  "test-mem-inout.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-meminout.ucl", 0)
  }
  "test-axiom-1.ucl" should "should verify all assertions." in {
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
  "test-ltl-0-unsafe.ucl" should "should fail to verify 3 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-0-unsafe.ucl", 3)
  }
  "test-ltl-1-safe.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-1-safe.ucl", 0)
  }
  "test-ltl-1-unsafe.ucl" should "should fail to verify 6 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-1-unsafe.ucl", 6)
  }
}
