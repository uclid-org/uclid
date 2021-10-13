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

import org.scalatest.flatspec.AnyFlatSpec
import java.io.File
import uclid.{lang => l}

object SMTLIB2Spec {
  def expectedFails(filename: String, nFail : Int) : String = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val config = UclidMain.Config().copy(smtSolver=List("z3", "-smt2", "-in"))
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
class SMTLIB2Spec extends AnyFlatSpec {
  
"test-int-fib.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-int-fib.ucl", 1)
  }
  "test-assert-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-assert-1.ucl", 0)
  }
  "test-array-0.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-array-0.ucl", 0)
  }
  "test-array-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-array-1.ucl", 0)
  }
  "test-array-2.ucl" should "fail to verify 1 assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-array-2.ucl", 1)
  }
  "array-update.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/array-update.ucl", 0)
  }
  "test-array-1-unsafe.ucl" should "verify all but 4 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-array-1-unsafe.ucl", 4)
  }
  "test-bv-fib.ucl" should "fail to verify 1 assertion" in {
    SMTLIB2Spec.expectedFails("./test/test-bv-fib.ucl", 1)
  }
  "test-case-mc91.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-case-mc91.ucl", 0)
  }
  "test-int-fib.ucl" should "verify successfully all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-int-fib.ucl", 1)
  }
  "test-mc91.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-mc91.ucl", 0)
  }
  "test-if-star.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-if-star.ucl", 0)
  }
  "test-if-star-2.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-if-star-2.ucl", 0)
  }
  "test-scheduler-0.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-scheduler-0.ucl", 0)
  }
  "test-assume-1.ucl" should "fail to verify five assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-assume-1.ucl", 5)
  }
  "test-assert-2.ucl" should "fail to verify five assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-assert-2.ucl", 5)
  }
  "test-assert-3.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-assert-3.ucl", 0)
  }
  "test-primed-variables-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-primed-variables-1.ucl", 0)
  }
  "test-assume-primed-var.ucl" should "verify all but 6 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-assume-primed-var.ucl", 6)
  }
  "test-bv-assign.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-bv-assign.ucl", 0)
  }
  "test-forloop.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-forloop.ucl", 0)
  }
  "test-forloop-0.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-forloop-0.ucl", 0)
  }
  "test-forloop-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-forloop-1.ucl", 0)
  }
  // "test-ite.ucl" should "verify all but 6 assertions successfully." in {
  //   SMTLIB2Spec.expectedFails("./test/test-ite.ucl", 6)
  // }
  "test-bit-concat.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-bit-concat.ucl", 0)
  }
  "test-bv-sign-ext-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-bv-sign-ext-1.ucl", 0)
  }
  "test-bv-zero-ext-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-bv-zero-ext-1.ucl", 0)
  }
  "test-bv-left-shift-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-bv-left-shift-1.ucl", 0)
  }
  "test-bv-a-right-shift-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-bv-a-right-shift-1.ucl", 0)
  }
  "test-bv-l-right-shift-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-bv-l-right-shift-1.ucl", 0)
  }
  "test-record-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-record-1.ucl", 0)
  }
  "test-tuple-record-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-tuple-record-1.ucl", 0)
  }
  "test-functions-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-functions-1.ucl", 0)
  }
  "test-conflicting-assumptions.ucl" should "verify all but 1 assertion" in {
    SMTLIB2Spec.expectedFails("./test/test-conflicting-assumptions.ucl", 1)
  }
  "test-exprs-1.ucl" should "verify four assertions and fail to verify two assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-exprs-1.ucl", 2)
  }
  "test-enum-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-enum-1.ucl", 0)
  }
  "test-enum-2.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-enum-2.ucl", 0)
  }
  "havoc_ordering.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/havoc_ordering.ucl", 0)
  }
  "test-array-new.ucl" should "fail to verify 5 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-array-new.ucl", 5)
  }
  "test-subst-1.ucl" should "fail to verify 2 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-subst-1.ucl", 2)
  }
  "test-const-array.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-const-array.ucl", 1)
  }
  "test-record-havoc.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-record-havoc.ucl", 0)
  }
  "test-const-array-2.ucl" should "verify all but 6 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-const-array-2.ucl", 6)
  }
  "test-const-array-3.ucl" should "verify all but 4 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-const-array-3.ucl", 4)
  }
  "test-array-update.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-array-update.ucl", 0)
  }
  "test-unsigned-comparators-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-unsigned-comparators-1.ucl", 0)
  }
  // "test-bv2int.ucl" should "verify all but one assertion." in {
  //   SMTLIB2Spec.expectedFails("./test/test-bv2int.ucl", 1)
  // }
  "test-range-expr.ucl" should "verify all but two assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-range-expr.ucl", 2)
  }
  "test-multiply-divide.ucl" should "verify all but one assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-multiply-divide.ucl", 1)
  }
  "test-multiply-divide-subtract-chaining.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-multiply-divide-subtract-chaining.ucl", 1)
  }
  "test-inliner.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-inliner.ucl", 0)
  }
  "test-inliner-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-inliner-1.ucl", 0)
  }
  "test-procedure-inline.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-inline.ucl", 0)
  }
  "test-procedure-inline-2.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-inline-2.ucl", 0)
  }
  "test-procedure-inline-3.ucl" should "verify all but 1" in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-inline-3.ucl", 1)
  }
  "test-procedure-noinline.ucl" should "verify all but 1 assertion successfully" in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-noinline.ucl", 1)
  }
  "test-procedure-noinline-2.ucl" should "fail" in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-noinline-2.ucl", 1)
  }
  "test-procedure-checker-2.ucl" should "verify all but 4 invariants successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-checker-2.ucl", 4)
  }
  "test-procedure-checker-3.ucl" should "verify all but one invariants successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-checker-3.ucl", 1)
  }
  "test-procedure-checker-4.ucl" should "verify all invariants successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-checker-4.ucl", 0)
  }
  "test-procedure-checker-5.ucl" should "verify all invariants successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-checker-5.ucl", 0)
  }
  "test-procedure-checker-6.ucl" should "verify all invariants successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-checker-6.ucl", 0)
  }
  "test-procedure-checker-7.ucl" should "fail to verify 4 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-checker-7.ucl", 4)
  }
  "test-procedure-checker-8.ucl" should "fail to verify 4 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-checker-8.ucl", 4)
  }
  "test-procedure-global-axiom.ucl" should "verify all invariants successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-global-axiom.ucl", 0)
  }
  "test-procedure-postcondition-0.ucl" should "fail to verify 1 assertion" in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-postcondition-0.ucl", 1)
  }
  "test-procedure-postcondition-3.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-postcondition-3.ucl", 0)
  }
  "test-procedure-postcondition-4.ucl" should "fail to verify 4 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-postcondition-4.ucl", 4)
  }
  "proc_precond_1.ucl" should "fail to verify 4 assertions" in {
    val output = SMTLIB2Spec.expectedFails("./test/proc_precond_1.ucl", 4)
    assert (output.contains("precondition @ "))
    assert (output.contains("proc_precond_1.ucl, line 8"))
  }
  "proc_requires_1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/proc_requires_1.ucl", 0)
  }
  "proc_ensures_1.ucl" should "fail to verify 2 assertions." in {
    SMTLIB2Spec.expectedFails("./test/proc_ensures_1.ucl", 2)
  }
  "proc_ensures_2.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/proc_ensures_2.ucl", 0)
  }
  "module_assump_1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/module_assump_1.ucl", 0)
  }
  "test-while-0.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-while-0.ucl", 0)
  }
  "test-while-1.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-while-1.ucl", 0)
  }
  "test-while-2.ucl" should "fail to verify 2 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-while-2.ucl", 2)
  }
  "test-while-3.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-while-3.ucl", 0)
  }
  "test-while-4.ucl" should "fail to verify 6 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-while-4.ucl", 6)
  }
  "test-block-var.ucl" should "fail to verify 2 assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-block-var.ucl", 2)
  }
  "test-distinct-op.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-distinct-op.ucl", 0)
  }
  "test-procedure-old-1.ucl" should "fail to verify 1 assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-old-1.ucl", 1)
  }
  "test-old-instance-var-0.ucl" should "verify all assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-old-instance-var-0.ucl", 0)
  }
  "test-old-instance-var-1.ucl" should "verify all assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-old-instance-var-1.ucl", 0)
  }
  "test-old-instance-var-2.ucl" should "verify all assertions" in {
    SMTLIB2Spec.expectedFails("./test/test-old-instance-var-2.ucl", 0)
  }
  "test-k-induction-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-k-induction-1.ucl", 0)
  }
  "test-k-induction-2.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-k-induction-2.ucl", 1)
  }
  "test-k-induction-3.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-k-induction-3.ucl", 0)
  }
  "test-k-induction-4.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-k-induction-4.ucl", 1)
  }
  "induction-pre-control-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/induction-pre-control-1.ucl", 0)
  }
  "induction-pre-control-2.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/induction-pre-control-2.ucl", 1)
  }
  "induction-pre-control-3.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/induction-pre-control-3.ucl", 0)
  }
  "induction-pre-control-4.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/induction-pre-control-4.ucl", 1)
  }
  "induction-pre-control-5.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/induction-pre-control-5.ucl", 1)
  }
  "test-tuple.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-tuple.ucl", 0)
  }
  "test-forall-0.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-forall-0.ucl", 0)
  }
  "test-exists-0.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-exists-0.ucl", 0)
  }


  "test-modules.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-modules.ucl", 0)
  }
  "test-modules-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-modules-1.ucl", 0)
  }
  "test-modules-5.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-modules-5.ucl", 0)
  }
  "test-modules-6.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-modules-6.ucl", 0)
  }
  // "test-type-import.ucl" should "verify all assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/test-type-import.ucl", 0)
  // }
  "test-const-import-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-const-import-1.ucl", 0)
  }
  "test-const-import-2.ucl" should "fail to verify 4 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-const-import-2.ucl", 4)
  }
  "test-const-import-3.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-const-import-3.ucl", 0)
  }
  "test-const-import-4.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-const-import-4.ucl", 0)
  }
  "test-func-import-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-func-import-1.ucl", 0)
  }
  "test-func-import-2.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-func-import-2.ucl", 0)
  }
  "test-func-import-3.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-func-import-3.ucl", 0)
  }
  // "test-func-import-4.ucl" should "verify all assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/test-func-import-4.ucl", 0)
  // }
  "test-def-import-0.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-def-import-0.ucl", 0)
  }
  "test-def-import-4.ucl" should "verify 2 assertions and fail 1." in {
    SMTLIB2Spec.expectedFails("./test/test-def-import-4.ucl", 1)
  }
  "test-procedure-postcondition-1.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-procedure-postcondition-1.ucl", 1)
  }
  "test-meminout.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-meminout.ucl", 0)
  }
  "test-axiom-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-axiom-1.ucl", 0)
  }
  "test-axiom-2.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-axiom-2.ucl", 0)
  }
  "test-nested-instance-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-nested-instance-1.ucl", 0)
  }
  "test-instance-procedure-call-0.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-instance-procedure-call-0.ucl", 1)
  }
  "test-instance-procedure-call-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-instance-procedure-call-1.ucl", 0)
  }
  "test-instance-procedure-call-3.ucl" should "verify all but one." in {
    SMTLIB2Spec.expectedFails("./test/test-instance-procedure-call-3.ucl", 1)
  }
  "test-instance-procedure-call-4.ucl" should "verify all but one." in {
    SMTLIB2Spec.expectedFails("./test/test-instance-procedure-call-4.ucl", 1)
  }
  "test-instance-procedure-call-5.ucl" should "verify all but two." in {
    SMTLIB2Spec.expectedFails("./test/test-instance-procedure-call-5.ucl", 2)
  }
  "test-instance-procedure-call-7.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-instance-procedure-call-7.ucl", 0)
  }
  "sp-basic.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/sp-basic.ucl", 0)
  }
  "issue-187b.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/issue-187b.ucl", 0)
  }
  "test-redundant-assign.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-redundant-assign.ucl", 0)
  }


  "test-history-1.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-history-1.ucl", 0)
  }
  // "test-ltl-0-safe.ucl" should "verify all assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/test-ltl-0-safe.ucl", 0)
  // }
  "test-ltl-0-unsafe.ucl" should " fail to verify 2 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-0-unsafe.ucl", 2)
  }
  // "test-ltl-1-safe.ucl" should "verify all assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/test-ltl-1-safe.ucl", 0)
  // }
  // "test-ltl-1-unsafe.ucl" should "fail to verify 10 assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/test-ltl-1-unsafe.ucl", 10)
  // }
  "test-ltl-2-holds.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-2-holds.ucl", 0)
  }
  "test-ltl-2-fails.ucl" should "fail to verify 4 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-2-fails.ucl", 4)
  }
  "test-ltl-3-holds.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-3-holds.ucl", 0)
  }
  "test-ltl-3-fails.ucl" should "fail to verify 2 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-3-fails.ucl", 2)
  }
  "test-ltl-4-holds.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-4-holds.ucl", 0)
  }
  "test-ltl-4-fails.ucl" should "fail to verify 1 assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-4-fails.ucl", 1)
  }
  "test-ltl-5-holds.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-5-holds.ucl", 0)
  }
  "test-ltl-5-fails.ucl" should "fail to verify 2 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-5-fails.ucl", 2)
  }
  // "test-ltl-6-fails.ucl" should "fail to verify 4 assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/test-ltl-6-fails.ucl", 4)
  // }
  "test-ltl-7-holds.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-7-holds.ucl", 0)
  }
  "test-ltl-7a-fails.ucl" should "fail to verify 6 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-7a-fails.ucl", 6)
  }
  "test-ltl-7b-fails.ucl" should "fail to verify 5 assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-ltl-7b-fails.ucl", 5)
  }
  // "queue-ltl.ucl" should "verify all assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/queue-ltl.ucl", 0)
  // }
  // "ltl-eventually-1.ucl" should "fail to verify 3 assertions." in {
  //   SMTLIB2Spec.expectedFails("./test/ltl-eventually-1.ucl", 3)
  // }
  "ltl-toy-0.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/ltl-toy-0.ucl", 0)
  }
  "ltl-toy-1.ucl" should "fail to verify 11 assertions." in {
    SMTLIB2Spec.expectedFails("./test/ltl-toy-1.ucl", 11)
  }
  "test-smtlib-array.ucl" should "verify successfully." in {
    SMTLIB2Spec.expectedFails("./test/test-smtlib-array.ucl", 0)
  }

  "test-hyperproperty-0.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-hyperproperty-0.ucl", 0)
  }
  
  "test-hyperproperty-4.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-hyperproperty-4.ucl", 0)
  }

  "test-smtlib-consts.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-smtlib-consts.ucl", 0)
  }

  "test-too-many-vars-error.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-too-many-vars-error.ucl", 0)
  }
  "test-macro-1.ucl" should "fail to verify 1 assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-macro-1.ucl", 1)
  }
  "test-macro-2.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-macro-2.ucl", 0)
  }
  "test-macro-3.ucl" should "verify all assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-macro-3.ucl", 0)
  }
  "test-macro-4.ucl" should "fail to verify 1 assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-macro-4.ucl", 1)
  }
  "test-float.ucl" should "fail to verify 6 assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-float.ucl", 6)
  }
  "test-float.ucl" should "fail to verify 3 assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-float-2.ucl", 3)
  }
}
