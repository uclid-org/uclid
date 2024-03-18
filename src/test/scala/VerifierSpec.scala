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

import org.json4s.jackson.JsonMethods._
import org.json4s.JString

object VerifierSpec {
  def expectedFails(filename: String, nFail : Int, config: Option[UclidMain.Config]=None) : String = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val compileConfig = if (config.isDefined) config.get else ConfigCons.createConfig(filename)
    val modules = UclidMain.compile(compileConfig, lang.Identifier("main"), true)
    val instantiateConfig = UclidMain.Config() 
    val mainModule = UclidMain.instantiate(instantiateConfig, modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    // val config = UclidMain.Config("main", List("/usr/bin/z3", "-in", "-smt2"), List.empty)
    val results = UclidMain.execute(mainModule.get, instantiateConfig)
    val outputString = UclidMain.stringOutput.toString()
    assert (results.count((e) => e.result.isFalse) == nFail)

    assert (results.count((e) => e.result.isUndefined) == 0)
    outputString
  }

  def expectedFailsMultipleFiles(filenames: List[String], nFail : Int, config: Option[UclidMain.Config]=None) : String = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val compileConfig = if (config.isDefined) config.get else UclidMain.Config(files=filenames.map(f => new File(f)))
    val modules = UclidMain.compile(compileConfig, lang.Identifier("main"), true)
    val instantiateConfig = UclidMain.Config()
    val mainModule = UclidMain.instantiate(instantiateConfig, modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    // val config = UclidMain.Config("main", List("/usr/bin/z3", "-in", "-smt2"), List.empty)
    val results = UclidMain.execute(mainModule.get, instantiateConfig)
    val outputString = UclidMain.stringOutput.toString()
    assert (results.count((e) => e.result.isFalse) == nFail)
    assert (results.count((e) => e.result.isUndefined) == 0)
    outputString
  }
}
class VerifierSanitySpec extends AnyFlatSpec {
  "test-int-fib.ucl" should "verify all but one assertion." in {
    SMTLIB2Spec.expectedFails("./test/test-int-fib.ucl", 1)
  }
  "test-assert-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-assert-1.ucl", 0)
  }
  "test-array-0.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-array-0.ucl", 0)
  }
  "test-array-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-array-1.ucl", 0)
  }
  "test-array-2.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-array-2.ucl", 1)
  }
  "array-update.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/array-update.ucl", 0)
  }
  "test-array-1-unsafe.ucl" should "verify all but 4 assertions." in {
    VerifierSpec.expectedFails("./test/test-array-1-unsafe.ucl", 4)
  }
  "test-bv-fib.ucl" should "fail to verify 1 assertion" in {
    VerifierSpec.expectedFails("./test/test-bv-fib.ucl", 1)
  }
  "test-case-mc91.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-case-mc91.ucl", 0)
  }
  "test-int-fib.ucl" should "verify successfully all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-int-fib.ucl", 1)
  }
  "test-mc91.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-mc91.ucl", 0)
  }
  "test-if-star.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-if-star.ucl", 0)
  }
  "test-if-star-2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-if-star-2.ucl", 0)
  }
  "test-scheduler-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-scheduler-0.ucl", 0)
  }
  "test-assume-1.ucl" should "fail to verify five assertions." in {
    VerifierSpec.expectedFails("./test/test-assume-1.ucl", 5)
  }
  "test-assert-2.ucl" should "fail to verify five assertions." in {
    VerifierSpec.expectedFails("./test/test-assert-2.ucl", 5)
  }
  "test-assert-3.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-assert-3.ucl", 0)
  }
  "test-assert-4.ucl" should "fail to verify two assertions." in {
    val output = SMTLIB2Spec.expectedFails("./test/test-assert-4.ucl", 2)
    assert (output.contains("1000"))
  }
  "test-assert-5.ucl" should "fail to verify one assertions." in {
    SMTLIB2Spec.expectedFails("./test/test-assert-5.ucl", 1)
  }
  "test-primed-variables-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-primed-variables-1.ucl", 0)
  }
  "test-assume-primed-var.ucl" should "verify all but 6 assertions." in {
    VerifierSpec.expectedFails("./test/test-assume-primed-var.ucl", 6)
  }
  "test-real-1.ucl" should "verify all assertions." in{
    VerifierSpec.expectedFails("./test/test-real-1.ucl", 0)
  }
  "test-real-2.ucl" should "fail to verify 3 assertions." in{
    VerifierSpec.expectedFails("./test/test-real-2.ucl", 3)
  }
}
class BasicVerifierSpec extends AnyFlatSpec {
  "test-bv-assign.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bv-assign.ucl", 0)
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
  // "test-ite.ucl" should "verify all but 6 assertions successfully." in {
  //   VerifierSpec.expectedFails("./test/test-ite.ucl", 6)
  // }
  "test-bit-concat.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bit-concat.ucl", 0)
  }
  "test-bv-sign-ext-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bv-sign-ext-1.ucl", 0)
  }
  "test-bv-zero-ext-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bv-zero-ext-1.ucl", 0)
  }
  "test-bv-left-shift-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bv-left-shift-1.ucl", 0)
  }
  "test-bv-a-right-shift-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bv-a-right-shift-1.ucl", 0)
  }
  "test-bv-l-right-shift-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-bv-l-right-shift-1.ucl", 0)
  }
  "test-record-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-1.ucl", 0)
  }
  "test-record-array.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-array-record.ucl", 0)
  }
  "test-record-update-op-1.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-1.ucl", 1)
  }
  "test-record-update-op-5.ucl" should "fail to verify 2 assertions." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-5.ucl", 2)
  }
  "test-record-update-op-6.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-6.ucl", 0)
  }
  "test-record-update-op-7.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-7.ucl", 1)
  }
  "test-record-update-op-8.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-8.ucl", 1)
  }
  "test-record-update-op-11.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-11.ucl", 1)
  }

  "test-const-record-1.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-const-record-1.ucl", 1)
  }
  "test-const-record-4.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-record-4.ucl", 0)
  }
  "test-const-record-6.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-const-record-6.ucl", 1)
  }

  "test-tuple-record-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-tuple-record-1.ucl", 0)
  }
  "test-functions-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-functions-1.ucl", 0)
  }
  "test-conflicting-assumptions.ucl" should "verify all but 1 assertion" in {
    VerifierSpec.expectedFails("./test/test-conflicting-assumptions.ucl", 1)
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
  "havoc_ordering.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/havoc_ordering.ucl", 0)
  }
  "test-array-new.ucl" should "fail to verify 5 assertions" in {
    VerifierSpec.expectedFails("./test/test-array-new.ucl", 5)
  }
  "test-subst-1.ucl" should "fail to verify 2 assertions" in {
    VerifierSpec.expectedFails("./test/test-subst-1.ucl", 2)
  }
  "test-const-array.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-const-array.ucl", 1)
  }
  "test-record-havoc.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-record-havoc.ucl", 0)
  }
  "test-const-array-2.ucl" should "verify all but 6 assertions." in {
    VerifierSpec.expectedFails("./test/test-const-array-2.ucl", 6)
  }
  "test-const-array-3.ucl" should "verify all but 4 assertions." in {
    VerifierSpec.expectedFails("./test/test-const-array-3.ucl", 4)
  }
  "test-array-update.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-array-update.ucl", 0)
  }
  "test-unsigned-comparators-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-unsigned-comparators-1.ucl", 0)
  }
  "test-bv2int.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-bv2int.ucl", 1)
  }
  "test-range-expr.ucl" should "verify all but two assertions." in {
    VerifierSpec.expectedFails("./test/test-range-expr.ucl", 2)
  }
  "test-multiply-divide.ucl" should "verify all but one assertions." in {
    VerifierSpec.expectedFails("./test/test-multiply-divide.ucl", 1)
  }
  "test-multiply-divide-subtract-chaining.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-multiply-divide-subtract-chaining.ucl", 1)
  }
  "test-smtlib-consts.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-smtlib-consts.ucl", 0)
  }
}
class ProcedureVerifSpec extends AnyFlatSpec {
  "test-inliner.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-inliner.ucl", 0)
  }
  "test-inliner-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-inliner-1.ucl", 0)
  }
  "test-procedure-inline.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-inline.ucl", 0)
  }
  "test-procedure-inline-2.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-inline-2.ucl", 0)
  }
  "test-procedure-inline-3.ucl" should "verify all but 1" in {
    VerifierSpec.expectedFails("./test/test-procedure-inline-3.ucl", 1)
  }
  "test-procedure-noinline.ucl" should "verify all but 1 assertion successfully" in {
    VerifierSpec.expectedFails("./test/test-procedure-noinline.ucl", 1)
  }
  "test-procedure-noinline-2.ucl" should "fail" in {
    VerifierSpec.expectedFails("./test/test-procedure-noinline-2.ucl", 1)
  }
  "test-procedure-checker-2.ucl" should "verify all but 4 invariants successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-2.ucl", 4)
  }
  "test-procedure-checker-3.ucl" should "verify all but one invariants successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-3.ucl", 1)
  }
  "test-procedure-checker-4.ucl" should "verify all invariants successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-4.ucl", 0)
  }
  "test-procedure-checker-5.ucl" should "verify all invariants successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-5.ucl", 0)
  }
  "test-procedure-checker-6.ucl" should "verify all invariants successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-6.ucl", 0)
  }
  "test-procedure-checker-7.ucl" should "fail to verify 4 assertions" in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-7.ucl", 4)
  }
  "test-procedure-checker-8.ucl" should "fail to verify 4 assertions" in {
    VerifierSpec.expectedFails("./test/test-procedure-checker-8.ucl", 4)
  }
  "test-procedure-global-axiom.ucl" should "verify all invariants successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-global-axiom.ucl", 0)
  }
  "test-procedure-postcondition-0.ucl" should "fail to verify 1 assertion" in {
    VerifierSpec.expectedFails("./test/test-procedure-postcondition-0.ucl", 1)
  }
  "test-procedure-postcondition-3.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-procedure-postcondition-3.ucl", 0)
  }
  "test-procedure-postcondition-4.ucl" should "fail to verify 4 assertions" in {
    VerifierSpec.expectedFails("./test/test-procedure-postcondition-4.ucl", 4)
  }
  "proc_precond_1.ucl" should "fail to verify 4 assertions" in {
    val output = VerifierSpec.expectedFails("./test/proc_precond_1.ucl", 4)
    assert (output.contains("precondition @ "))
    assert (output.contains("proc_precond_1.ucl, line 8"))
  }
  "proc_requires_1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/proc_requires_1.ucl", 0)
  }
  "proc_ensures_1.ucl" should "fail to verify 2 assertions." in {
    VerifierSpec.expectedFails("./test/proc_ensures_1.ucl", 2)
  }
  "proc_ensures_2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/proc_ensures_2.ucl", 0)
  }
  "module_assump_1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/module_assump_1.ucl", 0)
  }
  "test-while-0.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-while-0.ucl", 0)
  }
  "test-while-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-while-1.ucl", 0)
  }
  "test-while-2.ucl" should "fail to verify 2 assertions" in {
    VerifierSpec.expectedFails("./test/test-while-2.ucl", 2)
  }
  "test-while-3.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-while-3.ucl", 0)
  }
  "test-while-4.ucl" should "fail to verify 6 assertions" in {
    VerifierSpec.expectedFails("./test/test-while-4.ucl", 6)
  }
  "test-block-var.ucl" should "fail to verify 2 assertions" in {
    VerifierSpec.expectedFails("./test/test-block-var.ucl", 2)
  }
  "test-distinct-op.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-distinct-op.ucl", 0)
  }
  "test-procedure-old-1.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-procedure-old-1.ucl", 1)
  }
  "test-old-instance-var-0.ucl" should "verify all assertions" in {
    VerifierSpec.expectedFails("./test/test-old-instance-var-0.ucl", 0)
  }
  "test-old-instance-var-1.ucl" should "verify all assertions" in {
    VerifierSpec.expectedFails("./test/test-old-instance-var-1.ucl", 0)
  }
  "test-old-instance-var-2.ucl" should "verify all assertions" in {
    VerifierSpec.expectedFails("./test/test-old-instance-var-2.ucl", 0)
  }
  "test-mod-set-analysis-4.ucl" should "verify all assertions" in {
    VerifierSpec.expectedFails("./test/test-mod-set-analysis-4.ucl", 0, Some(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-4.ucl")))
  }
  "test-mod-set-analysis-5.ucl" should "verify all assertions" in {
    VerifierSpec.expectedFails("./test/test-mod-set-analysis-5.ucl", 0, Some(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-5.ucl")))
  }
  "test-mod-set-analysis-7.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-mod-set-analysis-7.ucl", 1, Some(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-7.ucl")))
  }
}
class InductionVerifSpec extends AnyFlatSpec {
  "test-k-induction-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-k-induction-1.ucl", 0)
  }
  "test-k-induction-2.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-k-induction-2.ucl", 1)
  }
  "test-k-induction-3.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-k-induction-3.ucl", 0)
  }
  "test-k-induction-4.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-k-induction-4.ucl", 1)
  }
  "induction-pre-control-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/induction-pre-control-1.ucl", 0)
  }
  "induction-pre-control-2.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/induction-pre-control-2.ucl", 1)
  }
  "induction-pre-control-3.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/induction-pre-control-3.ucl", 0)
  }
  "induction-pre-control-4.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/induction-pre-control-4.ucl", 1)
  }
  "induction-pre-control-5.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/induction-pre-control-5.ucl", 1)
  }
  "test-tuple.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-tuple.ucl", 0)
  }
  "test-record-update-op-9.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-9.ucl", 0)
  }
  "test-record-update-op-10.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-record-update-op-10.ucl", 0)
  }
  "test-const-record-3.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-record-3.ucl", 0)
  }
  "test-const-record-7.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-record-7.ucl", 0)
  }

}
class QuantifierVerifSpec extends AnyFlatSpec {
  "test-forall-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-forall-0.ucl", 0)
  }
  "test-exists-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-exists-0.ucl", 0)
  }
}
class GroupVerifSpec extends AnyFlatSpec {
  "test-group-0.ucl" should "verify one and fail one assertion." in {
    VerifierSpec.expectedFails("./test/test-group-0.ucl", 1)
  }
  "test-group-1.ucl" should "verify one and fail one assertion." in {
    VerifierSpec.expectedFails("./test/test-group-1.ucl", 1)
  }
  "test-group-2.ucl" should "verify one and fail one assertion." in {
    VerifierSpec.expectedFails("./test/test-group-2.ucl", 1)
  }
  "test-group-3.ucl" should "verify one and fail one assertion." in {
    VerifierSpec.expectedFails("./test/test-group-3.ucl", 1)
  }
  "test-group-4.ucl" should "verify one and fail one assertion." in {
    VerifierSpec.expectedFails("./test/test-group-4.ucl", 1)
  }
}
class ModuleVerifSpec extends AnyFlatSpec {
  "test-modules.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-modules.ucl", 0)
  }
  "test-modules-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-modules-1.ucl", 0)
  }
  "test-modules-5.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-modules-5.ucl", 0)
  }
  "test-modules-6.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-modules-6.ucl", 0)
  }
  "test-module-import-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-module-import-0.ucl", 0)
  }
  "test-type-import.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-type-import.ucl", 0)
  }
  "test-const-import-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-import-1.ucl", 0)
  }
  "test-const-import-2.ucl" should "fail to verify 4 assertions." in {
    VerifierSpec.expectedFails("./test/test-const-import-2.ucl", 4)
  }
  "test-const-import-3.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-import-3.ucl", 0)
  }
  "test-const-import-4.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-const-import-4.ucl", 0)
  }
  "test-func-import-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-func-import-1.ucl", 0)
  }
  "test-func-import-2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-func-import-2.ucl", 0)
  }
  "test-func-import-3.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-func-import-3.ucl", 0)
  }
  "test-func-import-4.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-func-import-4.ucl", 0)
  }
  "test-def-import-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-def-import-0.ucl", 0)
  }
  "test-def-import-4.ucl" should "verify 2 assertions, fail 1." in {
    VerifierSpec.expectedFails("./test/test-def-import-4.ucl", 1)
  }
  "test-renaming-defines.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-renaming-defines.ucl", 0)
  }
  "test-procedure-postcondition-1.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-procedure-postcondition-1.ucl", 1)
  }
  "test-meminout.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-meminout.ucl", 0)
  }
  "test-axiom-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-axiom-1.ucl", 0)
  }
  "test-axiom-2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-axiom-2.ucl", 0)
  }
  "test-nested-instance-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-nested-instance-1.ucl", 0)
  }
  "test-instance-procedure-call-0.ucl" should "verify all but one assertion." in {
    VerifierSpec.expectedFails("./test/test-instance-procedure-call-0.ucl", 1)
  }
  "test-instance-procedure-call-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-instance-procedure-call-1.ucl", 0)
  }
  "test-instance-procedure-call-3.ucl" should "verify all but one." in {
    VerifierSpec.expectedFails("./test/test-instance-procedure-call-3.ucl", 1)
  }
  "test-instance-procedure-call-4.ucl" should "verify all but one." in {
    VerifierSpec.expectedFails("./test/test-instance-procedure-call-4.ucl", 1)
  }
  "test-instance-procedure-call-5.ucl" should "verify all but two." in {
    VerifierSpec.expectedFails("./test/test-instance-procedure-call-5.ucl", 2)
  }
  "test-instance-procedure-call-7.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-instance-procedure-call-7.ucl", 0)
  }
  "sp-basic.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/sp-basic.ucl", 0)
  }
  "issue-187b.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/issue-187b.ucl", 0)
  }
  "test-redundant-assign.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-redundant-assign.ucl", 0)
  }
  "test-macro-1.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-macro-1.ucl", 1)
  }
  "test-macro-2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-macro-2.ucl", 0)
  }
  "test-macro-3.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-macro-3.ucl", 0)
  }
  "test-macro-4.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-macro-4.ucl", 1)
  }
  "test-bmc-4.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-bmc-4.ucl", 1)
  }
}
class LTLVerifSpec extends AnyFlatSpec {
  "test-history-1.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-history-1.ucl", 0)
  }
  "test-history-2.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-history-2.ucl", 1)
  }
  // "test-ltl-0-safe.ucl" should "verify all assertions." in {
  //   VerifierSpec.expectedFails("./test/test-ltl-0-safe.ucl", 0)
  // }
  "test-ltl-0-unsafe.ucl" should " fail to verify 2 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-0-unsafe.ucl", 2)
  }
  // "test-ltl-1-safe.ucl" should "verify all assertions." in {
  //   VerifierSpec.expectedFails("./test/test-ltl-1-safe.ucl", 0)
  // }
  // "test-ltl-1-unsafe.ucl" should "fail to verify 10 assertions." in {
  //   VerifierSpec.expectedFails("./test/test-ltl-1-unsafe.ucl", 10)
  // }
  "test-ltl-2-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-2-holds.ucl", 0)
  }
  "test-ltl-2-fails.ucl" should "fail to verify 4 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-2-fails.ucl", 4)
  }
  "test-ltl-3-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-3-holds.ucl", 0)
  }
  "test-ltl-3-fails.ucl" should "fail to verify 2 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-3-fails.ucl", 2)
  }
  "test-ltl-4-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-4-holds.ucl", 0)
  }
  "test-ltl-4-fails.ucl" should "fail to verify 1 assertion." in {
    VerifierSpec.expectedFails("./test/test-ltl-4-fails.ucl", 1)
  }
  "test-ltl-5-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-5-holds.ucl", 0)
  }
  "test-ltl-5-fails.ucl" should "fail to verify 2 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-5-fails.ucl", 2)
  }
  // "test-ltl-6-fails.ucl" should "fail to verify 4 assertions." in {
  //   VerifierSpec.expectedFails("./test/test-ltl-6-fails.ucl", 4)
  // }
  "test-ltl-7-holds.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-7-holds.ucl", 0)
  }
  "test-ltl-7a-fails.ucl" should "fail to verify 6 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-7a-fails.ucl", 6)
  }
  "test-ltl-7b-fails.ucl" should "fail to verify 5 assertions." in {
    VerifierSpec.expectedFails("./test/test-ltl-7b-fails.ucl", 5)
  }
  // "queue-ltl.ucl" should "verify all assertions." in {
  //   VerifierSpec.expectedFails("./test/queue-ltl.ucl", 0)
  // }
  // "ltl-eventually-1.ucl" should "fail to verify 3 assertions." in {
  //   VerifierSpec.expectedFails("./test/ltl-eventually-1.ucl", 3)
  // }
  "ltl-toy-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/ltl-toy-0.ucl", 0)
  }
  "ltl-toy-1.ucl" should "fail to verify 11 assertions." in {
    VerifierSpec.expectedFails("./test/ltl-toy-1.ucl", 11)
  }
}
class HyperPropertySpec extends AnyFlatSpec {
  "test-hyperproperty-0.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-hyperproperty-0.ucl", 0)
  }
  "test-hyperproperty-4.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-hyperproperty-4.ucl", 0)
  }
  "test-hyperproperty-6.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-hyperproperty-6.ucl", 0)
  }
  "test-hyperproperty-7.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFails("./test/test-hyperproperty-7.ucl", 0)
  }
}

object PrintCexSpec {
  def checkPrintCex(filename: String, n : Int) {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val modules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"), true)
    val mainModule = UclidMain.instantiate(UclidMain.Config(), modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    val config = UclidMain.Config() 
    val results = UclidMain.execute(mainModule.get, config)
    val outputString = UclidMain.stringOutput.toString()
    val lines1 = outputString.split('\n')
    val check = "FAILED -> v [Step #%d]".format(n-1)
    assert (lines1.exists(l => l.contains(check)))
    val lines2 = lines1.filter(l => !l.contains("===="))
    val tail2 = lines2.takeRight(2*n)
    assert(lines2.size >= 2*n)
    (tail2 zip (1 to 2*n)).foreach {
      p => {
        val s = p._1
        val i = (p._2 - 1)/ 2
        if (p._2 % 2 == 1) {
          val sP = "Step #%d".format(i)
          assert (s == sP)
        } else {
          val sP = "  n : %d".format(i)
          assert (s == sP)
        }
      }
    }
  }
  def checkJSONCex (filename : String, n : Int, cex_lens : List[Int], cexfile : String = "") {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val modules = UclidMain.compile(
      UclidMain.Config(files=List(new File(filename))),
      lang.Identifier("main"), true
    )
    val mainModule = UclidMain.instantiate(UclidMain.Config(), modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    val config = UclidMain.Config(smtSolver=List("z3", "-in"), jsonCEXfile=cexfile)
    val results = UclidMain.execute(mainModule.get, config)
    val outputString = UclidMain.stringOutput.toString()
    val lines1 = outputString.split('\n')
    val check = "FAILED -> v [Step #%d]".format(n-1)
    assert (lines1.exists(l => l.contains(check)))
    val lines2 = lines1.filter(l => !l.contains("===="))
    cex_lens.foreach {
      len =>
        val checklen = "Generated CEX trace of length %d".format(len)
        assert (lines2.exists(l => l.contains(checklen)))
    }
    val checkfilemsg = cexfile.isEmpty match {
      case true  => "Wrote CEX traces to file: cex.json"
      case false => s"Wrote CEX traces to file: ${cexfile}.json"
    }
    assert (lines2.exists(l => l.contains(checkfilemsg)))
    // Cleanup generated file
    val actual_cexfile = if (cexfile.isEmpty()) "cex.json" else s"${cexfile}.json"
    new File(actual_cexfile).delete()
  }
  def checkSExprToUclidLang (filename : String) : String = {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    UclidMain.clearJSONString()
    val modules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"), true)
    val mainModule = UclidMain.instantiate(UclidMain.Config(), modules, l.Identifier("main"))
    assert (mainModule.isDefined)
    val config = UclidMain.Config(smtSolver=List("z3", "-in"))
    val results = UclidMain.execute(mainModule.get, config)
    UclidMain.jsonString.toString()
  }
}
class PrintCexSpec extends AnyFlatSpec {
  "test-bmc-0.ucl" should "print a one-step CEX" in {
    PrintCexSpec.checkPrintCex("test/test-bmc-0.ucl", 1)
  }
  "test-bmc-1.ucl" should "print a 2-step CEX" in {
    PrintCexSpec.checkPrintCex("test/test-bmc-1.ucl", 2)
  }
  "test-bmc-3.ucl" should "print a 4-step CEX" in {
    PrintCexSpec.checkPrintCex("test/test-bmc-3.ucl", 4)
  }
  "test-bmc-5.ucl" should "print a 6-step CEX" in {
    PrintCexSpec.checkPrintCex("test/test-bmc-5.ucl", 6)
  }
  "test-k-induction-5.ucl" should "print a 4-step CEX" in {
    VerifierSpec.expectedFails("./test/test-k-induction-5.ucl", 1)
  }
  "test-cex-json-bmc.ucl" should "generate a 3 JSON CEX traces" in {
    PrintCexSpec.checkJSONCex("test/test-cex-json-bmc.ucl", 4, List(4, 5, 6), "cex")
  }
  "test-cex-json-arrays-1.ucl" should "generate a JSON CEX trace" in {
    PrintCexSpec.checkJSONCex("test/test-cex-json-arrays-1.ucl", 6, List(2, 3, 4, 5, 6), "tweedledee")
  }
  "test-cex-json-arrays-2.ucl" should "generate a JSON CEX trace" in {
    PrintCexSpec.checkJSONCex("test/test-cex-json-arrays-2.ucl", 4, List(4), "tweedledum")
  }
  "test/test-cex-json-enum.ucl" should "generate a JSON CEX trace" in {
    PrintCexSpec.checkJSONCex("test/test-cex-json-enum.ucl", 6, List(2, 3, 4, 5, 6))
  }
  "test/test-cex-json-mixed.ucl" should "generate a JSON CEX trace" in {
    PrintCexSpec.checkJSONCex("test/test-cex-json-mixed.ucl", 4, List(4))
  }
  "test/test-cex-json-record.ucl" should "generate a JSON CEX trace" in {
    PrintCexSpec.checkJSONCex("test/test-cex-json-record.ucl", 3, List(1, 2))
  }
  "test-sexpr-uclid-lang-records-1.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-records-1.ucl"))
    val str0 = ((json \ "property__trivial__0" \ "trace")(0) \ "cache1")(0)
    str0 match {
      case JString(s) => assert(s.contains("update-field _field__rec_valid"))
      case _ => assert(false)
    }
    val str1 = ((json \ "property__trivial__1" \ "trace")(1) \ "cache1")(0)
    str1 match {
      case JString(s) => assert(s.equals("const-record [_rec_valid := false, _rec_value := 0]"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-records-2.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-records-2.ucl"))
    val str0 = ((json \ "property__trivial__1" \ "trace")(0) \ "cache1")(0)
    str0 match {
      case JString(s) => assert(s.contains("update-field _field__rec_value")) 
      case _ => assert(false)
    }
    val str1 = ((json \ "property__trivial__1" \ "trace")(1) \ "cache1")(0)
    str1 match {
      case JString(s) => assert(s.equals("const-record [_rec_valid := false, _rec_value := const(0bv32, [bv4]bv32)]"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-arrays-1.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-arrays-1.ucl"))
    val str0 = ((json \ "property__trivial__1" \ "trace")(1) \ "database")(0)
    str0 match {
      case JString(s) => assert(s.equals("(const(3, [integer]integer))[2 -> 4]"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-enums-1.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-enums-1.ucl"))
    val str0 = ((json \ "property__trivial__0" \ "trace")(2) \ "color")(0)
    str0 match {
      case JString(s) => assert(s.equals("YELLOW"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-mixed-1.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-mixed-1.ucl"))
    val str0 = ((json \ "property__trivial__1" \ "trace")(1) \ "database")(0)
    str0 match {
      case JString(s) => assert(s.equals("(const(const-record [_rec_uid := 2, _rec_color := false], [integer]utype_t))[2 -> const-record [_rec_uid := 3, _rec_color := false]]"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-mixed-2.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-mixed-2.ucl"))
    val str0 = ((json \ "property__trivial__1" \ "trace")(1) \ "database")(0)
    str0 match {
      case JString(s) => assert(s.equals("(const(BLUE, [integer]color_t))[2 -> RED]"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-mixed-3.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-mixed-3.ucl"))
    val str0 = ((json \ "property__trivial__1" \ "trace")(1) \ "database")(0)
    str0 match {
      case JString(s) => assert(s.equals("(const(const-record [_rec_uid := 2, _rec_color := RED], [integer]utype_t))[2 -> const-record [_rec_uid := 3, _rec_color := RED]]"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-uninterp-type.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-uninterp-type.ucl"))
    val str0 = ((json \ "property__trivial__1" \ "trace")(1) \ "database")(0)
    str0 match {
      case JString(s) => assert(s.equals("(const(utype_t!val!0, [integer]utype_t))[2 -> utype_t!val!1]"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-uninterp-type-2.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-uninterp-type-2.ucl"))
    val str0 = ((json \ "property__a_equal_b__0" \ "trace")(0) \ "a")(0)
    str0 match {
      case JString(s) => assert(s.equals("ValueSpace!val!0"))
      case _ => assert(false)
    }
    val str1 = ((json \ "property__a_equal_b__0" \ "trace")(0) \ "b")(0)
    str1 match {
      case JString(s) => assert(s.equals("ValueSpace!val!1"))
      case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-uninterp-type-3.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-uninterp-type-3.ucl"))
    val str0 = ((json \ "property__trivial__0" \ "trace")(0) \ "database_1")(0)
    str0 match {
      case JString(s) => assert(s.contains("const(UndefineType!val!"))
      case _ => assert(false)
    }
     val str1 = ((json \ "property__trivial__1" \ "trace")(1) \ "database_1")(0)
     str1 match {
       case JString(s) => assert(s.contains("const(UndefineType!val!"))
       case _ => assert(false)
    }
  }
  "test-sexpr-uclid-lang-uninterp-type-4.ucl" should "generate UclidLang JSON cex" in {
    val json = parse(PrintCexSpec.checkSExprToUclidLang("./test/test-sexpr-uclid-lang-uninterp-type-4.ucl"))
    val str0 = ((json \ "property__graph__0" \ "trace")(0) \ "map")(0)
    str0 match {
      case JString(s) => assert(s.contains("(let (("))
      case _ => assert(false)
    }
  }  
  "test-record-naming-1.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-1.ucl", 0)
  }
  "test-record-naming-2.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-2.ucl", 0)
  }
  "test-record-naming-3.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-3.ucl", 0)
  } 
  "test-record-naming-4.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-4.ucl", 0)
  }
  "test-record-naming-5.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-5.ucl", 0)
  }
  "test-record-naming-6.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-6.ucl", 0)
  }
  "test-record-naming-7.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-7.ucl", 0)
  }
  "test-record-naming-8.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-8.ucl", 0)
  }
  "test-record-naming-9.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-9.ucl", 0)
  }
  "test-record-naming-10.ucl" should "fail to verify assertion." in {
    VerifierSpec.expectedFails("./test/test-record-naming-10.ucl", 6)
  }
  "test-record-naming-11.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-naming-11.ucl"), lang.Identifier("main"))
      assert (false);
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
    }
  }
  "test-record-naming-12.ucl" should "fail to verify assertion." in {
    VerifierSpec.expectedFails("./test/test-record-naming-12.ucl", 1)
  }
  "test-record-naming-13.ucl" should "fail to verify assertion." in {
    VerifierSpec.expectedFails("./test/test-record-naming-13.ucl", 5)
  }
  "test-record-naming-14.ucl" should "fail to verify assertion." in {
    VerifierSpec.expectedFails("./test/test-record-naming-14.ucl", 2)
  }
  "test-record-naming-15.ucl" should "verify successfully." in {
    VerifierSpec.expectedFails("./test/test-record-naming-15.ucl", 0)
  }
  "test-record-naming-16.ucl" should "fail to verify assertion." in {
    VerifierSpec.expectedFails("./test/test-record-naming-16.ucl", 2)
  }
}
class ModuleConcatSpec extends AnyFlatSpec {
  "test-concat-modules-w-init-2-fab.ucl" should "verify all assertions." in {
    VerifierSpec.expectedFailsMultipleFiles(List(
      "test/test-concat-modules-w-init-2-fa.ucl", "test/test-concat-modules-w-init-2-fb.ucl"
    ), 0)
  }
  "test-concat-modules-w-init-2-fba.ucl" should "fail to verify assertion." in {
    VerifierSpec.expectedFailsMultipleFiles(List(
      "test/test-concat-modules-w-init-2-fb.ucl", "test/test-concat-modules-w-init-2-fa.ucl"
    ), 2)
  }
}

