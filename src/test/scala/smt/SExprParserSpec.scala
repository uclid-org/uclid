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
 * Authors: Norman Mu, Pramod Subramanyan
 *
 * UCLID Parser/Typechecker tests.
 *
 */

package uclid
package test

import org.scalatest.FlatSpec
import uclid.{lang => l}
import uclid.smt._
import scala.io.Source

object SExprParserSpec {
  //TODO: Might need to change output depending on tests
  def expectPass(filename: String) : Unit = {
    val buffSource = Source.fromFile(filename)
    try {
      val input = buffSource.getLines mkString "\n"
      SExprParser.parseModel(input)
    } finally {
      buffSource.close
    }
  }
}

class SExprParserNoErrorSpec extends FlatSpec {
  "data-ineq-01.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/data-ineq-01.smt2")
  }
  "data-ineq-02.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/data-ineq-02.smt2")
  }
  "dll-entails-dll_rev.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll-entails-dll_rev.smt2")
  }
  "dll_plus-entails-dll.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_plus-entails-dll.smt2")
  }
  "dll_plus-entails-dll_plus_rev.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_plus-entails-dll_plus_rev.smt2")
  }
  "dll_plus-entails-node-dll_plus_rev.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_plus-entails-node-dll_plus_rev.smt2")
  }
   "dll_plus-entails-node-node-dll_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_plus-entails-node-node-dll_plus.smt2")
  }
   "dll_plus_mid-entails-dll_plus_rev.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_plus_mid-entails-dll_plus_rev.smt2")
  }
  "dll_plus_rev-entails-dll_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_plus_rev-entails-dll_plus.smt2")
  }
  "dll_plus_rev-entails-dll_plus_mid.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_plus_rev-entails-dll_plus_mid.smt2")
  }
  "dll_rev-entails-dll.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dll_rev-entails-dll.smt2")
  }
  "dllseg2_plus-entails-dllseg2_plus_rev.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dllseg2_plus-entails-dllseg2_plus_rev.smt2")
  }
  "dllseg2_plus-spaghetti-existential.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dllseg2_plus-spaghetti-existential.smt2")
  }
  "dllseg2_plus-spaghetti.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/dllseg2_plus-spaghetti.smt2")
  }
  "node-dll_plus_rev-dll_plus-entails-dll_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/node-dll_plus_rev-dll_plus-entails-dll_plus.smt2")
  }
  "node-node-dll_plus-entails_dll_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/node-node-dll_plus-entails_dll_plus.smt2")
  }
  "node-tll_plus-tll_plus-entails-tll_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/node-tll_plus-tll_plus-entails-tll_plus.smt2")
  }
  "pto-01.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/pto-01.smt2")
  }
  "pto-02.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/pto-02.smt2")
  }
  "pto-03.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/pto-03.smt2")
  }
  "pto-04.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/pto-04.smt2")
  }
  "sep-01.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/sep-01.smt2")
  }
  "sep-02.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/sep-02.smt2")
  }
  "sep-03.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/sep-03.smt2")
  }
  "sep-04.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/sep-04.smt2")
  }
  "tll-ravioli-existential.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/tll-ravioli-existential.smt2")
  }
  "tll-ravioli.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/tll-ravioli.smt2")
  }
  "tll_plus-entails-node-tll_plus-tll_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/tll_plus-entails-node-tll_plus-tll_plus.smt2")
  }
  "tll_plus-entails-tll_plus_rev.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/tll_plus-entails-tll_plus_rev.smt2")
  }
  "tll_plus_rev-entails-tll_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/tll_plus_rev-entails-tll_plus.smt2")
  }
  "tpp_plus-entails-tpp_plus_rev.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/tpp_plus-entails-tpp_plus_rev.smt2")
  }
  "tpp_plus_rev-entails-tpp_plus.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/parse-smtlib-benches/tpp_plus_rev-entails-tpp_plus.smt2")
  }
  "kaluzalong.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/kaluzalong.smt2")
  }
  "pisa-000.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-000.smt2")
  }
  "pisa-001.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-001.smt2")
  }
  "pisa-002.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-002.smt2")
  }
  "pisa-003.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-003.smt2")
  }
  "pisa-004.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-004.smt2")
  }
  "pisa-005.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-005.smt2")
  }
  "pisa-006.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-006.smt2")
  }
  "pisa-007.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-007.smt2")
  }
  "pisa-008.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-008.smt2")
  }
  "pisa-009.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-009.smt2")
  }
  "pisa-010.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-010.smt2")
  }
  "pisa-011.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/pisa-011.smt2")
  }
  "test1.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/test1.smt2")
  }
  "test2.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/test2.smt2")
  }
  "test3.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/test3.smt2")
  }
  "test4.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/test4.smt2")
  }
  "test5.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/test5.smt2")
  }
  "test6.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/antlr-examples/test6.smt2")
  }
  "2447.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/z3-regress/2447.smt2")
  }
  "crash.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/z3-regress/crash.smt2")
  }
  "o2.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/z3-regress/o2.smt2")
  }
  "t170.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/z3-regress/t170.smt2")
  }
  "t178.smt2" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/z3-regress/t178.smt2")
  }
}
