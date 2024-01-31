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
 * Authors: Pranav Gaddamadugu
 *
 * UCLID Parser/Typechecker tests.
 *
 */

package uclid
package test

import org.scalatest.flatspec.AnyFlatSpec

import scala.io.Source

object SExprParserSpec {
  //TODO: Might need to change output depending on tests
  def expectPass(filename: String) : Unit = {
    val buffSource = Source.fromFile(filename)
    try {
      val input = buffSource.getLines mkString "\n"
      smt.SExprParser.parseModel(input)
    } finally {
      buffSource.close
    }
  }
}


class SExprParserNoErrorSpec extends AnyFlatSpec {
  "parser_test1.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test1.txt")
  }
  "parser_test2.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test2.txt")
  }
  "parser_test3.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test3.txt")
  }
  "parser_test4.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test4.txt")
  }
  "parser_test5.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test5.txt")
  }
  "parser_test6.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test6.txt")
  }
  "parser_test7.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test7.txt")
  }
  "parser_test8.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test8.txt")
  }
  "parser_test9.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test9.txt")
  }
  "parser_test10.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test10.txt")
  }
  "parser_test11.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test11.txt")
  }
  "parser_test12.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test12.txt")
  }
  "parser_test13.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test13.txt")
  }
  "parser_test14.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test14.txt")
  }
  "parser_test15.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test15.txt")
  }
  "parser_test16.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test16.txt")
  }
  "parser_test17.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test17.txt")
  }
  "parser_test18.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test18.txt")
  }
  "parser_test19.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test19.txt")
  }
  "parser_test20.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test20.txt")
  }
  "parser_test21.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test21.txt")
  }
  "parser_test22.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test22.txt")
  }
  "parser_test23.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test23.txt")
  }
  "parser_test24.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test24.txt")
  }
  "parser_test25.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test25.txt")
  }
  "parser_test26.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test26.txt")
  }
  "parser_test27.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test27.txt")
  }
  "parser_test28.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test28.txt")
  }
  "parser_test29.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test29.txt")
  }
  "parser_test30.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test30.txt")
  }
  "parser_test31.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test31.txt")
  }
  "parser_test32.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test32.txt")
  }
  "parser_test33.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test33.txt")
  }
  "parser_test34.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test34.txt")
  }
  "parser_test35.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test35.txt")
  }
  "parser_test36.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test36.txt")
  }
  "parser_test37.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test37.txt")
  }
  "parser_test38.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test38.txt")
  }
  "parser_test39.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test39.txt")
  }
  "parser_test40.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test40.txt")
  }
  "parser_test41.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test41.txt")
  }
  "parser_test42.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test42.txt")
  }
  "parser_test43.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test43.txt")
  }
  "parser_test44.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test44.txt")
  }
  "parser_test45.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test45.txt")
  }
  "parser_test46.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test46.txt")
  }
  "parser_test47.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test47.txt")
  }
  "parser_test48.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test48.txt")
  }
  "parser_test49.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test49.txt")
  }
  "parser_test50.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test50.txt")
  }
  "parser_test51.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test51.txt")
  }
  "parser_test52.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test52.txt")
  }
  "parser_test53.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test53.txt")
  }
  "parser_test54.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test54.txt")
  }
  "parser_test55.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test55.txt")
  }
  "parser_test56.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test56.txt")
  }
  "parser_test57.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test57.txt")
  }
  "parser_test58.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test58.txt")
  }
  "parser_test59.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test59.txt")
  }
  "parser_test60.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test60.txt")
  }
  "parser_test61.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test61.txt")
  }
  "parser_test62.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test62.txt")
  }
  "parser_test63.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test63.txt")
  }
  "parser_test64.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test64.txt")
  }
  "parser_test65.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test65.txt")
  }
  "parser_test66.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test66.txt")
  }
  "parser_test67.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test67.txt")
  }
  "parser_test68.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test68.txt")
  }
  "parser_test69.txt" should "parse successfully." in {
    SExprParserSpec.expectPass("test/parser/command-response/output/parser_test69.txt")
  }
}
