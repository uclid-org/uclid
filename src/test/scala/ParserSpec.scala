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
 * Authors: Norman Mu, Pramod Subramanyan
 *
 * UCLID Parser/Typechecker tests.
 *
 */

package uclid
package test

import org.scalatest.FlatSpec
import uclid.{lang => l}

class ParserSpec extends FlatSpec {
  "test-type1.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-type1.ucl"
      val fileModules = UclidMain.compile(List(filename), lang.Identifier("main"))
      assert (fileModules.size == 2)
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0)._1.contains("Redeclaration of identifier 'test'."))
    }
  }
  "test-typechecker-0.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-0.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 8)
    }
  }
  "test-typechecker-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-1.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        val msg : String = p.errors(0)._1
        assert (msg.contains("Unknown identifier in havoc statement"))
    }
  }
  "test-module-errors.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-module-errors.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 5)
    }
  }
  "test-typechecker-6.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-6.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
    }
  }
  "test-typechecker-3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-3.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
    }
  }
  "test-typechecker-4.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-4.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
        // XXX: continue testing here
    }
  }
  "test-recursion.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-recursion.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        // XXX: continue testing here
    }
  }
  "test-procedure-types-errors.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-procedure-types-errors.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
        assert (p.errors.forall(p => p._1.contains("Parameter r expected")))
    }
  }
  "test-procedure-invocation-errors.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-procedure-invocation-errors.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0).getMessage().contains("Cannot apply foo, which is of type procedure"))
    }
  }
  "test-syntax-errors-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-syntax-errors-1.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 3)
        assert (p.errors.forall(e => e.getMessage().contains("Argument to select operator must be module instance")))
    }
  }
  "test-typechecker-5.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-5.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeError =>
        assert (p.getMessage().contains("Recursively defined synonym type"))
        // XXX: continue testing here
    }
  }
  "test-modules-2.ucl" should "not parse successfully." in {
    try {
     val fileModules = UclidMain.compile(List("test/test-modules-2.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 4)
        // XXX: continue testing here
    }
  }
  "test-procedure-checker-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-procedure-checker-1.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.exists(p => p._1.contains("Assignment to variable not declared modifiable: x")))
        assert (p.errors.exists(p => p._1.contains("Unknown state variable declared as modifiable: z")))
    }
  }
  "test-mutual-recursion-error.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-mutual-recursion-error.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Recursion involving procedures")))
    }
  }
  "test-parsing-history-op-error.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-parsing-history-op-error.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Operator can only be used in a verification expression")))
    }
  }
  "test-typechecker-7.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-7.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p.msg.contains("Arguments to operator '+' must be of the same type")))
    }
  }
  "test-typechecker-8.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-8.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Return type and expression type do not match")))
    }
  }
  "test-define-expand.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List("test/test-define-expand.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-procedure-inline-bv.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List("test/test-procedure-inline-bv.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-define-recursive.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-define-recursive.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
        assert (p.errors.exists(p => p._1.contains("Recursion involving define declarations")))
    }
  }
  "nested_instances.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List("test/nested_instances.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
}
