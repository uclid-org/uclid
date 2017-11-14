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
  "test/test-type1.ucl4" should "not parse successfully." in {
    try {
      val filename = "test/test-type1.ucl4"
      val fileModules = UclidMain.compile(List(filename))
      assert (fileModules.size == 2)
    }
    catch {
      case p : Utils.ParserErrorList => 
        assert (p.errors.size == 1)
        assert (p.errors(0)._1.contains("Redeclaration of identifier 'test'."))
    }
  }
  "test/test-typechecker-0.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-0.ucl4"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 6)
    }
  }
  "test/test-typechecker-1.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-1.ucl4"))
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
  "test/test-module-errors.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-module-errors.ucl4"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 5)
    }
  }
  "test/test-typechecker-3.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-3.ucl4"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
    }
  }
  "test/test-typechecker-4.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-4.ucl4"))
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
  "test/test-recursion.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-recursion.ucl4"))
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
  "test/test-procedure-types-errors.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-procedure-types-errors.ucl4"))
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
  "test/test-procedure-invocation-errors.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-procedure-invocation-errors.ucl4"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0).getMessage().contains("Type error in function application"))
    }
  } 
}