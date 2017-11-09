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
      case p : Utils.ParserError => 
        assert(p.getMessage() == "Repeated module names: test")
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
        assert (p.errors.size == 2)
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
}