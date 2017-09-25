package uclid
package test

import org.scalatest.FlatSpec
import uclid.{lang => l}

class ParserSpec extends FlatSpec {
  "test/test1.ucl4" should "parse successfully." in {
      val text = scala.io.Source.fromFile("test/test1.ucl4").mkString
      val fileModules = l.UclidParser.parseModel(text)
      assert (fileModules.size == 1)
  }
  "test/test-type1.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-type1.ucl4"))
      assert (fileModules.size == 2)
    }
    catch {
      case p : Utils.ParserError => 
        assert(p.getMessage() == "Repeated module names: test")
    }
  }
  "test/test-typechecker-1.ucl4" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List("test/test-typechecker-1.ucl4"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserError =>
        val msg : String = p.getMessage()
        assert (msg.contains("Unknown identifier in havoc statement"))
    }
  }

}