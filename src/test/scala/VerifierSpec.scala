package uclid
package test

import org.scalatest.FlatSpec
import uclid.{lang => l}

class VerifierSpec extends FlatSpec {
  def nTestsFail(filename: String, nFail : Int) {
    val modules = UclidMain.compile(List(filename))
    assert (modules.size == 1)
    val mainModule = modules.get(l.Identifier("main"))
    assert (mainModule.isDefined)
    val results = UclidMain.execute(mainModule.get)
    assert (results.count((e) => e._2 == Some(false)) == nFail)
    assert (results.count((e) => e._2 == Some(true)) == (results.size - nFail));
  }
  
  "test/test-array-0.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-array-0.ucl4", 0)
  }
  "test/test-bv-assign.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-bv-assign.ucl4", 0)
  }
  "test/test-bv-fib.ucl4" should "verify successfully all but one assertion." in {
    nTestsFail("./test/test-bv-fib.ucl4", 1)
  }
  "test/test-case-mc91.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-case-mc91.ucl4", 0)
  }
  "test/test-forloop-0.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-forloop-0.ucl4", 0)
  }
  "test/test-forloop-1.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-forloop-1.ucl4", 0)
  }
  "test/test-inliner.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-inliner.ucl4", 0)
  }
  "test/test-bv-int.ucl4" should "verify successfully all but one assertion." in {
    nTestsFail("./test/test-int-fib.ucl4", 1)
  }
  "test/test-mc91.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-mc91.ucl4", 0)
  }
  "test/test-record-1.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-record-1.ucl4", 0)
  }
  "test/test-tuple-record-1.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-tuple-record-1.ucl4", 0)
  }
  "test/test-types-0.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-types-0.ucl4", 0)
  }
  "test/test-functions-1.ucl4" should "verify successfully." in {
    nTestsFail("./test/test-functions-1.ucl4", 0)
  }
  "test/test-array-1.ucl4" should "verify four assertions and fail to verify two assertions." in {
    nTestsFail("./test/test-array-1.ucl4", 2)
  }
  "test/test-enum-1.ucl4" should "verify all assertions." in {
    nTestsFail("./test/test-enum-1.ucl4", 0)
  }
}