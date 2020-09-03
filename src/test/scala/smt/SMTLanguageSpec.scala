package uclid.smt

import org.scalatest.flatspec.AnyFlatSpec

class SMTLanguageSpec extends AnyFlatSpec {

  type AssertError = uclid.Utils.AssertionError

  "BitVectorLit" should "detect whether the positive value fits into the bitvector" in {
    assertThrows[AssertError] { BitVectorLit(2, 1) }
    assertThrows[AssertError] { BitVectorLit(4, 2) }
    assertThrows[AssertError] { BitVectorLit(128, 7) }
  }

  "BitVectorLit" should "disallow literals of width=0" in {
    // 0 should be represented with one bit (z3 requires bv lits to be at least 1-bit wide)
    assertThrows[AssertError] { BitVectorLit(0, 0) }
  }

  "BitVectorLit" should "detect whether the negative value fits into the bitvector" in {
    // two's complement of -1 is 0b1, thus it should fit in one bit
    BitVectorLit(-1, 1)
    assertThrows[AssertError] { BitVectorLit(-2, 1) } // two's complement of -2 is  0b10
    assertThrows[AssertError] { BitVectorLit(-3, 2) } // two's complement of -3 is 0b101
    BitVectorLit(-3, 3)
    assertThrows[AssertError] { BitVectorLit(-4, 2) } // two's complement of -4 is 0b100
    BitVectorLit(-4, 3)
    assertThrows[AssertError] { BitVectorLit(-5, 2) } // two's complement of -5 is 0b1011
    assertThrows[AssertError] { BitVectorLit(-5, 3) }
    BitVectorLit(-5, 4)
    assertThrows[AssertError] { BitVectorLit(-6, 2) } // two's complement of -6 is 0b1010
    assertThrows[AssertError] { BitVectorLit(-6, 3) }
    BitVectorLit(-6, 4)
    assertThrows[AssertError] { BitVectorLit(-7, 2) } // two's complement of -7 is 0b1001
    assertThrows[AssertError] { BitVectorLit(-7, 3) }
    BitVectorLit(-7, 4)
    assertThrows[AssertError] { BitVectorLit(-8, 2) } // two's complement of -8 is 0b1000
    assertThrows[AssertError] { BitVectorLit(-8, 3) }
    BitVectorLit(-8, 4)
  }

  "BitVectorLit" should "serialize to a positive bv literal" in {
    assert(BitVectorLit(0,1).toString == "(_ bv0 1)")
    assert(BitVectorLit( 1,1).toString == "(_ bv1 1)")
    assert(BitVectorLit( 1,2).toString == "(_ bv1 2)")
    assert(BitVectorLit(-1,1).toString == "(_ bv1 1)")
    assert(BitVectorLit(-1,2).toString == "(_ bv3 2)")

    // three bit values (two's complement)
    assert(BitVectorLit( 3,3).toString == "(_ bv3 3)")
    assert(BitVectorLit( 2,3).toString == "(_ bv2 3)")
    assert(BitVectorLit( 1,3).toString == "(_ bv1 3)")
    assert(BitVectorLit( 0,3).toString == "(_ bv0 3)")
    assert(BitVectorLit(-1,3).toString == "(_ bv7 3)")
    assert(BitVectorLit(-2,3).toString == "(_ bv6 3)")
    assert(BitVectorLit(-3,3).toString == "(_ bv5 3)")
    assert(BitVectorLit(-4,3).toString == "(_ bv4 3)")

    // other positive three bit values
    assert(BitVectorLit( 4,3).toString == "(_ bv4 3)")
    assert(BitVectorLit( 5,3).toString == "(_ bv5 3)")
    assert(BitVectorLit( 6,3).toString == "(_ bv6 3)")
    assert(BitVectorLit( 7,3).toString == "(_ bv7 3)")
  }


}
