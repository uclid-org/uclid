package uclid.smt

import org.scalatest.flatspec.AnyFlatSpec


class SymbolSpec extends AnyFlatSpec {
  val t = BoolType

  it should "not escape simple symbols" in {
    assert(Symbol("a", t).toString == "a")
    assert(Symbol("++", t).toString == "++")
    assert(Symbol("*-", t).toString == "*-")
    assert(Symbol("=a=", t).toString == "=a=")
    assert(Symbol("...", t).toString == "...")
    assert(Symbol("<<<<", t).toString == "<<<<")
    assert(Symbol("@1", t).toString == "@1")
    assert(Symbol("a/b/c", t).toString == "a/b/c")
    assert(Symbol("&~&", t).toString == "&~&")
    assert(Symbol("^_^", t).toString == "^_^")
    assert(Symbol("!?", t).toString == "!?")
  }

  it should "reject ids that cannot be represented" in {
    assertThrows[AssertionError] { Symbol("|", t) }
    assertThrows[AssertionError] { Symbol("test|", t) }
    assertThrows[AssertionError] { Symbol("|test|", t) }
    assertThrows[AssertionError] { Symbol("\\", t) }
    assertThrows[AssertionError] { Symbol("test\\", t) }
  }

  it should "escape symbols when they are not simple" in {
    assert(Symbol("1", t).toString == "|1|")
    assert(Symbol("1a", t).toString == "|1a|")
    assert(Symbol("", t).toString == "||")
    assert(Symbol(" ", t).toString == "| |")
    assert(Symbol("(select mem test)", t).toString == "|(select mem test)|")
    assert(Symbol("mem[test]", t).toString == "|mem[test]|")
    // the SMTLib spec says "printable characters", not sure if this includes UNICODE
    assert(Symbol("\uD83D\uDC4D", t).toString == "|\uD83D\uDC4D|")
  }
}
