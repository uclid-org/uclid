package uclid.smt
import org.scalatest.{FlatSpec, Matchers}

class SymbolSpec extends FlatSpec with Matchers {
  val t = BoolType

  it should "not escape simple symbols" in {
    Symbol("a", t).toString should be ("a")
    Symbol("++", t).toString should be ("++")
    Symbol("*-", t).toString should be ("*-")
    Symbol("=a=", t).toString should be ("=a=")
    Symbol("...", t).toString should be ("...")
    Symbol("<<<<", t).toString should be ("<<<<")
    Symbol("@1", t).toString should be ("@1")
    Symbol("a/b/c", t).toString should be ("a/b/c")
    Symbol("&~&", t).toString should be ("&~&")
    Symbol("^_^", t).toString should be ("^_^")
    Symbol("!?", t).toString should be ("!?")
  }

  it should "reject ids that cannot be represented" in {
    assertThrows[AssertionError] { Symbol("|", t) }
    assertThrows[AssertionError] { Symbol("test|", t) }
    assertThrows[AssertionError] { Symbol("|test|", t) }
    assertThrows[AssertionError] { Symbol("\\", t) }
    assertThrows[AssertionError] { Symbol("test\\", t) }
  }

  it should "escape symbols when they are not simple" in {
    Symbol("1", t).toString should be ("|1|")
    Symbol("1a", t).toString should be ("|1a|")
    Symbol("", t).toString should be ("||")
    Symbol(" ", t).toString should be ("| |")
    Symbol("(select mem test)", t).toString should be ("|(select mem test)|")
    Symbol("mem[test]", t).toString should be ("|mem[test]|")
    // the SMTLib spec says "printable characters", not sure if this includes UNICODE
    Symbol("\uD83D\uDC4D", t).toString should be ("|\uD83D\uDC4D|")
  }
}
