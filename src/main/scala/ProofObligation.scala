package uclid

import uclid.lang._

case class AssertInfo(name : String, iter : Int, expr : smt.Expr, pos : ASTPosition) {
  override def toString = {
    "[Step #" + iter.toString + "] " + name + " @ " + pos.toString
  }
}

case class CheckResult(assert : AssertInfo, result : smt.SolverResult)

class ProofObligation(val parent: Option[ProofObligation], val assumptions: List[smt.Expr], val assertions: List[AssertInfo]) {
  def allAssumptions : List[smt.Expr] = {
    assumptions ++ (parent match {
      case Some(p) => p.allAssumptions
      case None    => List.empty
    })
  }
  def addAssumption(assumption: smt.Expr) = {
    if (assertions.size > 0) {
      (true, new ProofObligation(Some(this), List(assumption), List.empty))
    } else {
      (false, new ProofObligation(parent, assumption :: assumptions, assertions))
    }
  }
  def addAssertion(assertion: AssertInfo) = {
    new ProofObligation(parent, assumptions, assertion :: assertions)
  }
  override def toString : String = {
    val assumps = Utils.join(assumptions.map("  " + _.toString), "\n")
    val asserts = Utils.join(assertions.map("  " + _.toString), "\n")
    "** assumptions **" + assumps + "\n\n** assertions **" + asserts
  }
}

object ProofObligation {
  def root : ProofObligation = new ProofObligation(None, List.empty, List.empty)
}
