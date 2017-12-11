package uclid

import uclid.lang._

import scala.collection.mutable.ListBuffer

case class AssertInfo(name : String, iter : Int, expr : smt.Expr, pos : ASTPosition) {
  override def toString = {
    "[Step #" + iter.toString + "] " + name + " @ " + pos.toString
  }
}

case class CheckResult(assert : AssertInfo, result : smt.SolverResult)

class AssertionTree {
  class TreeNode(p : Option[TreeNode], assumps : List[smt.Expr]) {
    var parent : Option[TreeNode] = p
    var children : ListBuffer[TreeNode] = ListBuffer.empty
    var assumptions: ListBuffer[smt.Expr] = assumps.to[ListBuffer]
    var assertions: ListBuffer[AssertInfo] = ListBuffer.empty
    var results : List[CheckResult] = List.empty

    // these two functions add assumptions.
    def +=(e : smt.Expr) { assumptions += e }
    // and these two add assertions
    def +=(assert: AssertInfo) { assertions += assert }
  }

  val root : TreeNode = new TreeNode(None, List.empty)
  val initialRoot : TreeNode = root
  var currentNode : TreeNode = root

  def addAssumption(assump: smt.Expr) {
    if (currentNode.assertions.size > 0) {
      val childNode = new TreeNode(Some(currentNode), List(assump))
      currentNode.children += childNode
      currentNode = childNode
    } else {
      currentNode += assump
    }
  }

  def addAssert(assert: AssertInfo) {
    currentNode += assert
  }

  def resetToInitial() {
    currentNode = initialRoot
  }

  def _verify(node : TreeNode, solver : smt.SolverInterface) : List[CheckResult] = {
    solver.addAssumptions(node.assumptions.toList)
    node.results = (node.assertions.map {
      e => {
        val sat = solver.check(smt.OperatorApplication(smt.NegationOp, List(e.expr)))
        val result = sat.result match {
          case Some(true)  => smt.SolverResult(Some(false), sat.model)
          case Some(false) => smt.SolverResult(Some(true), sat.model)
          case None        => smt.SolverResult(None, None)
        }
        CheckResult(e, result)
      }
    }).toList
    // now recurse into children
    val childResults = node.children.flatMap(c => _verify(c, solver))
    solver.popAssumptions()
    node.results ++ childResults
  }
  def verify(solver : smt.SolverInterface) : List[CheckResult] = _verify(root, solver)
}