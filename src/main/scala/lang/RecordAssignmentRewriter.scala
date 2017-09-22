package uclid
package lang

abstract class RecordAssignmentRewriterPass(typechecker: TypeComputePass) extends RewritePass {
  def expandAssignment(lhs: Lhs, rhs: Expr) : List[(Lhs, Expr)]
  
  override def rewriteAssign(st : AssignStmt, ctx : ScopeMap) : List[Statement] = {
    val pairs = (st.lhss zip st.rhss).flatMap((p) => expandAssignment(p._1, p._2))
    val assign = AssignStmt(pairs.map(_._1), pairs.map(_._2))
    return List(assign)
  }
}

/*
class RecordAssignmentRewriter extends ASTRewriter(
    "RecordAssignmentRewriter", new RecordAssignmentRewriterPass())
*/