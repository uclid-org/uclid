package uclid
package lang

class CaseEliminatorPass extends RewritePass {
  def casesToIfs(cases : List[(Expr, List[Statement])]) : List[Statement] = {
    cases match {
      case Nil => 
        List.empty[Statement]
      case head :: rest =>
        List(IfElseStmt(head._1, head._2, casesToIfs(rest)))
    }
  }

  override def rewriteCase(st : CaseStmt, ctx : ScopeMap) : List[Statement] = {
    casesToIfs(st.body)
  }
}

class CaseEliminator extends ASTRewriter(
    "CaseEliminator", new CaseEliminatorPass())
