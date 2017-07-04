package uclid
package lang

object FindLeafProcedures {
  type ProcedureList = List[IdGenerator.Id]
  def findLeafProcedures(module : Module) : ProcedureList = {
    val pass = new ReadOnlyPass[ProcedureList] {
      override def applyOnProcedure(d : TraversalDirection.T, proc : UclProcedureDecl, in : ProcedureList, ctx : ScopeMap) : ProcedureList = {
        val hasProcedureCalls = proc.body.exists((st) => {
          st match {
            case UclProcedureCallStmt(_,_,_) => true
            case _ => false
          }
        })
        if (!hasProcedureCalls) {
          proc.astNodeId :: in
        } else {
          in
        }
      }
    }
    val emptyList : ProcedureList = List.empty
    val visitor = (new ASTAnalyzer(pass))
    return visitor.visitModule(module, emptyList)
  }
}
