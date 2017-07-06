package uclid
package lang

import scala.collection.mutable.Map
import scala.collection.immutable.Set

class FindLeafProceduresPass extends ReadOnlyPass[Set[IdGenerator.Id]] {
  var procedureMap = Map.empty[IdGenerator.Id, UclProcedureDecl]  
  override def reset() { 
    procedureMap.clear()
  }
  override def applyOnProcedure(d : TraversalDirection.T, proc : UclProcedureDecl, in : Set[IdGenerator.Id], ctx : ScopeMap) : Set[IdGenerator.Id] = {
    if (d == TraversalDirection.Down) return in
    
    val hasProcedureCalls = proc.body.exists((st) => {
      st match {
        case UclProcedureCallStmt(_,_,_) => true
        case _ => false
      }
    })
    if (!hasProcedureCalls) {
      procedureMap.put(proc.astNodeId, proc)
      return in + proc.astNodeId
    } else {
      return in
    }
  }
  def procedure(i : IdGenerator.Id) : UclProcedureDecl = procedureMap.get(i).get
}
class FindLeafProcedures extends ASTAnalyzer("FindLeafProcedures", new FindLeafProceduresPass) {
  override def pass : FindLeafProceduresPass = super.pass.asInstanceOf[FindLeafProceduresPass]
  in = Some(Set.empty)
  override def reset() {
    in = Some(Set.empty)
  }
  
  // Mainly for debugging.
  def printLeafProcedures() {
    out match {
      case Some(list) => println("Found some leaf procedures.")
                         list.foreach{ (astNodeId) => println("--> " + pass.procedure(astNodeId).id.toString) }
      case None       => println("No leaf procedures. (ERROR!)")
    }
  }
}
