package uclid
package lang

import scala.collection.mutable.Map
import scala.collection.immutable.Set

class FindLeafProceduresPass extends ReadOnlyPass[Set[IdGenerator.Id]] {
  var procedureMap = Map.empty[IdGenerator.Id, ProcedureDecl]  
  override def reset() { 
    procedureMap.clear()
  }
  override def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : Set[IdGenerator.Id], ctx : ScopeMap) : Set[IdGenerator.Id] = {
    if (d == TraversalDirection.Down) return in
    
    val hasProcedureCalls = proc.body.exists((st) => {
      st match {
        case ProcedureCallStmt(_,_,_) => true
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
  def procedure(i : IdGenerator.Id) : ProcedureDecl = procedureMap.get(i).get
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

class TupleFlattenerPass extends RewritePass {
  def rewriteTuple(id : Identifier, typ : Type) : List[(Identifier, Type)] = {
    typ match {
      case RecordType(fields) => fields.map{ (f) => (Identifier(id + "_$field$_" + f._1.value), f._2) }
      case TupleType(fields) => fields.zipWithIndex.map{ case (f, i) => (Identifier(id.value + "_$tuple$_" + i.toString), f) }
      case _ => List((id, typ))
    }
  }
  
  override def rewriteModule(module: Module, ctx : ScopeMap) : Option[Module] = {
    val newDecls : List[Decl] = module.decls.flatMap{ (decl) =>
      decl match {
        case StateVarDecl(id, typ) => rewriteTuple(id, typ).map((t) => StateVarDecl(t._1, t._2))
        case InputVarDecl(id, typ) => rewriteTuple(id, typ).map((t) => InputVarDecl(t._1, t._2))
        case OutputVarDecl(id, typ) => rewriteTuple(id, typ).map((t) => OutputVarDecl(t._1, t._2))
        case ConstantDecl(id, typ) => rewriteTuple(id, typ).map((t) => ConstantDecl(t._1, t._2))
        case FunctionDecl(id, sig) => throw new Utils.UnimplementedException("TODO")
        case _ => List(decl)
      }
    }
    return Some(Module(module.id, newDecls, module.cmds))
  }
}
class TupleFlattener extends ASTRewriter("TupleExpander", new TupleFlattenerPass())
