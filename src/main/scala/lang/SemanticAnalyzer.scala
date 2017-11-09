/*
 * UCLID5
 * 
 * Authors: Rohit Sinha, Pramod Subramanyan
 * 
 * Walks through the module looking for semantic errors.
 */
package uclid;
package lang;

case class ModuleError(msg : String, position : ASTPosition)

class SemanticAnalyzerPass extends ReadOnlyPass[List[ModuleError]] {
  def checkIdRedeclaration(idSeq : Seq[(Identifier, ASTPosition)], in : List[ModuleError]) : List[ModuleError] = {
    val init = (Map.empty[Identifier, ASTPosition], in)
    (idSeq.foldLeft(init){
      (acc, id) => {
        acc._1.get(id._1) match {
          case Some(pos) =>
            val msg = "Redeclaration of identifier '" + id._1.name + "'. Previous declaration at " + pos.toString
            (acc._1, ModuleError(msg, id._2) :: acc._2)
          case None =>
            ((acc._1 + (id._1 -> id._2)), acc._2)
        }
      }
    })._2
  }
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      // val moduleIds = module.decls.filter((d) => d.declNames.isDefined).map((d) => (d.declName.get, d.position))
      val moduleIds = module.decls.flatMap((d) => d.declNames.map((n) => (n, d.position)))
      checkIdRedeclaration(moduleIds, in)
    } else { in }
  }
  override def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      val inParams = proc.sig.inParams.map((arg) => (arg._1, arg._1.position))
      val outParams = proc.sig.outParams.map((arg) => (arg._1, arg._1.position))
      val localVars = proc.decls.map((v) => (v.id, v.position))
      checkIdRedeclaration(inParams ++ outParams ++ localVars, in)
    } else { in }
  }
  override def applyOnFunction(d : TraversalDirection.T, func : FunctionDecl, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      val params = func.sig.args.map((arg) => (arg._1, arg._1.position))
      checkIdRedeclaration(params, in)
    } else { in }
  }
  override def applyOnAssign(d : TraversalDirection.T, stmt : AssignStmt, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      if (stmt.lhss.size != stmt.rhss.size) {
        val msg = "Number of left and right hand sides on assignement statement don't match."
        ModuleError(msg, stmt.position) :: in
      } else { in }
    } else { in }
  }
  override def applyOnRecordType(d : TraversalDirection.T, recordT : RecordType, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      val fieldNames = recordT.members.map((f) => (f._1, f._1.position))
      checkIdRedeclaration(fieldNames, in)
    } else {
      in
    }
  }
}

class SemanticAnalyzer extends ASTAnalyzer("SemanticAnalyzer", new SemanticAnalyzerPass())  {
  override def visit(module : Module) : Option[Module] = {
    val out = visitModule(module, List.empty[ModuleError])
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position))
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}

