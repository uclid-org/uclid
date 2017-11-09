/*
 * UCLID5
 * 
 * Authors: Pramod Subramanyan.
 * 
 * AddFilenamePass annotates each AST node in a module with a filename.
 */
package uclid
package lang

class AddFilenamePass(var filename : Option[String]) extends RewritePass {
  override def rewriteModule(module : Module, ctx : ScopeMap) : Option[Module] = { 
    module.filename = filename
    return Some(module)
  }
  override def rewriteDecl(decl : Decl, ctx : ScopeMap) : Option[Decl] = { 
    decl.filename = filename
    Some(decl) 
  }
  override def rewriteCommand(cmd : ProofCommand, ctx : ScopeMap) : Option[ProofCommand] = { 
    cmd.filename = filename
    Some(cmd) 
  }
  override def rewriteProcedureSig(sig : ProcedureSig, ctx : ScopeMap) : Option[ProcedureSig] = { 
    sig.filename = filename
    Some(sig) 
  }
  override def rewriteFunctionSig(sig : FunctionSig, ctx : ScopeMap) : Option[FunctionSig] = { 
    sig.filename = filename
    Some(sig) 
  }
  override def rewriteLocalVar(lvar : LocalVarDecl, ctx : ScopeMap) : Option[LocalVarDecl] = { 
    lvar.filename = filename
    Some(lvar) 
  }
  override def rewriteStatement(st : Statement, ctx : ScopeMap) : List[Statement] = { 
    st.filename = filename
    List(st) 
  }
  override def rewriteLHS(lhs : Lhs, ctx : ScopeMap) : Option[Lhs] = { 
    lhs.filename = filename
    Some(lhs) 
  }
  override def rewriteExpr(e : Expr, ctx : ScopeMap) : Option[Expr] = { 
    e.filename = filename
    Some(e) 
  }
  override def rewriteIdentifierBase(id : IdentifierBase, ctx : ScopeMap) : Option[IdentifierBase] = { 
    id.filename = filename
    Some(id)
  }
  override def rewriteIdentifier(id : Identifier, ctx : ScopeMap) : Option[Identifier] = {
    id.filename = filename
    Some(id)
  }
  override def rewriteConstIdentifier(id : ConstIdentifier, ctx : ScopeMap) : Option[ConstIdentifier] = {
    id.filename = filename
    Some(id)
  }
  override def rewriteTuple(rec : Tuple, ctx : ScopeMap) : Option[Tuple] = { 
    rec.filename = filename
    Some(rec) 
  }
  override def rewriteOperator(op : Operator, ctx : ScopeMap) : Option[Operator] = { 
    op.filename = filename
    Some(op) 
  }
}

class AddFilenameRewriter(filename : Option[String]) extends ASTRewriter(
    "AddFilenameRewriter", new AddFilenamePass(filename), false)  {
  
  def setFilename(fn: String) {
    pass.asInstanceOf[AddFilenamePass].filename = Some(fn)
  }
}
