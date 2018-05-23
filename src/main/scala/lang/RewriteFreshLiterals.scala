package uclid
package lang

class RewriteFreshLiteralsPass extends RewritePass {
  var freshLit : Option[Identifier] = None
  
  override def reset() {
    freshLit = None
  }

  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    val declsP = freshLit match {
      case Some(freshId) =>
        StateVarsDecl(List(freshId), BooleanType()) :: module.decls
      case None =>
        module.decls
    }
    val moduleP = Module(module.id, declsP, module.cmds, module.notes)
    Some(moduleP)
  }
  override def rewriteFreshLit(f : FreshLit, context : Scope) : Option[Expr] = {
    freshLit match {
      case Some(f) => Some(f)
      case None =>
        val newId = new ContextualNameProvider(context, "fresh").apply(Identifier("if_star"), "")
        freshLit = Some(newId)
        Some(newId)
    }
  }
}

class RewriteFreshLiterals extends ASTRewriter("RewriteFreshLiterals", new RewriteFreshLiteralsPass())

class IntroduceFreshHavocsPass extends RewritePass {
  override def rewriteIfElse(st : IfElseStmt, ctx : Scope) : Option[Statement] = {
    st.cond match {
      case f : FreshLit =>
        val havoc = HavocStmt(HavocableFreshLit(f))
        Some(BlockStmt(List(havoc, st)))
      case _ =>
        Some(st)
    }
  }
}
class IntroduceFreshHavocs extends ASTRewriter("IntroduceFreshHavocs", new IntroduceFreshHavocsPass())
