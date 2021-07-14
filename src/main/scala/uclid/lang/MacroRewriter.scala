package uclid
package lang


class MacroReplacerPass extends RewritePass {


  override def rewriteBlock(st: BlockStmt, ctx: Scope): Option[Statement] = {
    // if all statements in block have macro annotation, replace all statements with macro 
    // (add macro annotation to new block)
    // throw runtime error if macro doesn't exist

    // if some statements but not all have macro annotations, throw error? we replace full blocks only?

    // if no statements have macro annotations, return original block
    Some(st)
  }

  override def rewriteStatement(st: MacroCallStmt, ctx: Scope): Option[Statement] = {
  }


// should not be any macro call statements?
  override def rewriteMacroCall(st: MacroCallStmt, ctx: Scope): Option[Statement] = {
    val mId = st.id
    ctx.map.get(mId) match {
      case Some(Scope.Macro(mId, typ, macroDecl)) => 
      {
        var body  = macroDecl.body
        body.macroAnnotation = Some(MacroAnnotation(mId,macroDecl.body.stmts.size))
        Some(macroDecl.body)
      }
      case _ => Some(st)
    }
  }
}

class MacroReplacer extends ASTRewriter(
  "MacroReplacer", new MacroRewriterPass())


class MacroRewriterPass extends RewritePass {

  override def rewriteMacroCall(st: MacroCallStmt, ctx: Scope): Option[Statement] = {
    val mId = st.id
    ctx.map.get(mId) match {
      case Some(Scope.Macro(mId, typ, macroDecl)) => 
      {
        var body  = macroDecl.body
        body.macroAnnotation = Some(MacroAnnotation(mId,macroDecl.body.stmts.size))
        Some(macroDecl.body)
      }
      case _ => Some(st)
    }
  }
}

class MacroRewriter extends ASTRewriter(
  "MacroRewriter", new MacroRewriterPass())
