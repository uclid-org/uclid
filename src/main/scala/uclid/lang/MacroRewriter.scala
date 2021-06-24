package uclid
package lang

class MacroRewriterPass extends RewritePass {
  override def rewriteMacroCall(st: MacroCallStmt, ctx: Scope): Option[Statement] = {
    val mId = st.id
    ctx.map.get(mId) match {
      case Some(Scope.Macro(mId, typ, macroDecl)) => Some(macroDecl.body)
      case _ => Some(st)
    }
  }
}

class MacroRewriter extends ASTRewriter(
  "MacroRewriter", new MacroRewriterPass())
