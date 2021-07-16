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
}

class MacroReplacer extends ASTRewriter(
  "MacroReplacer", new MacroRewriterPass())

class MacroAnnotationCollector extends ReadOnlyPass [MacroAnnotation] {
  type T = MacroAnnotation

  override def applyOnMacro(d : TraversalDirection.T, macroDecl : MacroDecl, in : T, context : Scope) : T = {
    val listOfPositions = macroDecl.body.stmts.foldLeft(List[ASTPosition]()){
      (acc, s)  => acc :+ s.position }
      val newMap = in.macroMap + (macroDecl.id -> listOfPositions)
      MacroAnnotation(newMap)
  }
}

class MacroAnnotator extends ASTAnalyzer(
  "MacroAnnotator", new MacroAnnotationCollector())
{
  override def reset() {
    in = Some(MacroAnnotation(Map[Identifier, List[ASTPosition]]()))
  }

  override def visit(module : Module, context : Scope) : Option[Module] = {
    val macroAnnotationMap = visitModule(module, MacroAnnotation(Map[Identifier, List[ASTPosition]]()), context)
    _out = Some(macroAnnotationMap)
    return Some(Module(module.id, module.decls, module.cmds, module.notes :+ macroAnnotationMap))
  }
}

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
