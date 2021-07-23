package uclid
package lang

class MacroReplacerPass(macroId : Identifier, newMacroBody : BlockStmt) extends RewritePass {
  var newMacroMap : Option[Map[Identifier, List[ASTPosition]]] = None

  override def rewriteAnnotation(note : Annotation, ctx : Scope) : Option[Annotation] = {
    note match {
      case MacroAnnotation(macroMap) =>
        newMacroMap match {
          case Some(m) => Some(MacroAnnotation(m))
          case None    => Some(note)
        }
      case _ => Some(note)
    }
  }

  def updateNewMacroMap(listOfPositions : List[ASTPosition], ctx : Scope) = {
    newMacroMap = newMacroMap match {
      case Some(m) =>
        val allPositions = listOfPositions ++ m(macroId)
        Some(m + (macroId -> allPositions))
      case None =>
        val oldMacroMap = ctx.module match {
          case Some(module) => module.getAnnotation[MacroAnnotation]().get.macroMap
          case None         => Map[Identifier, List[ASTPosition]]()
        }
        val allPositions = listOfPositions ++ oldMacroMap(macroId)
        Some(oldMacroMap + (macroId -> listOfPositions))
    }
  }

  override def rewriteBlock(st : BlockStmt, ctx : Scope) : Option[Statement] = {
    ctx.module match {
      case Some(module) =>
        var blockStatements = st.stmts
        var macroMap = module.getAnnotation[MacroAnnotation]().get.macroMap
        var macroPositions = macroMap get macroId match {
          case Some(p) => p
          case _ => throw new Utils.RuntimeError("Macro does not exist.")
        }
        var blockPositions = blockStatements.map(s => s.position)
        val allStmtsMacro = blockPositions.forall(pos => {macroPositions contains pos})
        val noStmtsMacro = blockPositions.forall(pos => !(macroPositions contains pos))
        if (allStmtsMacro) {
          // The entire block statement consists of statements originating from the given macro
          val listOfPositions = newMacroBody.stmts.foldLeft(List[ASTPosition]()){
            (acc, s) => acc :+ s.position }
          val newMacroMap = macroMap + (macroId -> listOfPositions)
          updateNewMacroMap(listOfPositions, ctx)
          Some(newMacroBody)
        } else if (noStmtsMacro) {
          // No statements in the block statement originated from the given macro
          Some(st)
        } else {
          // Some statements in the block statement originated from the given macro
          // These statements are expected to be contiguous
          val newBlockStmt = replaceMacroWithinBlock(st, macroPositions, newMacroBody)
          val listOfPositions = newMacroBody.stmts.foldLeft(List[ASTPosition]()){
            (acc, s) => acc :+ s.position }
          updateNewMacroMap(listOfPositions, ctx)
          Some(newBlockStmt)
        }
      case _ => 
        Some(st)
    }
  }

  def replaceMacroWithinBlock(st : BlockStmt, macroPositions : List[ASTPosition], newMacroBody : BlockStmt) = {
    /** Given a block statement replaces the statements originating from the macro with the given
     * positions with the statements from the new macro body
     */
    var (leftStmts, rightStmts) = st.stmts.span(s => !(macroPositions contains s.position))
    while (!rightStmts.isEmpty) {
      leftStmts = leftStmts ++ newMacroBody.stmts
      rightStmts = rightStmts.dropWhile(s => macroPositions contains s.position)
      rightStmts.span(s => !(macroPositions contains s.position)) match {
        case (l, r) =>
          leftStmts = leftStmts ++ l
          rightStmts = r
        case _ =>
      }
    }
    BlockStmt(st.vars, leftStmts)
  }
}

class MacroReplacer(macroId : Identifier, newMacroBody : BlockStmt) extends ASTRewriter(
  "MacroReplacer", new MacroReplacerPass(macroId, newMacroBody))

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
