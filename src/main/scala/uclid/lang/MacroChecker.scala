package uclid
package lang

class MacroCheckerPass extends ReadOnlyPass[Set[ModuleError]] {
  type T = Set[ModuleError]

  var inNextBlock = false
  var inMacroDecl = false

  override def applyOnMacro(d : TraversalDirection.T, macroDecl : MacroDecl, in : T, context : Scope) : T = {
    inMacroDecl = d == TraversalDirection.Down
    in
  }

  override def applyOnNext(d : TraversalDirection.T, next : NextDecl, in : T, context : Scope): T = {
    inNextBlock = d == TraversalDirection.Down
    in
  }

  override def applyOnMacroCall(d : TraversalDirection.T, st : MacroCallStmt, in : T, context : Scope): T = {
    if (d == TraversalDirection.Down) {
      if (inNextBlock) {
        val error = ModuleError("Macro calls are not allowed in the next block", st.position)
        in + error
      } else if (inMacroDecl) {
        val error = ModuleError("Macro calls are not allowed in macro declarations", st.position)
        in + error
      } else {
        in
      }
    } else {
      in
    }
  }
}

class MacroChecker extends ASTAnalyzer("MacroChecker", new MacroCheckerPass()) {
    override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, Set.empty[ModuleError], context)
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}


