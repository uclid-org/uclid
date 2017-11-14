package uclid
package lang

class ModuleCleanerPass extends RewritePass {
  override def rewriteTypeDecl(typDec : TypeDecl, ctx : ScopeMap) : Option[TypeDecl] = {
    None
  }
}

class ModuleCleaner extends ASTRewriter(
    "ModuleCleaner", new ModuleCleanerPass())

class ModuleEliminatorPass(moduleName : Identifier) extends RewritePass {
  override def rewriteModule(module : Module, ctx : ScopeMap) : Option[Module] = {
    if (module.id == moduleName) {
      Some(module)
    } else {
      None
    }
  }
}

class ModuleEliminator(moduleName : Identifier) extends ASTRewriter(
    "ModuleEliminator", new ModuleEliminatorPass(moduleName))