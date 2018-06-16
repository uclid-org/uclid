package uclid
package lang

class ModuleCleanerPass extends RewritePass {
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val declsP = module.decls.sortWith((d1, d2) => d1.hashId < d2.hashId)
    Some(Module(module.id, declsP, module.cmds, module.notes))
  }
}

class ModuleCleaner extends ASTRewriter(
    "ModuleCleaner", new ModuleCleanerPass())

class ModuleEliminatorPass(moduleName : Identifier) extends RewritePass {
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    if (module.id == moduleName) {
      Some(module)
    } else {
      None
    }
  }
}

class ModuleEliminator(moduleName : Identifier) extends ASTRewriter(
    "ModuleEliminator", new ModuleEliminatorPass(moduleName))