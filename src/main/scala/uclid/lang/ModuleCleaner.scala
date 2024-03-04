package uclid
package lang

class ModuleCleanerPass() extends RewritePass {
  override def rewriteModuleTypesImport(modTypImport : ModuleTypesImportDecl, ctx : Scope) : Option[ModuleTypesImportDecl] = {
    None
  }
  override def rewriteModuleFunctionsImport(modFuncImport : ModuleFunctionsImportDecl, ctx : Scope) : Option[ModuleFunctionsImportDecl] = {
    None
  }
  override def rewriteModuleSynthFunctionsImport(modSynthFuncImport : ModuleSynthFunctionsImportDecl, ctx : Scope) : Option[ModuleSynthFunctionsImportDecl] = {
    None
  }
  override def rewriteModuleConstantsImport(modCnstImport : ModuleConstantsImportDecl, ctx : Scope) : Option[ModuleConstantsImportDecl] = {
    None
  }
  override def rewriteModuleDefinesImport(modDefImport : ModuleDefinesImportDecl, ctx : Scope) : Option[ModuleDefinesImportDecl] = {
    None
  }
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val declsP = module.decls.sortWith((d1, d2) => d1.hashCode() < d2.hashCode())
    Some(Module(module.id, declsP, module.cmds, module.notes))
  }
}

class ModuleCleaner() extends ASTRewriter(
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
