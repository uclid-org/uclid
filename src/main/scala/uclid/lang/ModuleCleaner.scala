package uclid
package lang

class ModuleCleanerPass(mainModuleName : Identifier) extends RewritePass {
  override def rewriteModuleTypesImport(modTypImport : ModuleTypesImportDecl, ctx : Scope) : Option[ModuleTypesImportDecl] = {
    None
  }
  override def rewriteModuleFunctionsImport(modFuncImport : ModuleFunctionsImportDecl, ctx : Scope) : Option[ModuleFunctionsImportDecl] = {
    None
  }
  override def rewriteModuleConstantsImport(modCnstImport : ModuleConstantsImportDecl, ctx : Scope) :
  Option[ModuleConstantsImportDecl] = {
    None
  }
  override def rewriteProcedure(proc : ProcedureDecl, ctx : Scope) : Option[ProcedureDecl] = {
    if (ctx.module.get.id != mainModuleName) {
      None
    } else {
      Some(proc)
    }
  }
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val declsP = module.decls.sortWith((d1, d2) => d1.hashId < d2.hashId)
    Some(Module(module.id, declsP, module.cmds, module.notes))
  }
}

class ModuleCleaner(mainModuleName : Identifier) extends ASTRewriter(
    "ModuleCleaner", new ModuleCleanerPass(mainModuleName))

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
