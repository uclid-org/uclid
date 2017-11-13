package uclid
package lang

class ModuleCleanerPass extends RewritePass {
  override def rewriteTypeDecl(typDec : TypeDecl, ctx : ScopeMap) : Option[TypeDecl] = {
    None
  }
}

class ModuleCleaner extends ASTRewriter(
    "ModuleCleaner", new ModuleCleanerPass())