package uclid
package lang

class ExternalTypeRewriterPass extends RewritePass {
  override def rewriteExternalType(extT : ExternalType, context : Scope) : Option[Type] = {
    println("external type: " + extT.toString)
    println("context::module: " + context.moduleDefinitionMap.toString)

    context.moduleDefinitionMap.get(extT.moduleId) match {
      case Some(mod) =>
        mod.typeDeclarationMap.get(extT.typeId) match {
          case Some(typ) => Some(typ)
          case None => 
            println("Can't find type in module!")
            Some(extT)
        }
      case None =>
        println("Can't find module!")
        Some(extT)
    }
  }
}
class ExternalTypeRewriter extends ASTRewriter(
    "ExternalTypeRewriter", new ExternalTypeRewriterPass())
