package uclid
package lang

import scala.reflect.ClassTag

class ExternalSymbolMap (
  val nameProvider : Option[ContextualNameProvider], val externalMap: Map[ExternalIdentifier, (Identifier, ModuleExternal)]) {

  def + (module : Module, context : Scope) : ExternalSymbolMap = {
    val newProvider = new ContextualNameProvider(context, "$external")
    new ExternalSymbolMap(Some(newProvider), externalMap)
  }

  def + (extId : ExternalIdentifier, extDecl : ModuleExternal) : ExternalSymbolMap = {
    val newName : Identifier = nameProvider.get.apply(extId.id, extId.moduleId.toString)
    new ExternalSymbolMap(nameProvider, externalMap + (extId -> (newName, extDecl)))
  }

  def getOrAdd(extId : ExternalIdentifier, extDecl : ModuleExternal) : (ExternalSymbolMap, Identifier) = {
    externalMap.get(extId) match {
      case Some((newName, extDecl)) =>
        (this, newName)
      case None =>
        val newMap = this + (extId, extDecl)
        (newMap, newMap.externalMap.get(extId).get._1)
    }
  }
}

object ExternalSymbolMap {
  def empty = {
    new ExternalSymbolMap(None, Map.empty)
  }
}

class ExternalSymbolAnalysisPass extends ReadOnlyPass[ExternalSymbolMap] {
  override def applyOnModule(d : TraversalDirection.T, mod : Module, in : ExternalSymbolMap, context : Scope) : ExternalSymbolMap = {
    in + (mod, context)
  }
  override def applyOnExternalIdentifier(d : TraversalDirection.T, eId : ExternalIdentifier, in  : ExternalSymbolMap, context : Scope) : ExternalSymbolMap = {
    context.moduleDefinitionMap.get(eId.moduleId) match {
      case Some(mod) =>
        mod.externalMap.get (eId.id) match {
          case Some(modExt) => in + (eId, modExt)
          case None =>
            throw new Utils.RuntimeError("Unknown ExternalIdentifiers must have been eliminated by now.")
        }
      case None =>
        throw new Utils.RuntimeError("Unknown ExternalIdentifiers must have been eliminated by now.")
    }
  }
}

class ExternalSymbolAnalysis extends ASTAnalyzer("ExternalSymbolAnalysis", new ExternalSymbolAnalysisPass()) {
  override def reset() {
    in = Some(ExternalSymbolMap.empty)
  }
}

class ExternalSymbolRewriterPass(externalSymbolMap: ExternalSymbolMap) extends RewritePass {
  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    val extDecls = externalSymbolMap.externalMap.map(p => {
      p._2._2 match {
        case f : FunctionDecl => FunctionDecl(p._2._1, f.sig)
        case c : ConstantsDecl => ConstantsDecl(List(p._2._1), c.typ)
      }
    }).toList
    Some(Module(module.id, extDecls ++ module.decls, module.cmds, module.notes))
  }
  override def rewriteExternalIdentifier(extId : ExternalIdentifier, context : Scope) : Option[Expr] = {
    externalSymbolMap.externalMap.get(extId) match {
      case Some((newId, _)) => Some(newId)
      case None => throw new Utils.RuntimeError("Unknown external identifiers must have been eliminated by now: " + extId.toString)
    }
  }
}

class ExternalSymbolRewriter(externalSymbolMap: ExternalSymbolMap) extends ASTRewriter(
    "ExternalSymbolRewriter", new ExternalSymbolRewriterPass(externalSymbolMap))
