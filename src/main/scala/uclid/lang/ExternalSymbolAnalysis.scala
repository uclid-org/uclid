package uclid
package lang

class ExternalSymbolMap (val externalMap: Map[ExternalIdentifier, (Identifier, ModuleExternal)]) {

  def + (module : Module, context : Scope) : ExternalSymbolMap = {
    new ExternalSymbolMap(externalMap)
  }

  def + (extId : ExternalIdentifier, extDecl : ModuleExternal, context : Scope) : ExternalSymbolMap = {
    val newName : Identifier = NameProvider.get(extId.id.toString + "_" + extId.moduleId.toString)
    new ExternalSymbolMap(externalMap + (extId -> (newName, extDecl)))
  }

  def getOrAdd(extId : ExternalIdentifier, extDecl : ModuleExternal, context : Scope) : (ExternalSymbolMap, Identifier) = {
    externalMap.get(extId) match {
      case Some((newName, extDecl)) =>
        (this, newName)
      case None =>
        val newMap = this.+(extId, extDecl, context)
        (newMap, newMap.externalMap.get(extId).get._1)
    }
  }
}

object ExternalSymbolMap {
  def empty = {
    new ExternalSymbolMap(Map.empty)
  }
}

class ExternalSymbolAnalysisPass extends ReadOnlyPass[ExternalSymbolMap] {
  override def applyOnModule(d : TraversalDirection.T, mod : Module, in : ExternalSymbolMap, context : Scope) : ExternalSymbolMap = {
    in.+(mod, context)
  }
  override def applyOnExternalIdentifier(d : TraversalDirection.T, eId : ExternalIdentifier, in  : ExternalSymbolMap, context : Scope) : ExternalSymbolMap = {
    context.moduleDefinitionMap.get(eId.moduleId) match {
      case Some(mod) =>
        mod.externalMap.get (eId.id) match {
          case Some(modExt) => in.+(eId, modExt, context)
          case None =>
            throw new Utils.RuntimeError("Unknown ExternalIdentifiers must have been eliminated by now.")
        }
      case None =>
        throw new Utils.RuntimeError("Unknown ExternalIdentifiers must have been eliminated by now.")
    }
  }
}

class ExternalSymbolAnalysis extends ASTAnalyzer("ExternalSymbolAnalysis", new ExternalSymbolAnalysisPass()) {
  override def reset(): Unit = {
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
