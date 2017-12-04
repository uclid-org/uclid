package uclid
package lang

import scala.reflect.ClassTag

class ExternalSymbolMap (
  val nameProvider : Option[ContextualNameProvider], val externalMap: Map[ExternalIdentifier, (Identifier, ModuleExternal)]) {

  def + (module : Module, context : Scope) : ExternalSymbolMap = {
    val newProvider = new ContextualNameProvider(context, "$external_function")
    new ExternalSymbolMap(Some(newProvider), externalMap)
  }

  def + (extId : ExternalIdentifier, extDecl : ModuleExternal) : ExternalSymbolMap = {
    val newName : Identifier = nameProvider.get.apply(extDecl.extName, extId.moduleId.toString)
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

  /*
  override def rewriteModule(mod : Module, context : Scope) : Option[Module] = {
    val funcMap : Map[ExternalIdentifier, (Identifier, FunctionDecl)] = externalTypeAnalysis.out.get.functionMap
    val newFunctions : List[FunctionDecl] = funcMap.map(e => FunctionDecl(e._2._1, e._2._2.sig)).toList
    val modP = Module(mod.id, newFunctions ++ mod.decls, mod.cmds)
    Some(modP)
  }

  override def rewriteExternalIdentifier(eId : ExternalIdentifier, context : Scope) : Option[Expr] = {
    val funcMap : Map[ExternalIdentifier, (Identifier, FunctionDecl)] = externalTypeAnalysis.out.get.functionMap
    val idP = funcMap.get(eId)
    Utils.assert(idP.isDefined, "Unknown external identifiers must have been eliminated by now: " + eId.toString)
    Some(idP.get._1)
  }
  */

