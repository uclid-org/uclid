package uclid
package lang

class ExternalTypeMap (val errors : Set[ModuleError], val typeMap : Map[ExternalType, Type]) {
  def + (error : ModuleError) : ExternalTypeMap =
    new ExternalTypeMap(errors + error, typeMap)

  def + (extT: ExternalType, typ: Type)  : ExternalTypeMap =
    new ExternalTypeMap(errors, typeMap + (extT -> typ))

  def toParserErrorList = new Utils.ParserErrorList(errors.toList.map(e => (e.msg, e.position)))
}

object ExternalTypeMap {
  def empty = {
    new ExternalTypeMap(Set.empty, Map.empty)
  }
}

class ExternalTypeAnalysisPass extends ReadOnlyPass[ExternalTypeMap] {
  override def applyOnExternalType(d : TraversalDirection.T, extT : ExternalType, in : ExternalTypeMap, context : Scope) : ExternalTypeMap = {
    // do this in only only one direction.
    if (d == TraversalDirection.Down) {
      return in
    }
    // have we already seen this type?
    if (in.typeMap.contains(extT)) {
      return in
    }

    // look this type up in the module.
    context.moduleDefinitionMap.get(extT.moduleId) match {
      case Some(mod) =>
        mod.typeDeclarationMap.get(extT.typeId) match {
          case Some(typ) =>
            in + (extT, typ)
          case None =>
            val error = ModuleError("Unknown type '%s' in module '%s'".format(extT.typeId.toString, mod.id.toString), extT.typeId.position)
            in + error
        }
      case None =>
        val error = ModuleError("Unknown module: %s".format(extT.moduleId.toString), extT.moduleId.position)
        in + error
    }
  }

  override def applyOnExternalIdentifier(d : TraversalDirection.T, eId : ExternalIdentifier, in  : ExternalTypeMap, context : Scope) : ExternalTypeMap = {
    // only one direction.
    if (d == TraversalDirection.Down) {
      return in
    }
    context.moduleDefinitionMap.get(eId.moduleId) match {
      case Some(mod) =>
        mod.externalMap.get (eId.id) match {
          case Some(funcDecl) => in
          case None =>
            val error = ModuleError("Unknown identifier '%s' in module '%s'".format(eId.id, eId.moduleId), eId.id.position)
            in + error
        }
      case None =>
        val error = ModuleError("Unknown module: %s".format(eId.moduleId.toString), eId.moduleId.position)
        in + error
    }
  }
}

class ExternalTypeAnalysis extends ASTAnalyzer("ExternalTypeAnalysis", new ExternalTypeAnalysisPass()) {
  override def reset() {
    in = Some(ExternalTypeMap.empty)
  }
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val analysisResult = visitModule(module, _in.get, context)
    if (analysisResult.errors.size > 0) {
      throw analysisResult.toParserErrorList
    }
    _out = Some(analysisResult)
    return Some(module)
  }
}

class ExternalTypeRewriterPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val externalTypeAnalysis = manager.pass("ExternalTypeAnalysis").asInstanceOf[ExternalTypeAnalysis]

  override def rewriteExternalType(extT : ExternalType, context : Scope) : Option[Type] = {
    val typeMap : Map[ExternalType, Type] = externalTypeAnalysis.out.get.typeMap
    val typP = typeMap.get(extT)
    Utils.assert(typP.isDefined, "Unknown external types must have been eliminated by now.")
    typP
  }
}

class ExternalTypeRewriter extends ASTRewriter("ExternalTypeRewriter", new ExternalTypeRewriterPass())

