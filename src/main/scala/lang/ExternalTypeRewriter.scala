package uclid
package lang

class ExternalTypeAnalysisPass extends ReadOnlyPass[(List[ModuleError], Map[ExternalType, Type])] {
  type T = (List[ModuleError], Map[ExternalType, Type])
  override def applyOnExternalType(d : TraversalDirection.T, extT : ExternalType, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      if (in._2.contains(extT)) {
        in
      } else {
        context.moduleDefinitionMap.get(extT.moduleId) match {
          case Some(mod) =>
            mod.typeDeclarationMap.get(extT.typeId) match {
              case Some(typ) => 
                (in._1, in._2 + (extT -> typ))
              case None =>
                val msg = "Unknown type '%s' in module '%s'.".format(extT.typeId.toString, mod.id.toString)
                (ModuleError(msg, extT.typeId.position) :: in._1, in._2)
            }
          case None =>
            val msg = "Unknown module: %s.".format(extT.moduleId.toString)
            (ModuleError(msg, extT.moduleId.position) :: in._1, in._2)
        }
      }
    } else {
      in
    }
  }
}
class ExternalTypeAnalysis extends ASTAnalyzer("ExternalTypeAnalysis", new ExternalTypeAnalysisPass()) {
  in = Some((List.empty[ModuleError], Map.empty[ExternalType, Type]))
  
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val analysisResult = visitModule(module, _in.get, context) 
    val errors = analysisResult._1
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
    _out = Some(analysisResult)
    return Some(module)
  }
}

class ExternalTypeRewriterPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val externalTypeAnalysis = manager.pass("ExternalTypeAnalysis").asInstanceOf[ExternalTypeAnalysis]
  lazy val typeMap : Map[ExternalType, Type] = externalTypeAnalysis.out.get._2

  override def rewriteExternalType(extT : ExternalType, context : Scope) : Option[Type] = {
    val typP = typeMap.get(extT)
    Utils.assert(typP.isDefined, "Unknown external types must have been eliminated by now.")
    typP
  }
}

class ExternalTypeRewriter extends ASTRewriter("ExternalTypeRewriter", new ExternalTypeRewriterPass())

