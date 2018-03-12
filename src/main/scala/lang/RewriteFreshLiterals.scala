package uclid
package lang

object FindFreshLiteralsPass {
  case class T(nameProvider : Option[ContextualNameProvider], inputs: List[(IdGenerator.Id, InputVarsDecl)]) {
    def getNewName(name : Identifier, tag : String) = {
      nameProvider match {
        case Some(provider) =>
          provider.apply(name, tag)
        case None =>
          throw new Utils.RuntimeError("ContextualNameProvider not defined.")
      }
    }
  }
}

class FindFreshLiteralsPass extends ReadOnlyPass[FindFreshLiteralsPass.T] {
  type T = FindFreshLiteralsPass.T
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      FindFreshLiteralsPass.T(Some(new ContextualNameProvider(context, "fresh")), in.inputs)
    } else {
      FindFreshLiteralsPass.T(None, in.inputs)
    }
  }
  override def applyOnFreshLit(d : TraversalDirection.T, f : FreshLit, in : T, context : Scope) : T = {
    val newInput = InputVarsDecl(List(in.getNewName(Identifier("nd"), f.typ.toString)), f.typ)
    FindFreshLiteralsPass.T(in.nameProvider, (f.astNodeId, newInput) :: in.inputs)
  }
}

class FindFreshLiterals extends ASTAnalyzer("FindFreshLiterals", new FindFreshLiteralsPass()) {
  in = Some(FindFreshLiteralsPass.T(None, List.empty))
  lazy val literalMap : Map[IdGenerator.Id, InputVarsDecl] = out.get.inputs.toMap
  lazy val declarations : List[InputVarsDecl] = out.get.inputs.map(_._2)
}

class RewriteFreshLiteralsPass extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val findFreshLiterals = manager.pass("FindFreshLiterals").asInstanceOf[FindFreshLiterals]

  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    val moduleP = Module(module.id, findFreshLiterals.declarations ++ module.decls, module.cmds, module.notes)
    Some(moduleP)
  }
  override def rewriteFreshLit(f : FreshLit, context : Scope) : Option[Expr] = {
    findFreshLiterals.literalMap.get(f.astNodeId) match {
      case Some(inpDecl) => Some(inpDecl.ids(0))
      case None          => throw new Utils.RuntimeError("All FreshLit instances must be in map.")
    }
  }
}

class RewriteFreshLiterals extends ASTRewriter("RewriteFreshLiterals", new RewriteFreshLiteralsPass())