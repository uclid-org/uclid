package uclid
package lang

object FindFreshLiteralsPass {
  case class T(nameProvider : Option[ContextualNameProvider], inputs: List[(IdGenerator.Id, InputVarDecl)]) {
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
    val newInput = InputVarDecl(in.getNewName(Identifier("nd"), f.typ.toString), f.typ)
    FindFreshLiteralsPass.T(in.nameProvider, (f.astNodeId, newInput) :: in.inputs)
  }
}

class FindFreshLiterals extends ASTAnalyzer("FindFreshLiterals", new FindFreshLiteralsPass()) {
  in = Some(FindFreshLiteralsPass.T(None, List.empty))
}
    
class RewriteFreshLiterals extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  lazy val findFreshLiterals = manager.pass("FindFreshLiterals").asInstanceOf[FindFreshLiterals].pass
  
}