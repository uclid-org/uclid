package uclid
package lang

class ModuleInstanceCheckerPass(modules : List[Module]) extends ReadOnlyPass[List[ModuleError]] {
  val moduleNames = modules.map(_.id).toSet
  
  def checkInstance(inst : InstanceDecl, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (!moduleNames.contains(inst.instanceId)) {
      val error = ModuleError("Unknown module being instantiated: " + inst.instanceId.toString, inst.instanceId.position)
      error :: in
    } else {
      in
    }
  }
  override def applyOnInstance(d : TraversalDirection.T, inst : InstanceDecl, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      // only need to check in one direction.
      checkInstance(inst, in, context)
    } else {
      in
    }
  }
}

class ModuleInstanceChecker(modules : List[Module]) extends ASTAnalyzer(
    "ModuleInstanceChecker", new ModuleInstanceCheckerPass(modules))
{
  override def reset() {
    in = Some(List.empty[ModuleError])
  }
}

class ModuleInstantiator {
  
}