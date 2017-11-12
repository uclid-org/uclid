package uclid
package lang

class ModuleInstanceCheckerPass(modules : List[Module]) extends ReadOnlyPass[List[ModuleError]] {
  val moduleMap = modules.map(m => (m.id -> m)).toMap

  def doesInstanceTypeMatch(modT : ModuleType, instT : ModuleInstanceType, in : List[ModuleError]) : List[ModuleError] = {
    // check the types of a list of pairs of identifiers and types..
    def checkTypes(args : List[(Identifier, Type)], in : List[ModuleError], argType : String, typeMap : Map[Identifier, Type]) : List[ModuleError] = {
      args.foldLeft(in) {
        (acc, arg) => {
          val id = arg._1
          val actualTyp = arg._2
          typeMap.get(id) match {
            case Some(expTyp) =>
              if (actualTyp.matches(expTyp)) {
                acc
              } else {
                val msg = "Incorrect type for module " + argType + ": " + id.toString + ". Expected " + 
                          actualTyp.toString + ", got " + expTyp.toString + " instead."
                ModuleError(msg, id.position) :: acc
              }
            case None =>
              // we've already reported this.
              acc
          }
        }
      }
    }
  
    // first check there are no unknown arguments (arguments that don't correspond to the I/Os of module).
    val badArgs = instT.args.map(_._1).filter(a => !modT.argSet.contains(a))
    val errs1 = badArgs.foldLeft(in) { 
      (acc, arg) => {
        ModuleError("Unknown module input/output: " + arg.toString, arg.position) :: acc
      }
    }
    // for this first let's filter out the inputs who are "wired"
    val wiredInputs = instT.args.filter((a) => modT.inputMap.contains(a._1) && a._2.isDefined).map((a) => (a._1, a._2.get))
    // now check that all input types match.
    val errs2 = checkTypes(wiredInputs, errs1, "input", modT.inputMap)

    // filter out wired outputs.
    val wiredOutputs = instT.args.filter((a) => modT.outputMap.contains(a._1) && a._2.isDefined).map((a) => (a._1, a._2.get))
    // check output types.
    val errs3 = checkTypes(wiredOutputs, errs2, "output", modT.outputMap)
    errs3
  }
  
  def checkInstance(inst : InstanceDecl, in : List[ModuleError], context : ScopeMap) : List[ModuleError] = {
    moduleMap.get(inst.moduleId) match {
      case None =>
        val error = ModuleError("Unknown module being instantiated: " + inst.moduleId.toString, inst.moduleId.position)
        error :: in
      case Some(targetMod) =>
        val targetModT = targetMod.moduleType
        Utils.assert(inst.instType.isDefined, "Instance type must be defined at this point!")
        val err1 = doesInstanceTypeMatch(targetModT, inst.instType.get, in)
        // make sure all outputs are wired to identifiers.
        val outputExprs = inst.arguments.filter(a => targetModT.outputMap.contains(a._1) && a._2.isDefined).map(_._2.get)
        outputExprs.foldLeft(err1) { 
          (acc, arg) => {
            arg match {
              case Identifier(name) =>
                acc
              case _ =>
                val msg = "Invalid module output: " + arg.toString() + "."
                ModuleError(msg, arg.position) :: acc
            }
          }
        }
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
  override def finish() {
    val errors = out.get
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map((e) => (e.msg, e.position)))
    }
  }
}

class ModuleInstantiator {
  
}