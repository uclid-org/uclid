/*
 * ControlCommandChecker.
 * 
 * Walks through the control section of a module and checks if the commands are well-formed.
 */
package uclid
package lang

class ControlCommandCheckerPass extends ReadOnlyPass[Unit] {
  def checkNoArgs(cmd : ProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 0, "'initialize' command does not expect any arguments.", cmd.pos, filename)
  }
  def checkNoParams(cmd : ProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.params.size == 0, "'initialize' command does not except any parameters.", cmd.pos, filename)
  }
  def checkHasOneIntLitArg(cmd : ProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 1, "'simulate' command expects exactly one argument.", cmd.pos, filename)
    val cntLit = cmd.args(0)
    Utils.checkParsingError(cntLit.isInstanceOf[IntLit], "'simulate' command expects a constant integer argument.", cmd.pos, filename)
    val cnt = cntLit.asInstanceOf[IntLit].value
    val cntInt = cnt.intValue()
    Utils.checkParsingError(cntInt == cnt, "Argument to simulate is too large.", cmd.pos, filename)
  }
  override def applyOnCmd(d : TraversalDirection.T, cmd : ProofCommand, in : Unit, context : ScopeMap) : Unit = {
    val filename = context.module.flatMap(_.filename)
    cmd.name.toString match {
      case "clear_context" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
      case "initialize" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
      case "simulate" =>
        checkNoParams(cmd, filename)
        checkHasOneIntLitArg(cmd, filename)
      case "k_induction_base" =>
        checkNoParams(cmd, filename)
        checkHasOneIntLitArg(cmd, filename)
      case "k_induction_step" =>
        checkNoParams(cmd, filename)
        checkHasOneIntLitArg(cmd, filename)
      case "decide" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
      case "print_results" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
      case "print_cex" =>
        checkNoParams(cmd, filename)
      case "print_module" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
      case _ =>
        Utils.raiseParsingError("Unknown control command: " + cmd.name.toString, cmd.pos, filename)
    }
  }
}

class ControlCommandChecker extends ASTAnalyzer("ContralCommandChecker", new ControlCommandCheckerPass())  {
  in = Some(Unit)
}
