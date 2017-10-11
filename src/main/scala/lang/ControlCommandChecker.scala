package uclid
package lang

class ControlCommandCheckerPass extends ReadOnlyPass[Unit] {
  override def applyOnCmd(d : TraversalDirection.T, cmd : ProofCommand, in : Unit, context : ScopeMap) : Unit = {
    val filename = context.module.flatMap(_.filename)
    cmd.name.toString match {
      case "initialize" => 
        Utils.checkParsingError(cmd.params.size == 0, "'initialize' command does not except any parameters.", cmd.pos, filename)
        Utils.checkParsingError(cmd.args.size == 0, "'initialize' command does not expect any arguments.", cmd.pos, filename)
      case "simulate" =>
        Utils.checkParsingError(cmd.params.size == 0, "'simulate' command does not expect any parameters.", cmd.pos, filename)
        Utils.checkParsingError(cmd.args.size == 1, "'simulate' command expects exactly one argument.", cmd.pos, filename)
        val cntLit = cmd.args(0)
        Utils.checkParsingError(cntLit.isInstanceOf[IntLit], "'simulate' command expects a constant integer argument.", cmd.pos, filename)
        val cnt = cntLit.asInstanceOf[IntLit].value
        val cntInt = cnt.intValue()
        Utils.checkParsingError(cntInt == cnt, "Argument to simulate is too large.", cmd.pos, filename)
      case "decide" =>
        Utils.checkParsingError(cmd.params.size == 0, "'decide' command does not except any parameters.", cmd.pos, filename)
        Utils.checkParsingError(cmd.args.size == 0, "'decide' command does not expect any arguments.", cmd.pos, filename)
      case "print_module" =>
        Utils.checkParsingError(cmd.params.size == 0, "'print_module' command does not except any parameters.", cmd.pos, filename)
        Utils.checkParsingError(cmd.args.size == 0, "'print_module' command does not expect any arguments.", cmd.pos, filename)
    }
  }
}

class ControlCommandChecker extends ASTAnalyzer("ContralCommandChecker", new ControlCommandCheckerPass())  {
  in = Some(Unit)
}
