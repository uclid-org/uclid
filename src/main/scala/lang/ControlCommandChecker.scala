/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017. The Regents of the University of California (Regents).
 * All Rights Reserved.
 *
 * Permission to use, copy, modify, and distribute this software
 * and its documentation for educational, research, and not-for-profit purposes,
 * without fee and without a signed licensing agreement, is hereby granted,
 * provided that the above copyright notice, this paragraph and the following two
 * paragraphs appear in all copies, modifications, and distributions.
 *
 * Contact The Office of Technology Licensing, UC Berkeley, 2150 Shattuck Avenue,
 * Suite 510, Berkeley, CA 94720-1620, (510) 643-7201, otl@berkeley.edu,
 * http://ipira.berkeley.edu/industry-info for commercial licensing opportunities.
 *
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
 * INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING OUT OF
 * THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS
 * PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *
 * Author: Pramod Subramanyan

 * ControlCommandChecker.
 *
 * Walks through the control section of a module and checks if the commands are well-formed.
 */
package uclid
package lang

class ControlCommandCheckerPass extends ReadOnlyPass[Unit] {
  def checkNoResultVar(cmd : GenericProofCommand, filename: Option[String]) {
    Utils.checkParsingError(cmd.resultVar.isEmpty, "'%s' command does not produce a result.".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkNoArgObj(cmd : GenericProofCommand, filename: Option[String]) {
    Utils.checkParsingError(cmd.argObj.isEmpty, "'%s' command does not expect an argument object.".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasArgObj(cmd : GenericProofCommand, filename: Option[String]) {
    Utils.checkParsingError(cmd.argObj.isDefined, "'%s' command expects an argument object.".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkNoArgs(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 0, "'%s' command does not expect any arguments.".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkNoParams(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.params.size == 0, "'%s' command does not except any parameters.".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasOneIntLitArg(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 1, "'%s' command expects exactly one argument.".format(cmd.name.toString), cmd.pos, filename)
    val cntLit = cmd.args(0)
    Utils.checkParsingError(cntLit.isInstanceOf[IntLit], "'%s' command expects a constant integer argument.".format(cmd.name.toString), cmd.pos, filename)
    val cnt = cntLit.asInstanceOf[IntLit].value
    val cntInt = cnt.intValue()
    Utils.checkParsingError(cntInt == cnt, "Argument to '%s' is too large.".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasOneIdentifierArg(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 1, "'%s' command expects exactly one argument.".format(cmd.name.toString), cmd.pos, filename)
    val cntLit = cmd.args(0)
    Utils.checkParsingError(cntLit.isInstanceOf[Identifier], "'%s' command expects a identifier as argument.".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasZeroOrOneIntLitArg(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size <= 1, "'%s' command expects no more than one argument.".format(cmd.name.toString), cmd.pos, filename)
    if (cmd.args.size > 0) {
      val cntLit = cmd.args(0)
      Utils.checkParsingError(cntLit.isInstanceOf[IntLit], "'%s' command expects a constant integer argument.".format(cmd.name.toString), cmd.pos, filename)
      val cnt = cntLit.asInstanceOf[IntLit].value
      val cntInt = cnt.intValue()
      Utils.checkParsingError(cntInt == cnt, "Argument to '%s' is too large.".format(cmd.name.toString), cmd.pos, filename)
    }
  }
  def checkParamsAreProperties(cmd : GenericProofCommand, context : Scope, filename : Option[String]) {
    def idIsProperty(id : Identifier) : Boolean = {
      context.get(id) match {
        case Some(Scope.SpecVar(_, _)) => true
        case _ => false
      }
    }
    val badParams = cmd.params.filter(p => !idIsProperty(p))
    lazy val badParamStr = Utils.join(badParams.map(_.toString), ", ")
    lazy val errorMsg = if (badParams.size == 1) {
      "Unknown property in %s command: %s".format(cmd.name.toString, badParamStr)
    } else {
      "Unknown properties in %s command: %s".format(cmd.name.toString, badParamStr)
    }
    Utils.checkParsingError(badParams.size == 0, errorMsg, cmd.pos, filename)
  }
  override def applyOnCmd(d : TraversalDirection.T, cmd : GenericProofCommand, in : Unit, context : Scope) : Unit = {
    val filename = context.module.flatMap(_.filename)
    cmd.name.toString match {
      case "clear_context" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
        checkNoResultVar(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "unroll" =>
        checkNoParams(cmd, filename)
        checkHasOneIntLitArg(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "induction" =>
        checkNoParams(cmd, filename)
        checkHasZeroOrOneIntLitArg(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "bmc" =>
        checkParamsAreProperties(cmd, context, filename)
        checkHasOneIntLitArg(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "verify" =>
        checkNoParams(cmd, filename)
        checkHasOneIdentifierArg(cmd, filename)
        checkNoArgObj(cmd, filename)
        val arg = cmd.args(0).asInstanceOf[Identifier]
        val module = context.module.get
        lazy val errorMsg = "Unknown procedure: '%s'.".format(arg.toString())
        Utils.checkParsingError(module.procedures.find(p => p.id == arg).isDefined, errorMsg, arg.pos, filename)
      case "check" | "print_module" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
        checkNoArgObj(cmd, filename)
        checkNoResultVar(cmd, filename)
      case "print_results" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
      case "print_cex" | "print_smt2" =>
        checkNoParams(cmd, filename)
        checkNoResultVar(cmd, filename)
        checkHasArgObj(cmd, filename)
      case _ =>
        Utils.raiseParsingError("Unknown control command: " + cmd.name.toString, cmd.pos, filename)
    }
  }
}

class ControlCommandChecker extends ASTAnalyzer("ContralCommandChecker", new ControlCommandCheckerPass())  {
  in = Some(Unit)
}