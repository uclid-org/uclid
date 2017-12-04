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
  override def applyOnCmd(d : TraversalDirection.T, cmd : ProofCommand, in : Unit, context : Scope) : Unit = {
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
