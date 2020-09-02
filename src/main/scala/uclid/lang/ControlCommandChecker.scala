/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
    Utils.checkParsingError(cmd.resultVar.isEmpty, "'%s' command does not produce a result".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkNoArgObj(cmd : GenericProofCommand, filename: Option[String]) {
    Utils.checkParsingError(cmd.argObj.isEmpty, "'%s' command does not expect an argument object".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasArgObj(cmd : GenericProofCommand, filename: Option[String]) {
    Utils.checkParsingError(cmd.argObj.isDefined, "'%s' command expects an argument object".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkNoArgs(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 0, "'%s' command does not expect any arguments".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkNoParams(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.params.size == 0, "'%s' command does not expect any parameters".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasOneIntLitArg(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 1, "'%s' command expects exactly one argument".format(cmd.name.toString), cmd.pos, filename)
    val cntLit = cmd.args(0)
    Utils.checkParsingError(cntLit._1.isInstanceOf[IntLit], "'%s' command expects a constant integer argument".format(cmd.name.toString), cmd.pos, filename)
    val cnt = cntLit._1.asInstanceOf[IntLit].value
    val cntInt = cnt.intValue
    Utils.checkParsingError(cntInt == cnt, "Argument to '%s' is too large".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasOneStringLitArg(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 1, "'%s' command expects exactly one argument".format(cmd.name.toString), cmd.pos, filename)
    val cntLit = cmd.args(0)
    Utils.checkParsingError(cntLit._1.isInstanceOf[StringLit], "'%s' command expects a string literal as an argument".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkHasOneIdentifierArg(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size == 1, "'%s' command expects exactly one argument".format(cmd.name.toString), cmd.pos, filename)
    val cntLit = cmd.args(0)
    Utils.checkParsingError(cntLit._1.isInstanceOf[Identifier], "'%s' command expects a identifier as argument".format(cmd.name.toString), cmd.pos, filename)
  }
  def checkSetOptionCmd(cmd : GenericProofCommand, filename: Option[String]): Unit = {
    Utils.checkParsingError(cmd.args.size == 2, "'%s' command expects exactly two arguments".format(cmd.name.toString()), cmd.pos, filename)
    val optionName = cmd.args(0)._1
    Utils.checkParsingError(
      optionName.isInstanceOf[StringLit], "First argument to '%s' must be a string".format(cmd.name.toString()),
      cmd.pos, filename)
    val optionValue = cmd.args(0)
    Utils.checkParsingError(
      optionValue._1 match {
        case StringLit(_) | IntLit(_) | BoolLit(_) => true
        case _ => false
      },
      "Second argument to '%s' must be a string, integer or Boolean literal".format(cmd.name.toString),
      cmd.pos, filename
    )
  }
  def checkHasZeroOrOneIntLitArg(cmd : GenericProofCommand, filename : Option[String]) {
    Utils.checkParsingError(cmd.args.size <= 1, "'%s' command expects no more than one argument".format(cmd.name.toString), cmd.pos, filename)
    if (cmd.args.size > 0) {
      val cntLit = cmd.args(0)
      Utils.checkParsingError(cntLit._1.isInstanceOf[IntLit], "'%s' command expects a constant integer argument".format(cmd.name.toString), cmd.pos, filename)
      val cnt = cntLit._1.asInstanceOf[IntLit].value
      val cntInt = cnt.intValue
      Utils.checkParsingError(cntInt == cnt, "Argument to '%s' is too large".format(cmd.name.toString), cmd.pos, filename)
    }
  }
  def checkPropertiesValid(paramName: Identifier, cmd : GenericProofCommand, context : Scope, filename : Option[String]) {
    def idIsProperty(id : Identifier) : Boolean = {
      context.get(id) match {
        case Some(Scope.SpecVar(_, _, _)) => true
        case _ => false
      }
    }
    val propertyParams = cmd.params.filter(p => p.name == paramName).flatMap(p => p.values)
    val invalidProperties = propertyParams.filter(p => !p.isInstanceOf[Identifier])
    if (invalidProperties.size > 0) {
      val badPropertyStr = "Invalid properties: " + Utils.join(invalidProperties.map(_.toString()), ", ")
      Utils.raiseParsingError(badPropertyStr, cmd.pos, filename)
    } 
    val properties = propertyParams.map(p => p.asInstanceOf[Identifier])
    val badProperties = properties.filter(p => !idIsProperty(p))
    lazy val badParamStr = Utils.join(badProperties.map(_.toString), ", ")
    lazy val errorMsg = if (badProperties.size == 1) {
      "Unknown property in %s command: %s".format(cmd.name.toString, badParamStr)
    } else {
      "Unknown properties in %s command: %s".format(cmd.name.toString, badParamStr)
    }
    Utils.checkParsingError(badProperties.size == 0, errorMsg, cmd.pos, filename)
  }
  def checkParamIsALogic(cmd : GenericProofCommand, context : Scope, filename : Option[String]) {
    Utils.checkParsingError(cmd.params.size == 1, "'%s' command expects one parameter specifying the logic".format(cmd.name.toString), cmd.pos, filename)
    def logicIsSupported(logic : String) : Boolean = {
      logic match {
        case "LIA" | "BV" | "ALL" => true
        case _ => false
      }
    }
    // TODO: Current way of specifying logic, change later if needed
    val logic = cmd.params(0).name.toString
    Utils.checkParsingError(logicIsSupported(logic), "'%s' command expects a supported logic as a parameter".format(cmd.name.toString), cmd.pos, filename)
  }
  override def applyOnCmd(d : TraversalDirection.T, cmd : GenericProofCommand, in : Unit, context : Scope) : Unit = {
    val filename = context.module.flatMap(_.filename)
    cmd.name.toString match {
      case "clear_context" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
        checkNoResultVar(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "set_solver_option" =>
        checkSetOptionCmd(cmd, filename)
      case "unroll" =>
        checkNoParams(cmd, filename)
        checkHasOneIntLitArg(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "lazysc" =>
        checkNoParams(cmd, filename)
        checkHasOneIntLitArg(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "induction" | "horn" =>
        checkPropertiesValid(Identifier("properties"), cmd, context, filename)
        checkPropertiesValid(Identifier("pre"), cmd, context, filename)
        checkPropertiesValid(Identifier("assumptions"), cmd, context, filename)
        checkHasZeroOrOneIntLitArg(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "bmc" =>
        checkPropertiesValid(Identifier("properties"), cmd, context, filename)
        checkHasOneIntLitArg(cmd, filename)
        checkNoArgObj(cmd, filename)
      case "verify" =>
        checkNoParams(cmd, filename)
        checkHasOneIdentifierArg(cmd, filename)
        checkNoArgObj(cmd, filename)
        val arg = cmd.args(0)._1.asInstanceOf[Identifier]
        val module = context.module.get
        lazy val errorMsg = "Unknown procedure: '%s'".format(arg.toString())
        Utils.checkParsingError(module.procedures.find(p => p.id == arg).isDefined, errorMsg, arg.pos, filename)
      case "synthesize_invariant" =>
        checkNoArgs(cmd, filename)
        checkParamIsALogic(cmd, context, filename)
        checkNoArgObj(cmd, filename)
        checkNoResultVar(cmd, filename)
      case "check" | "print_module" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
        checkNoArgObj(cmd, filename)
        checkNoResultVar(cmd, filename)
      case "print" =>
        checkHasOneStringLitArg(cmd, filename)
        checkNoParams(cmd, filename)
        checkNoArgObj(cmd, filename)
        checkNoResultVar(cmd, filename)
      case "print_results" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
      case "print_cex" =>
        checkNoParams(cmd, filename)
        checkNoResultVar(cmd, filename)
        checkHasArgObj(cmd, filename)
      case "dump_cex_vcds" =>
        checkNoArgs(cmd, filename)
        checkNoParams(cmd, filename)
        checkHasArgObj(cmd, filename)
        checkNoResultVar(cmd, filename)
      case _ =>
        Utils.raiseParsingError("Unknown control command: " + cmd.name.toString, cmd.pos, filename)
    }
  }
}

class ControlCommandChecker extends ASTAnalyzer("ContralCommandChecker", new ControlCommandCheckerPass())  {
  in = Some(())
}
