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

 * Ensure that old(x) and history(x) are used only in verification expressions
 * (assertions, invariants etc.).
 *
 */
package uclid
package lang
import com.typesafe.scalalogging.Logger


class VerificationExpressionCheckerPass extends ReadOnlyPass[List[ModuleError]]
{
  lazy val logger = Logger(classOf[VerificationExpressionCheckerPass])
  type T = List[ModuleError]
  override def applyOnOperatorApp(d : TraversalDirection.T, opapp : OperatorApplication, in : T, context : Scope) : T = {
    logger.debug("Visiting: {}; Env: {}", opapp.toString, context.environment.toString())
    if (d == TraversalDirection.Up) {
      if (context.environment.isModuleLevel && context.environment.isVerificationContext) {
        opapp.op match {
          case GetNextValueOp() =>
            ModuleError("Primed variables are not allowed in module-level assertions/assumptions", opapp.position) :: in
          case HyperSelect(i) =>
            if (!context.environment.inHyperproperty) {
              ModuleError("Trace select can only be used in a verification expression", opapp.position) :: in
            } else {
              in
            }
          case _ =>
          in
        }
      } else if (context.environment.isProcedural) {
        opapp.op match {
          case GetNextValueOp() =>
            ModuleError("Primed variables can't be referenced inside procedures", opapp.position) :: in
          case HyperSelect(i) =>
            ModuleError("Trace select can only be used in a verification expression", opapp.position) :: in
          case _ => in
        }
      } else if (!context.environment.isVerificationContext) {
        opapp.op match {
          case OldOperator() | HistoryOperator() | PastOperator() =>
            ModuleError("Operator can only be used in a verification expression", opapp.position) :: in
          case HyperSelect(i) =>
            ModuleError("Trace select can only be used in a verification expression", opapp.position) :: in
          case _ =>
            in
        }
      } else if (!context.environment.isModuleLevel) {
        // deal with old operators.
        val errs1 = context.environment match {
          case RequiresEnvironment =>
            opapp.op match {
              case OldOperator() =>
                ModuleError("Old operator can't be used in a requires expression", opapp.position) :: in
              case _ => in
            }
          case _ => in
        }
        // deal with hyperselect
        opapp.op match {
          case HyperSelect(i) =>
            ModuleError("Trace select can only be used in a module-level expression", opapp.position) :: errs1
          case _ =>
            errs1
        }
      } else {
        in
      }
    } else {
      in
    }
  }
}

class VerificationExpressionChecker extends ASTAnalyzer("VerificationExpressionChecker", new VerificationExpressionCheckerPass())  {
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, List.empty[ModuleError], context)
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}
