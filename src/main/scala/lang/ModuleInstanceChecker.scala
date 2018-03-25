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

 * Instance checking.
 *
 */
package uclid
package lang

import scala.collection.immutable.Map
import com.typesafe.scalalogging.Logger

class ModuleInstanceCheckerPass() extends ReadOnlyPass[List[ModuleError]] {
  lazy val logger = Logger(classOf[ModuleInstanceCheckerPass])

  def doesInstanceTypeMatch(modT : ModuleType, instT : ModuleInstanceType, in : List[ModuleError], pos : ASTPosition) : List[ModuleError] = {
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
                val msg = "Incorrect type for module " + argType + ": " + id.toString + ". Got " +
                          actualTyp.toString + ", expected " + expTyp.toString + " instead"
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

    // filter out shared variables.
    val wiredSharedVars = instT.args.filter((a) => modT.sharedVarMap.contains(a._1) && a._2.isDefined).map((a) => (a._1, a._2.get))
    val errs4 = checkTypes(wiredSharedVars, errs3, "sharedvar", modT.sharedVarMap)

    // ensure all shared variables are mapped.
    val unwiredSharedVars = modT.sharedVarMap.filter(v => !instT.argMap.contains(v._1))
    val unwiredSharedVarsErrors = unwiredSharedVars.map(v => ModuleError("Unmapped shared variable: " + v._1.toString, pos))

    errs4 ++ unwiredSharedVarsErrors
  }

  def checkInstance(inst : InstanceDecl, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    val targetModNamedExpr = context.map.get(inst.moduleId)
    targetModNamedExpr match {
      case None =>
        val error = ModuleError("Unknown module being instantiated: " + inst.moduleId.toString, inst.moduleId.position)
        error :: in
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.ModuleDefinition(targetMod) =>
            val targetModT = targetMod.moduleType
            Utils.assert(inst.instType.isDefined, "Instance type must be defined at this point!")
            val err1 = doesInstanceTypeMatch(targetModT, inst.instType.get, in, inst.position)
            // make sure all outputs are wired to identifiers.
            val outputExprs = inst.arguments.filter(a => targetModT.outputMap.contains(a._1) && a._2.isDefined).map(a => a._2.get)
            val sharedVarExprs = inst.arguments.filter(a => targetModT.sharedVarMap.contains(a._1) && a._2.isDefined).map(a => a._2.get)
            logger.debug("Outputs: {}", outputExprs.toString())
            val err2 = outputExprs.foldLeft(err1) {
              (acc, arg) => {
                arg match {
                  case Identifier(_) => acc
                  case _ =>
                    val msg = "Invalid module output : '%s'".format(arg.toString)
                    ModuleError(msg, arg.position) :: acc
                }
              }
            }
            sharedVarExprs.foldLeft(err2) {
              (acc, arg) => {
                arg match {
                  case Identifier(_) => acc
                  case _ =>
                    val msg = "Invalid shared variable : '%s'; must be an identifier".format(arg.toString())
                    ModuleError(msg, arg.position) :: acc
                }
              }
            }
          case _ =>
            val error = ModuleError("Module not in scope: " + inst.moduleId.toString, inst.moduleId.position)
            error :: in
        }
    }
  }

  override def applyOnInstance(d : TraversalDirection.T, inst : InstanceDecl, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      // only need to check in one direction.
      checkInstance(inst, in, context)
    } else {
      in
    }
  }
}

class ModuleInstanceChecker() extends ASTAnalyzer(
    "ModuleInstanceChecker", new ModuleInstanceCheckerPass())
{
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, List.empty, context)
    if (out.size > 0) {
      throw new Utils.ParserErrorList(out.map(e => (e.msg, e.position)))
    }
    Some(module)
  }
}

