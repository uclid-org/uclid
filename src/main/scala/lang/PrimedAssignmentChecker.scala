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
 *
 * Make sure that primed assignments are not used in the wrong place.
 *
 */
package uclid
package lang

class PrimedAssignmentCheckerPass extends ReadOnlyPass[Set[ModuleError]]
{
  type T = Set[ModuleError]
  def checkLhs(lhss : List[Lhs], in : T, context : Scope) : T = {
    val seqLhs = lhss.find(p => p.isProceduralLhs)
    val primedLhs = lhss.find(p => !p.isProceduralLhs)
    if (context.environment == ProceduralEnvironment) {
      if (primedLhs.isDefined) {
        in + ModuleError("Primed assignments are not allowed in procedural code", primedLhs.get.position)
      } else {
        in
      }
    } else {
      if (seqLhs.isDefined) {
        in + ModuleError("Sequential assignment not allowed outside procedures", seqLhs.get.position)
      } else {
        in
      }
    }
  }

  override def applyOnOperatorApp(d : TraversalDirection.T, opapp : OperatorApplication, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      in
    } else {
      opapp.op match {
        case GetNextValueOp() =>
          val arg1 = opapp.operands(0)
          val err1 = arg1 match {
            case id : Identifier => in
            case _ => in + ModuleError("Invalid application of prime operator", arg1.position)
          }
          if (context.environment == ProceduralEnvironment) {
            err1 + ModuleError("Primed variables can't be referenced in procedural code".format(opapp.toString()), opapp.position)
          } else {
            err1
          }
        case _ =>
          in
      }
    }
  }
  override def applyOnStatement(d : TraversalDirection.T, st : Statement, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      in
    } else {
      def checkParallelConstruct(name : String) : T = {
        if (context.environment == SequentialEnvironment) {
          in
        } else {
          in + ModuleError("Parallel construct %s cannot be used in procedural code".format(name), st.position)
        }
      }
      st match {
        case IfElseStmt(_, _, _) | ForStmt(_, _, _, _) | WhileStmt(_, _, _) |
             CaseStmt(_) | ProcedureCallStmt(_, _, _) | SkipStmt() |
             AssertStmt(_, _) | AssumeStmt(_, _) | HavocStmt(_) | BlockStmt(_, _) => 
          in
        case ModuleCallStmt(_) =>
          checkParallelConstruct("next")
        case AssignStmt(lhss, rhss) =>
          checkLhs(lhss, in, context)
      }
    }
  }

  override def applyOnProcedureCall(d : TraversalDirection.T, callStmt : ProcedureCallStmt, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Down) {
      in
    } else {
      checkLhs(callStmt.callLhss, in, context)
    }
  }
}

class PrimedAssignmentChecker extends ASTAnalyzer("PrimedAssignmentChecker", new PrimedAssignmentCheckerPass())  {
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, Set.empty[ModuleError], context)
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}