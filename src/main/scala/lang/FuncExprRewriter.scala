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
 * Rewrite old(x) and history(x, i) into the old and history operators.
 *
 */

package uclid
package lang

class FuncExprRewriterPass extends RewritePass {
  override def rewriteFuncApp(fapp : FuncApplication, ctx : Scope) : Option[Expr] = {
    val exprP = fapp.e match {
      case Identifier(fnName) =>
        if (fnName == "old") {
          OperatorApplication(OldOperator(), fapp.args)
        } else if (fnName == "history") {
          OperatorApplication(HistoryOperator(), fapp.args)
        } else if (fnName == "past") {
          OperatorApplication(PastOperator(), fapp.args)
        } else if (fnName == "distinct") {
          OperatorApplication(DistinctOp(), fapp.args)
        } else if (fnName == "bv_sign_extend") {
          if (fapp.args.size == 2) {
            fapp.args(0) match {
              case IntLit(v) =>
                OperatorApplication(BVSignExtOp(0, v.toInt), List(fapp.args(1)))
              case _ =>
                OperatorApplication(BVSignExtOp(0, 0), List(fapp.args(1)))
            }
          } else {
            OperatorApplication(BVSignExtOp(0, 0), List.empty)
          }
        } else if (fnName == "bv_zero_extend") {
          if (fapp.args.size == 2) {
            fapp.args(0) match {
              case IntLit(v) =>
                OperatorApplication(BVZeroExtOp(0, v.toInt), List(fapp.args(1)))
              case _ =>
                OperatorApplication(BVZeroExtOp(0, 0), List(fapp.args(1)))
            }
          } else {
            OperatorApplication(BVZeroExtOp(0, 0), List.empty)
          }
        } else if (fnName == "bv_left_shift") {
          if (fapp.args.size == 2) {
            fapp.args(0) match {
              case IntLit(v) =>
                OperatorApplication(BVLeftShiftIntOp(0, v.toInt), List(fapp.args(1)))
              case _ =>
                OperatorApplication(BVLeftShiftBVOp(0), List(fapp.args(1), fapp.args(0)))
            }
          } else {
            OperatorApplication(BVLeftShiftIntOp(0, 0), List.empty)
          }


        } else if (fnName == "bv_l_right_shift") {
          if (fapp.args.size == 2) {
            fapp.args(0) match {
              case IntLit(v) =>
                OperatorApplication(BVLRightShiftIntOp(0, v.toInt), List(fapp.args(1)))
              case _ =>
                OperatorApplication(BVLRightShiftBVOp(0), List(fapp.args(1), fapp.args(0)))
            }
          } else {
            OperatorApplication(BVLRightShiftIntOp(0, 0), List.empty)
          }


        } else if (fnName == "bv_a_right_shift") {
          if (fapp.args.size == 2) {
            fapp.args(0) match {
              case IntLit(v) =>
                OperatorApplication(BVARightShiftIntOp(0, v.toInt), List(fapp.args(1)))
              case _ =>
                OperatorApplication(BVARightShiftBVOp(0), List(fapp.args(1), fapp.args(0)))
            }
          } else {
            OperatorApplication(BVARightShiftIntOp(0, 0), List.empty)
          }


        } else {
          fapp
        }
      case _ => fapp
    }
    Some(exprP)
  }
}

class FuncExprRewriter extends ASTRewriter("OldExprRewriter", new FuncExprRewriterPass())
