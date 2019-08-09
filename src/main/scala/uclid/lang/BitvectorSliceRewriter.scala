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
 * Author : Pramod Subramanyan
 *
 * This file contains AST passes that compute the width of bitvector slice operations.
 *
 * To see why this is required, consider the following code:
 *
 *   for i in range(0, 3)  {
 *     call (sum[i:i], cout[i+1:i+1]) := full_adder(a[i:i], b[i:i], cout[i:i]);
 *   }
 *
 * To typecheck this code, we need to be able to determine that each of the bitvector slice operations
 * (sum[i:i], cout[i+1:i+1], a[i:i], b[i:i] and c[i:i]) are all of width 1. At the time we are parsing
 * the code and constructing the AST we do not know this fact. Therefore, these slice operations are
 * represented using VarBitVectorSlice nodes in the AST.
 *
 * The class BitVectorSliceFindWidthPass computes the width of VarBitVectorSlice nodes using the SMT solver.
 *
 * The class BitVectorSliceConstifyPass replaces VarBitVectorSlice nodes with ConstBitVectorSlice nodes
 * where possible if the SMT solver is able to prove that a particular node is a constant. Returning
 * to the above example, it bcomes possible to "constify" the slices after we unroll the for loop.
 *
 */

package uclid
package lang

import uclid.smt.{Converter => Converter}
import uclid.smt.{ExpressionAnalyzer => ExpressionAnalyzer}

class BitVectorSliceFindWidthPass extends RewritePass {
  def rewriteSlice(slice : VarBitVectorSlice, ctx : Scope) : VarBitVectorSlice = {
    val hiP = ReplacePolymorphicOperators.rewrite(slice.hi, IntegerType())
    val loP = ReplacePolymorphicOperators.rewrite(slice.lo, IntegerType())
    val hiExp = Converter.exprToSMT(hiP, ctx)
    val loExp = Converter.exprToSMT(loP, ctx)
    val subExp = smt.OperatorApplication(smt.IntSubOp, List(hiExp, loExp))
    val widthExpr = smt.OperatorApplication(smt.IntAddOp, List(subExp, smt.IntLit(1)))
    val width = ExpressionAnalyzer.getConstIntValue(widthExpr, ctx)
    VarBitVectorSlice(hiP, loP, width)
  }

  override def rewriteBitVectorSlice(slice : BitVectorSlice, ctx : Scope) : Option[BitVectorSlice] = {
    slice match {
      case varBvSlice : VarBitVectorSlice => Some(rewriteSlice(varBvSlice, ctx))
      case _ => Some(slice)
    }
  }
}

class BitVectorSliceFindWidth extends ASTRewriter(
    "BitVectorSliceFindWidth", new BitVectorSliceFindWidthPass())


class BitVectorSliceConstifyPass extends RewritePass {
  def rewriteSlice(slice : VarBitVectorSlice, ctx : Scope) : Some[BitVectorSlice] = {
    slice.width match {
      case None => Some(slice)
      case Some(w) =>
        val hiExp = Converter.exprToSMT(slice.hi, ctx)
        val loExp = Converter.exprToSMT(slice.lo, ctx)
        val hiInt = ExpressionAnalyzer.getConstIntValue(hiExp, ctx)
        val loInt = ExpressionAnalyzer.getConstIntValue(loExp, ctx)
        (hiInt, loInt) match {
          case (Some(hi), Some(lo)) =>
            Some(ConstBitVectorSlice(hi, lo))
          case _ =>
            Some(slice)
        }
    }
  }

  override def rewriteBitVectorSlice(slice : BitVectorSlice, ctx : Scope) : Option[BitVectorSlice] = {
    slice match {
      case varBvSlice : VarBitVectorSlice => rewriteSlice(varBvSlice, ctx)
      case _ => Some(slice)
    }
  }
}

class BitVectorSliceConstify extends ASTRewriter(
    "BitVectorSliceConstify", new BitVectorSliceConstifyPass())
