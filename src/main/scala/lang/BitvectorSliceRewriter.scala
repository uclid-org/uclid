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
    val hiP = ReplacePolymorphicOperators.rewrite(slice.hi, IntType())
    val loP = ReplacePolymorphicOperators.rewrite(slice.lo, IntType())
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