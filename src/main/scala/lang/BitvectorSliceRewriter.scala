package uclid
package lang

import uclid.smt.{Converter => Converter}
import uclid.smt.{ExpressionAnalyzer => ExpressionAnalyzer}

class BitVectorSliceFindWidthPass extends RewritePass {
  def rewriteSlice(slice : VarBitVectorSlice, ctx : ScopeMap) : VarBitVectorSlice = {
    val hiP = ReplacePolymorphicOperators.rewrite(slice.hi, IntType())
    val loP = ReplacePolymorphicOperators.rewrite(slice.lo, IntType())
    val hiExp = Converter.exprToSMT(hiP, ctx)
    val loExp = Converter.exprToSMT(loP, ctx)
    val subExp = smt.OperatorApplication(smt.IntSubOp, List(hiExp, loExp))
    val widthExpr = smt.OperatorApplication(smt.IntAddOp, List(subExp, smt.IntLit(1)))
    val width = ExpressionAnalyzer.getConstIntValue(widthExpr, ctx)
    VarBitVectorSlice(hiP, loP, width)
  }

  override def rewriteBitVectorSlice(slice : BitVectorSlice, ctx : ScopeMap) : Option[BitVectorSlice] = {
    slice match {
      case varBvSlice : VarBitVectorSlice => Some(rewriteSlice(varBvSlice, ctx))
      case _ => Some(slice)
    }
  }
}

class BitVectorSliceFindWidth extends ASTRewriter(
    "BitVectorSliceFindWidth", new BitVectorSliceFindWidthPass())


class BitVectorSliceConstifyPass extends RewritePass {
  def rewriteSlice(slice : VarBitVectorSlice, ctx : ScopeMap) : Some[BitVectorSlice] = {
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

  override def rewriteBitVectorSlice(slice : BitVectorSlice, ctx : ScopeMap) : Option[BitVectorSlice] = {
    slice match {
      case varBvSlice : VarBitVectorSlice => rewriteSlice(varBvSlice, ctx)
      case _ => Some(slice)
    }
  }
}

class BitVectorSliceConstify extends ASTRewriter(
    "BitVectorSliceConstify", new BitVectorSliceConstifyPass())