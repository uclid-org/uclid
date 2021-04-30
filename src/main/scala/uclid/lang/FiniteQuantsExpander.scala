/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2021 The Regents of the University of California
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
 * Author: Yatin Manerkar
 *
 * Class to expand finite quantifiers in UCLID ASTs.
 *
 */

package uclid
package lang

class FiniteQuantsExpanderPass() extends RewritePass {
  def expandFiniteQuant(id : Identifier, gId : Identifier, ctx : Scope, operands : List[Expr], isForall : Boolean) : Option[Expr] =
  {
    def flattenQuant(exprs : List[Expr], isForall : Boolean) : Expr =
    {
      if (isForall)
      {
          exprs.foldLeft[Expr](BoolLit(true))((a, b) => Operator.and(a, b))
      }
      else
      {
          exprs.foldLeft[Expr](BoolLit(false))((a, b) => Operator.or(a, b))
      }
    }

    def replaceWithGroupElem(id : Identifier, elem : Expr, ctx : Scope, operand : Expr) : Expr =
    {
      val rewriteMap : Map[Expr, Expr] = Map(id -> elem)
      val exprRewriter = new ExprRewriter("FiniteQuantRewriter", rewriteMap)
      val result = exprRewriter.visitExpr(operand, ctx)
      if(result.isEmpty)
      {
        throw new Utils.RuntimeError(
            "Grounding finite quantifier %s with %s in %s results in a null expression??".format(id.toString, elem.toString, operand.toString))
      }
      else
      {
        result.get
      }
    }
  
    def expandFiniteQuantInner(id : Identifier, elems : List[Expr], ctx : Scope, operand : Expr, isForall : Boolean) : Expr =
    {
      flattenQuant(elems.map(replaceWithGroupElem(id, _, ctx, operand)), isForall)
    }

    //We should only be grounding a quantifier over a single expression, or something is seriously amiss.
    assert(operands.length == 1);

    //Get the elements of the group.
    ctx.map.get(gId) match {
      case Some(Scope.Group(_, _, elems)) =>
        Some(flattenQuant(operands.map(expandFiniteQuantInner(id, elems, ctx, _, isForall)), isForall))
      case _ => throw new Utils.RuntimeError("Could not find group %s".format(gId.toString))
    }
  }

  override def rewriteOperatorApp(opapp : OperatorApplication, ctx : Scope) : Option[Expr] =
  {
    opapp match
    {
        case OperatorApplication(op, operands) =>
            op match
            {
                case FiniteForallOp(id, gId) =>
                    expandFiniteQuant(id, gId, ctx, operands, true)
                case FiniteExistsOp(id, gId) =>
                    expandFiniteQuant(id, gId, ctx, operands, false)
                case _ =>
                    Some(opapp)
            }
    }
  }
}

class FiniteQuantsExpander extends ASTRewriter(
    "FiniteQuantsExpander", new FiniteQuantsExpanderPass())
