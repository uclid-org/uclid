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
 * The CaseEliminatorPass eliminate case statements from the AST and replaces
 * them with ifs.
 *
 */
package uclid
package lang

import scala.collection.mutable.{Set => MutableSet}
import scala.collection.immutable.Map
import com.typesafe.scalalogging.Logger

class ConstantLitRewriterPass extends RewritePass {
  lazy val logger = Logger(classOf[ConstantLitRewriterPass])
  override def rewriteExpr(expr : Expr, context : Scope) : Option[Expr] = {
    expr match {
      case id : Identifier =>
        context.map.get(id) match {
          case Some(Scope.ConstantLit(id, lit)) => Some(lit)
          case _ => Some(id)
        }
      case _ => Some(expr)
    }
  }
  override def rewriteExternalIdentifier(eId : ExternalIdentifier, context : Scope) : Option[Expr] = {
    logger.debug("eId: " + eId.toString())
    val mId = eId.moduleId
    val fId = eId.id
    context.typeOf(mId) match {
      case Some(moduleType : ModuleType) =>
        moduleType.constLitMap.get(fId) match {
          case Some(lit) => Some(lit)
          case _ => Some(eId)
        }
      case _ =>
        Some(eId)
    }
  }
}

class ConstantLitRewriter extends ASTRewriter(
    "ConstantLitRewriter", new ConstantLitRewriterPass())
