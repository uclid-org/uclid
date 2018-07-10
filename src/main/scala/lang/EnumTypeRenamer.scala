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
 * The EnumTypeRenamerPass eliminate case statements from the AST and replaces
 * them with ifs.
 *
 */
package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.immutable.Map

class EnumTypeRenamerPass extends RewritePass {
  var enumNumericMap : MutableMap[Identifier, BigInt] = MutableMap.empty
  var enumType : MutableMap[Identifier, Type] = MutableMap.empty

  def enumBVWidth(typ : Type) : Int = {
  	math.ceil(math.log(typ.ids.size.toDouble)/math.log(2.0)).toInt
  }

  def replaceEnumMembers(e : Expr, ctx : Scope) : Option[Expr] = {
    if (!e.isInstanceOf[Identifier]) return Some(e)

    val eId = e.asInstanceOf[Identifier]
    val typ = ctx.typeOf(eId).get
    typ match {
      case EnumType(_) => {
        // Store original type
        enumType = enumType + (eId -> typ)
        // Add enum type with new mapping
        var enumRename : BigInt = BigInt(-1)
        if (!enumNumericMap.exists(_._1 == typ.ids(0))) {
          enumNumericMap = typ.ids.foldLeft(enumNumericMap) {
            (accMap, member) => {
              enumRename = enumRename + 1
              accMap + (member -> enumRename)
            }
          }
        }
        if (!enumNumericMap.exists(_._1 == eId)) return Some(e)
        Some(BitVectorLit(enumNumericMap(eId), enumBVWidth(typ)))
      }
      case _ => Some(e)
    }
  }

  def enumTypeToNumericType(typ : Type) : Option[Type] = {
    typ match {
      case EnumType(_) =>
        val width = enumBVWidth(typ)
        val retTyp = lang.BitVectorType(width)
        Some(retTyp)
      case _ =>
        Some(typ)
    }
  }

  override def rewriteExpr(e : Expr, ctx : Scope) : Option[Expr] = {
  	replaceEnumMembers(e, ctx)
  }

  override def rewriteType(typ: Type, ctx : Scope) : Option[Type] = {
    enumTypeToNumericType(typ)
  }
}

class EnumTypeRenamer extends ASTRewriter("EnumTypeRenamer", new EnumTypeRenamerPass())
