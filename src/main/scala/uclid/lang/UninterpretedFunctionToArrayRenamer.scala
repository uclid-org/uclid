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
 * Author : Kevin Cheang
 *
 * The UninterpretedFunctionToRenamerPass rewrites all uninterpreted functions as arrays.
 *
 */
package uclid
package lang

class UninterpretedFunctionToArrayRewriterPass extends RewritePass {
  def functionDeclToArrayDecl(funcDecl: FunctionDecl): StateVarsDecl = {
    val id = funcDecl.id
    val inTypes = funcDecl.sig.args.map(kv => kv._2)
    val outType = funcDecl.sig.retType
    StateVarsDecl(List(id), ArrayType(inTypes, outType))
  }

  override def rewriteDecl(decl : Decl, ctx : Scope) : Option[Decl] = {
    decl match {
      case FunctionDecl(_, _) => {
        Some(functionDeclToArrayDecl(decl.asInstanceOf[FunctionDecl]))
      }
      case _ => Some(decl)
    }
  }

  def functionAppToArraySelect(funcApp: FuncApplication): OperatorApplication = {
    val funcId = funcApp.e
    val arraySelectOp = ArraySelect(funcApp.args)
    OperatorApplication(arraySelectOp, List(funcId))
  }

  override def rewriteExpr(e : Expr, ctx : Scope) : Option[Expr] = {
    e match {
      case FuncApplication(_, _) => {
        val funcApp = e.asInstanceOf[FuncApplication]
        ctx.module match {
          case Some(mod) => {
            // If it's the declaration of the function to synthesize, we don't rewrite the expression
            if (mod.synthFunctions.map(sf => sf.id).contains(funcApp.e.asInstanceOf[Identifier])) return Some(e)
            else Some(functionAppToArraySelect(funcApp))
          }
          case None => {
            Some(e)
          }
        }
      }
      case _ => Some(e)
    }
  }

  def mapTypeToArrayType(typ: Type): Type = {
    typ match {
      case MapType(inTypes, outType) => {
        ArrayType(inTypes, outType)
      }
      case _ => typ
    }
  }

  override def rewriteSynthesisFunction(synFunc : SynthesisFunctionDecl, ctx : Scope) : Option[SynthesisFunctionDecl] = {
    val funcSig = synFunc.sig
    val sigP = FunctionSig(funcSig.args.map(kv => (kv._1, mapTypeToArrayType(kv._2))), mapTypeToArrayType(funcSig.retType))
    val synFuncP = SynthesisFunctionDecl(synFunc.id, sigP, synFunc.grammarId, synFunc.grammarArgs, synFunc.conditions)
    Some(synFuncP)
  }
}

class UninterpretedFunctionToArray extends ASTRewriter(
    "UninterpretedFunctionsToArray", new UninterpretedFunctionToArrayRewriterPass())
