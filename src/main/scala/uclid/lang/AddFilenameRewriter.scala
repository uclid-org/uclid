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
 * Authors: Pramod Subramanyan.
 *
 * AddFilenamePass annotates each AST node in a module with a filename.
 */
package uclid
package lang

class AddFilenamePass(var filename : Option[String]) extends RewritePass {
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    module.filename = filename
    return Some(module)
  }
  override def rewriteDecl(decl : Decl, ctx : Scope) : Option[Decl] = {
    decl.filename = filename
    Some(decl)
  }
  override def rewriteCommand(cmd : GenericProofCommand, ctx : Scope) : Option[GenericProofCommand] = {
    cmd.filename = filename
    Some(cmd)
  }
  override def rewriteProcedureSig(sig : ProcedureSig, ctx : Scope) : Option[ProcedureSig] = {
    sig.filename = filename
    Some(sig)
  }
  override def rewriteFunctionSig(sig : FunctionSig, ctx : Scope) : Option[FunctionSig] = {
    sig.filename = filename
    Some(sig)
  }
  override def rewriteStatement(st : Statement, ctx : Scope) : Option[Statement] = {
    st.filename = filename
    Some(st)
  }
  override def rewriteLHS(lhs : Lhs, ctx : Scope) : Option[Lhs] = {
    lhs.filename = filename
    Some(lhs)
  }
  override def rewriteExpr(e : Expr, ctx : Scope) : Option[Expr] = {
    e.filename = filename
    Some(e)
  }
  override def rewriteIdentifier(id : Identifier, ctx : Scope) : Option[Identifier] = {
    id.filename = filename
    Some(id)
  }
  override def rewriteTuple(rec : Tuple, ctx : Scope) : Option[Tuple] = {
    rec.filename = filename
    Some(rec)
  }
  override def rewriteOperator(op : Operator, ctx : Scope) : Option[Operator] = {
    op.filename = filename
    Some(op)
  }
  override def rewriteExprDecorator(dec : ExprDecorator, ctx : Scope) : Option[ExprDecorator] = {
    dec.filename = filename
    Some(dec)
  }
}

class AddFilenameRewriter(filename : Option[String]) extends ASTRewriter(
    "AddFilenameRewriter", new AddFilenamePass(filename), false)  {

  def setFilename(fn: String): Unit = {
    pass.asInstanceOf[AddFilenamePass].filename = Some(fn)
  }
}
