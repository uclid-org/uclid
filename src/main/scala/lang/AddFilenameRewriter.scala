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
  override def rewriteLocalVar(lvar : LocalVarDecl, ctx : Scope) : Option[LocalVarDecl] = {
    lvar.filename = filename
    Some(lvar)
  }
  override def rewriteStatement(st : Statement, ctx : Scope) : List[Statement] = {
    st.filename = filename
    List(st)
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

  def setFilename(fn: String) {
    pass.asInstanceOf[AddFilenamePass].filename = Some(fn)
  }
}
