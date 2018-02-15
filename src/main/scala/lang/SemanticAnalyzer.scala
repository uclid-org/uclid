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
 * Authors: Rohit Sinha, Pramod Subramanyan
 *
 * Walks through the module looking for semantic errors.
 */
package uclid;
package lang;

case class ModuleError(msg : String, position : ASTPosition)

object SemanticAnalyzerPass {
  def checkIdRedeclaration(idSeq : Seq[(Identifier, ASTPosition)], in : List[ModuleError]) : List[ModuleError] = {
    val init = (Map.empty[Identifier, ASTPosition], in)
    (idSeq.foldLeft(init){
      (acc, id) => {
        acc._1.get(id._1) match {
          case Some(pos) =>
            val msg = "Redeclaration of identifier '" + id._1.name + "'. Previous declaration at " + pos.toString
            (acc._1, ModuleError(msg, id._2) :: acc._2)
          case None =>
            ((acc._1 + (id._1 -> id._2)), acc._2)
        }
      }
    })._2
  }
}

class SemanticAnalyzerPass extends ReadOnlyPass[List[ModuleError]] {
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      // val moduleIds = module.decls.filter((d) => d.declNames.isDefined).map((d) => (d.declName.get, d.position))
      val moduleIds = module.decls.flatMap((d) => d.declNames.map((n) => (n, d.position)))
      SemanticAnalyzerPass.checkIdRedeclaration(moduleIds, in)
    } else { in }
  }
  override def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      val inParams = proc.sig.inParams.map((arg) => (arg._1, arg._1.position))
      val outParams = proc.sig.outParams.map((arg) => (arg._1, arg._1.position))
      val localVars = proc.decls.map((v) => (v.id, v.position))
      SemanticAnalyzerPass.checkIdRedeclaration(inParams ++ outParams ++ localVars, in)
    } else { in }
  }
  override def applyOnFunction(d : TraversalDirection.T, func : FunctionDecl, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      val params = func.sig.args.map((arg) => (arg._1, arg._1.position))
      SemanticAnalyzerPass.checkIdRedeclaration(params, in)
    } else { in }
  }
  override def applyOnAssign(d : TraversalDirection.T, stmt : AssignStmt, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      if (stmt.lhss.size != stmt.rhss.size) {
        val msg = "Number of left and right hand sides on assignement statement don't match"
        ModuleError(msg, stmt.position) :: in
      } else { in }
    } else { in }
  }
  override def applyOnRecordType(d : TraversalDirection.T, recordT : RecordType, in : List[ModuleError], context : Scope) : List[ModuleError] = {
    if (d == TraversalDirection.Down) {
      val fieldNames = recordT.members.map((f) => (f._1, f._1.position))
      SemanticAnalyzerPass.checkIdRedeclaration(fieldNames, in)
    } else {
      in
    }
  }
}

class SemanticAnalyzer extends ASTAnalyzer("SemanticAnalyzer", new SemanticAnalyzerPass())  {
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, List.empty[ModuleError], context)
    if (out.size > 0) {
      val errors = out.map((me) => (me.msg, me.position))
      throw new Utils.ParserErrorList(errors)
    }
    return Some(module)
  }
}
