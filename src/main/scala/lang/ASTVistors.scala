package uclid
package lang

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.immutable.{Map => ImmutableMap}


/* AST visitor that walks through the AST and collects information. */
trait FoldingASTVisitor[T] {
  def applyOnModule(module : UclModule, in : T) : T = { in }
  def applyOnDecl(decl : UclDecl, in : T) : T = { in }
  def applyOnProcedure(proc : UclProcedureDecl, in : T) : T = { in }
  def applyOnFunction(func : UclFunctionDecl, in : T) : T = { in }
  def applyOnStateVar(stvar : UclStateVarDecl, in : T) : T = { in }
  def applyOnInputVar(inpvar : UclInputVarDecl, in : T) : T = { in }
  def applyOnOutputVar(outvar : UclOutputVarDecl, in : T) : T = { in }
  def applyOnConstant(cnst : UclConstantDecl, in : T) : T = { in }
  def applyOnSpec(spec : UclSpecDecl, in : T) : T = { in }
  def applyOnTypeDecl(typDec : UclTypeDecl, in : T) : T = { in }
  def applyOnInit(init : UclInitDecl, in : T) : T = { in }
  def applyOnNext(next : UclNextDecl, in : T) : T = { in }
  def applyOnType(typ: Type, in : T) : T = { in }
  def applyOnProcedureSig(sig : UclProcedureSig, in : T) : T = { in }
  def applyOnFunctionSig(sig : UclFunctionSig, in : T) : T = { in }
  def applyOnLocalVar(lvar : UclLocalVarDecl, in : T) : T = { in }
  def applyOnStatement(st : UclStatement, in : T) : T = { in }
  def applyOnSkip(st : UclSkipStmt, in : T) : T = { in }
  def applyOnAssert(st : UclAssertStmt, in : T) : T = { in }
  def applyOnAssume(st : UclAssumeStmt, in : T) : T = { in }
  def applyOnHavoc(st : UclHavocStmt, in : T) : T = { in }
  def applyOnAssign(st : UclAssignStmt, in : T) : T = { in }
  def applyOnIfElse(st : UclIfElseStmt, in : T) : T = { in }
  def applyOnFor(st : UclForStmt, in : T) : T = { in }
  def applyOnCase(st : UclCaseStmt, in : T) : T = { in }
  def applyOnProcedureCall(st : UclProcedureCallStmt, in : T) : T = { in }
  def applyOnLHS(lhs : UclLhs, in : T) : T = { in }
  def applyOnExpr(e : Expr, in : T) : T = { in }
  def applyOnIdentifier(id : Identifier, in : T) : T = { in }
  def applyOnLit(lit : Literal, in : T) : T = { in }
  def applyOnBoolLit(b : BoolLit, in : T) : T = { in }
  def applyOnIntLit(i : IntLit, in : T) : T = { in }
  def applyOnBitVectorLit(bv : BitVectorLit, in : T) : T = { in }
  def applyOnRecord(rec : Record, in : T) : T = { in }
  def applyOnOperatorApp(opapp : UclOperatorApplication, in : T) : T = { in }
  def applyOnOperator(op : Operator, in : T) : T = { in }
  def applyOnArraySelect(arrSel : UclArraySelectOperation, in : T) : T = { in }
  def applyOnArrayStore(arrStore : UclArrayStoreOperation, in : T) : T = { in }
  def applyOnFuncApp(fapp : UclFuncApplication, in : T) : T = { in }
  def applyOnITE(ite : UclITE, in : T) : T = { in }
  def applyOnLambda(lambda : UclLambda, in : T) : T = { in }
  def applyOnCmd(cmd : UclCmd, in : T) : T = { in }
}

class FoldingVisitor[T] (v: FoldingASTVisitor[T], depthFirst: Boolean) {
  def visitModule(module : UclModule, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnModule(module, result)
    result = visitIdentifier(module.id, result)
    result = module.decls.foldLeft(result)((acc, i) => visitDecl(i, acc))
    result = module.cmds.foldLeft(result)((acc, i) => visitCmd(i, acc))
    if(depthFirst) result = v.applyOnModule(module, result)
    return result
  }
  def visitDecl(decl : UclDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnDecl(decl, result)
    result = decl match {
      case UclProcedureDecl(id, sig, vars, body) => visitProcedure(decl.asInstanceOf[UclProcedureDecl], result)
      case UclTypeDecl(id, typ) => visitTypeDecl(decl.asInstanceOf[UclTypeDecl], result)
      case UclStateVarDecl(id, typ) => visitStateVar(decl.asInstanceOf[UclStateVarDecl], result)
      case UclInputVarDecl(id, typ) => visitInputVar(decl.asInstanceOf[UclInputVarDecl], result)
      case UclOutputVarDecl(id, typ) => visitOutputVar(decl.asInstanceOf[UclOutputVarDecl], result)
      case UclConstantDecl(id, typ) => visitConstant(decl.asInstanceOf[UclConstantDecl], result)
      case UclFunctionDecl(id, sig) => visitFunction(decl.asInstanceOf[UclFunctionDecl], result)
      case UclInitDecl(body) => visitInit(decl.asInstanceOf[UclInitDecl], result)
      case UclNextDecl(body) => visitNext(decl.asInstanceOf[UclNextDecl], result)
      case UclSpecDecl(id, expr) => visitSpec(decl.asInstanceOf[UclSpecDecl], result)
    }
    if(depthFirst) result = v.applyOnDecl(decl, result)
    return result
  }
  def visitProcedure(proc : UclProcedureDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnProcedure(proc, result)
    result = visitIdentifier(proc.id, result)
    result = visitProcedureSig(proc.sig, result)
    result = proc.decls.foldLeft(result)((acc, i) => visitLocalVar(i, acc))
    result = proc.body.foldLeft(result)((acc, i) => visitStatement(i, acc))
    if(depthFirst) result = v.applyOnProcedure(proc, result)
    return result
  }
  def visitFunction(func : UclFunctionDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnFunction(func, result)
    result = visitIdentifier(func.id, result)
    result = visitFunctionSig(func.sig, result)
    if(depthFirst) result = v.applyOnFunction(func, result)
    return result
  }
  def visitStateVar(stvar : UclStateVarDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnStateVar(stvar, result)
    result = visitIdentifier(stvar.id, result)
    result = visitType(stvar.typ, result)
    if(depthFirst) result = v.applyOnStateVar(stvar, result)
    return result
  }
  def visitInputVar(inpvar : UclInputVarDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnInputVar(inpvar, result)
    result = visitIdentifier(inpvar.id, result)
    result = visitType(inpvar.typ, result)
    if(depthFirst) result = v.applyOnInputVar(inpvar, result)
    return result
  }
  def visitOutputVar(outvar : UclOutputVarDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnOutputVar(outvar, result)
    result = visitIdentifier(outvar.id, result)
    result = visitType(outvar.typ, result)
    if(depthFirst) result = v.applyOnOutputVar(outvar, result)
    return result
  }
  def visitConstant(cnst : UclConstantDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnConstant(cnst, result)
    result = visitIdentifier(cnst.id, result)
    result = visitType(cnst.typ, result)
    if(depthFirst) result = v.applyOnConstant(cnst, result)
    return result
  }
  def visitSpec(spec : UclSpecDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnSpec(spec, result)
    result = visitIdentifier(spec.id, result)
    result = visitExpr(spec.expr, result)
    if(depthFirst) result = v.applyOnSpec(spec, result)
    return result
  }
  def visitTypeDecl(typDec : UclTypeDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnTypeDecl(typDec, result)
    result = visitIdentifier(typDec.id, result)
    result = visitType(typDec.typ, result)
    if(depthFirst) result = v.applyOnTypeDecl(typDec, result)
    return result
  }
  def visitInit(init : UclInitDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnInit(init, result)
    result = init.body.foldLeft(result)((acc, i) => visitStatement(i, acc))
    if(depthFirst) result = v.applyOnInit(init, result)
    return result
  }
  def visitNext(next : UclNextDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnNext(next, result)
    result = next.body.foldLeft(result)((acc, i) => visitStatement(i, acc))
    if(depthFirst) result = v.applyOnNext(next, result)
    return result
  }
  def visitCmd(cmd : UclCmd, in : T) : T = {
    val result : T = in
    return v.applyOnCmd(cmd, result)
  }

  def visitType(typ: Type, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnType(typ, result)
    if(depthFirst) result = v.applyOnType(typ, result)
    return result
  }

  def visitProcedureSig(sig : UclProcedureSig, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnProcedureSig(sig, result)
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitIdentifier(inparam._1, acc))
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitType(inparam._2, acc))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitIdentifier(outparam._1, acc))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitType(outparam._2, acc))
    if(depthFirst) result = v.applyOnProcedureSig(sig, result)
    return result
  }
  def visitFunctionSig(sig : UclFunctionSig, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnFunctionSig(sig, result)
    result = sig.args.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc))
    result = sig.args.foldLeft(result)((acc, arg) => visitType(arg._2, acc))
    result = visitType(sig.retType, result)
    if(depthFirst) result = v.applyOnFunctionSig(sig, result)
    return result
  }
  def visitLocalVar(lvar : UclLocalVarDecl, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnLocalVar(lvar, result)
    if(depthFirst) result = v.applyOnLocalVar(lvar, result)
    return result
  }
  def visitStatement(st : UclStatement, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnStatement(st, result)
    result = st match {
      case UclSkipStmt() => visitSkipStatement(st.asInstanceOf[UclSkipStmt], result)
      case UclAssertStmt(e) => visitAssertStatement(st.asInstanceOf[UclAssertStmt], result)
      case UclAssumeStmt(e) => visitAssumeStatement(st.asInstanceOf[UclAssumeStmt], result)
      case UclHavocStmt(id) => visitHavocStatement(st.asInstanceOf[UclHavocStmt], result)
      case UclAssignStmt(lhss, rhss) => visitAssignStatement(st.asInstanceOf[UclAssignStmt], result)
      case UclIfElseStmt(cond, ifblock, elseblock) => visitIfElseStatement(st.asInstanceOf[UclIfElseStmt], result)
      case UclForStmt(id, range, body) => visitForStatement(st.asInstanceOf[UclForStmt], result)
      case UclCaseStmt(body) => visitCaseStatement(st.asInstanceOf[UclCaseStmt], result)
      case UclProcedureCallStmt(id, callLhss, args) => visitProcedureCallStatement(st.asInstanceOf[UclProcedureCallStmt], result)
    }
    if(depthFirst) result = v.applyOnStatement(st, result)
    return result
  }

  def visitSkipStatement(st : UclSkipStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnSkip(st, result)
    if(depthFirst) result = v.applyOnSkip(st, result)
    return result
  }
  def visitAssertStatement(st : UclAssertStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnAssert(st, result)
    result = visitExpr(st.e, result)
    if(depthFirst) result = v.applyOnAssert(st, result)
    return result
  }
  def visitAssumeStatement(st : UclAssumeStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnAssume(st, result)
    result = visitExpr(st.e, result)
    if(depthFirst) result = v.applyOnAssume(st, result)
    return result
  }
  def visitHavocStatement(st: UclHavocStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnHavoc(st, result)
    result = visitIdentifier(st.id, result)
    if(depthFirst) result = v.applyOnHavoc(st, result)
    return result
  }
  def visitAssignStatement(st : UclAssignStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnAssign(st, result)
    result = st.lhss.foldLeft(result)((arg, i) => visitLhs(i, arg))
    result = st.rhss.foldLeft(result)((arg, i) => visitExpr(i, arg))
    if(depthFirst) result = v.applyOnAssign(st, result)
    return result
  }
  def visitIfElseStatement(st : UclIfElseStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnIfElse(st, result)
    result = visitExpr(st.cond, result)
    result = st.ifblock.foldLeft(result)((arg, i) => visitStatement(i, arg))
    result = st.elseblock.foldLeft(result)((arg, i) => visitStatement(i, arg))
    if(depthFirst) result = v.applyOnIfElse(st, result)
    return result
  }
  def visitForStatement(st : UclForStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnFor(st, result)
    result = visitIdentifier(st.id, result)
    result = visitLiteral(st.range._1, result)
    result = visitLiteral(st.range._2, result)
    result = st.body.foldLeft(result)((arg, i) => visitStatement(i, arg))
    if(depthFirst) result = v.applyOnFor(st, result)
    return result
  }
  def visitCaseStatement(st : UclCaseStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnCase(st, result)
    result = st.body.foldLeft(result)(
      (arg, cases) => {
        cases._2.foldLeft(visitExpr(cases._1, arg))((arg, i) => visitStatement(i, arg))
      }
    )
    if(depthFirst) result = v.applyOnCase(st, result)
    return result
  }
  def visitProcedureCallStatement(st : UclProcedureCallStmt, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnProcedureCall(st, result)
    result = visitIdentifier(st.id, result)
    result = st.callLhss.foldLeft(result)((arg, i) => visitLhs(i, arg))
    result = st.args.foldLeft(result)((arg, i) => visitExpr(i, arg))
    if(depthFirst) result = v.applyOnProcedureCall(st, result)
    return result
  }
  def visitLhs(lhs : UclLhs, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnLHS(lhs, result)
    result = lhs.arraySelect match {
      case Some(as) => as.foldLeft(result)((acc, i) => visitExpr(i, acc))
      case None => result
    }
    result = lhs.recordSelect match {
      case Some(rs) => rs.foldLeft(result)((acc, i) => visitIdentifier(i, acc))
      case None => result
    }
    if(depthFirst) result = v.applyOnLHS(lhs, result)
    return result
  }
  def visitExpr(e : Expr, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnExpr(e, result)
    result = e match {
      case i : Identifier => visitIdentifier(i, result)
      case lit : Literal => visitLiteral(lit, result)
      case rec : Record => visitRecord(rec, result)
      case opapp : UclOperatorApplication => visitOperatorApp(opapp, result)
      case arrSel : UclArraySelectOperation => visitArraySelectOp(arrSel, result)
      case arrUpd : UclArrayStoreOperation => visitArrayStoreOp(arrUpd, result)
      case fapp : UclFuncApplication => visitFuncApp(fapp, result)
      case ite : UclITE => visitITE(ite, result)
      case lambda : UclLambda => visitLambda(lambda, result)
    }
    if(depthFirst) result = v.applyOnExpr(e, result)
    return result
  }
  def visitIdentifier(id : Identifier, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnIdentifier(id, result)
    if(depthFirst) result = v.applyOnIdentifier(id, result)
    return result
  }
  def visitLiteral(lit : Literal, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnLit(lit, result)
    result = lit match {
      case BoolLit(b) => visitBoolLiteral(lit.asInstanceOf[BoolLit], result)
      case IntLit(i) => visitIntLiteral(lit.asInstanceOf[IntLit], result)
      case BitVectorLit(bv, w) => visitBitVectorLiteral(lit.asInstanceOf[BitVectorLit], result)
    }
    if(depthFirst) result = v.applyOnLit(lit, result)
    return result
  }
  def visitBoolLiteral(b : BoolLit, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnBoolLit(b, result)
    if(depthFirst) result = v.applyOnBoolLit(b, result)
    return result
  }
  def visitIntLiteral(i : IntLit, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnIntLit(i, result)
    if(depthFirst) result = v.applyOnIntLit(i, result)
    return result
  }
  def visitBitVectorLiteral(bv : BitVectorLit, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnBitVectorLit(bv, result)
    if(depthFirst) result = v.applyOnBitVectorLit(bv, result)
    return result
  }
  def visitRecord(rec : Record, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnRecord(rec, result)
    result = rec.value.foldLeft(result)((acc, i) => visitExpr(i, acc))
    if(depthFirst) result = v.applyOnRecord(rec, result)
    return result
  }
  def visitOperatorApp(opapp : UclOperatorApplication, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnOperatorApp(opapp, result)
    result = visitOperator(opapp.op, result)
    result = opapp.operands.foldLeft(result)((acc, i) => visitExpr(i, acc))
    if(depthFirst) result = v.applyOnOperatorApp(opapp, result)
    return result
  }
  def visitOperator(op : Operator, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnOperator(op, result)
    if(depthFirst) result = v.applyOnOperator(op, result)
    return result
  }
  def visitArraySelectOp(arrSel : UclArraySelectOperation, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnArraySelect(arrSel, result)
    result = visitExpr(arrSel.e, result)
    result = arrSel.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc))
    if(depthFirst) result = v.applyOnArraySelect(arrSel, result)
    return result
  }
  def visitArrayStoreOp(arrStore : UclArrayStoreOperation, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnArrayStore(arrStore, result)
    result = visitExpr(arrStore.e, result)
    result = arrStore.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc))
    result = visitExpr(arrStore.value, result)
    if(depthFirst) result = v.applyOnArrayStore(arrStore, result)
    return result
  }
  def visitFuncApp(fapp : UclFuncApplication, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnFuncApp(fapp, result)
    result = visitExpr(fapp.e, result)
    result = fapp.args.foldLeft(result)((acc, arg) => visitExpr(arg, acc))
    if(depthFirst) result = v.applyOnFuncApp(fapp, result)
    return result
  }
  def visitITE(ite: UclITE, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnITE(ite, result)
    result = visitExpr(ite.e, result)
    result = visitExpr(ite.t, result)
    result = visitExpr(ite.f, result)
    if(depthFirst) result = v.applyOnITE(ite, result)
    return result
  }
  def visitLambda(lambda: UclLambda, in : T) : T = {
    var result : T = in
    if(!depthFirst) result = v.applyOnLambda(lambda, result)
    result = lambda.ids.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc))
    result = lambda.ids.foldLeft(result)((acc, arg) => visitType(arg._2, acc))
    result = visitExpr(lambda.e, result)
    if(depthFirst) result = v.applyOnLambda(lambda, result)
    return result
  }
}

/* AST Visitor that rewrites and generates a new AST. */

trait RewritingASTVisitor {
  def rewriteModule(module : UclModule) : Option[UclModule] = { Some(module) }
  def rewriteDecl(decl : UclDecl) : Option[UclDecl] = { Some(decl) }
  def rewriteCommand(cmd : UclCmd) : Option[UclCmd] = { Some(cmd) }
  def rewriteProcedure(proc : UclProcedureDecl) : Option[UclProcedureDecl] = { Some(proc) }
  def rewriteFunction(func : UclFunctionDecl) : Option[UclFunctionDecl] = { Some(func) }
  def rewriteStateVar(stvar : UclStateVarDecl) : Option[UclStateVarDecl] = { Some(stvar) }
  def rewriteInputVar(inpvar : UclInputVarDecl) : Option[UclInputVarDecl] = { Some(inpvar) }
  def rewriteOutputVar(outvar : UclOutputVarDecl) : Option[UclOutputVarDecl] = { Some(outvar) }
  def rewriteConstant(cnst : UclConstantDecl) : Option[UclConstantDecl] = { Some(cnst) }
  def rewriteSpec(spec : UclSpecDecl) : Option[UclSpecDecl] = { Some(spec) }
  def rewriteTypeDecl(typDec : UclTypeDecl) : Option[UclTypeDecl] = { Some(typDec) }
  def rewriteInit(init : UclInitDecl) : Option[UclInitDecl] = { Some(init) }
  def rewriteNext(next : UclNextDecl) : Option[UclNextDecl] = { Some(next) }
  def rewriteType(typ: Type) : Option[Type] = { Some(typ) }
  def rewriteProcedureSig(sig : UclProcedureSig) : Option[UclProcedureSig] = { Some(sig) }
  def rewriteFunctionSig(sig : UclFunctionSig) : Option[UclFunctionSig] = { Some(sig) }
  def rewriteLocalVar(lvar : UclLocalVarDecl) : Option[UclLocalVarDecl] = { Some(lvar) }
  def rewriteStatement(st : UclStatement) : Option[UclStatement] = { Some(st) }
  def rewriteSkip(st : UclSkipStmt) : Option[UclSkipStmt] = { Some(st) }
  def rewriteAssert(st : UclAssertStmt) : Option[UclAssertStmt] = { Some(st) }
  def rewriteAssume(st : UclAssumeStmt) : Option[UclAssumeStmt] = { Some(st) }
  def rewriteHavoc(st : UclHavocStmt) : Option[UclHavocStmt] = { Some(st) }
  def rewriteAssign(st : UclAssignStmt) : Option[UclAssignStmt] = { Some(st) }
  def rewriteIfElse(st : UclIfElseStmt) : Option[UclIfElseStmt] = { Some(st) }
  def rewriteFor(st : UclForStmt) : Option[UclForStmt] = { Some(st) }
  def rewriteCase(st : UclCaseStmt) : Option[UclCaseStmt] = { Some(st) }
  def rewriteProcedureCall(st : UclProcedureCallStmt) : Option[UclProcedureCallStmt] = { Some(st) }
  def rewriteLHS(lhs : UclLhs) : Option[UclLhs] = { Some(lhs) }
  def rewriteExpr(e : Expr) : Option[Expr] = { Some(e) }
  def rewriteIdentifier(id : Identifier) : Option[Identifier] = { Some(id) }
  def rewriteLit(lit : Literal) : Option[Literal] = { Some(lit) }
  def rewriteBoolLit(b : BoolLit) : Option[BoolLit] = { Some(b) }
  def rewriteIntLit(i : IntLit) : Option[IntLit] = { Some(i) }
  def rewriteBitVectorLit(bv : BitVectorLit) : Option[BitVectorLit] = { Some(bv) }
  def rewriteRecord(rec : Record) : Option[Record] = { Some(rec) }
  def rewriteOperatorApp(opapp : UclOperatorApplication) : Option[UclOperatorApplication] = { Some(opapp) }
  def rewriteOperator(op : Operator) : Option[Operator] = { Some(op) }
  def rewriteArraySelect(arrSel : UclArraySelectOperation) : Option[UclArraySelectOperation] = { Some(arrSel) }
  def rewriteArrayStore(arrStore : UclArrayStoreOperation) : Option[UclArrayStoreOperation] = { Some(arrStore) }
  def rewriteFuncApp(fapp : UclFuncApplication) : Option[UclFuncApplication] = { Some(fapp) }
  def rewriteITE(ite : UclITE) : Option[UclITE] = { Some(ite) }
  def rewriteLambda(lambda : UclLambda) : Option[UclLambda] = { Some(lambda) }
}


class RewritingVisitor (v: RewritingASTVisitor) {
  def visitModule(module : UclModule) : Option[UclModule] = {
    val id = visitIdentifier(module.id)
    val decls = module.decls.map(visitDecl(_)).flatten
    val cmds = module.cmds.map(visitCommand(_)).flatten
    return id.flatMap((i) => v.rewriteModule(UclModule(i, decls, cmds)))
  }
  
  def visitDecl(decl : UclDecl) : Option[UclDecl] = {
    return (decl match {
      case procDecl : UclProcedureDecl => visitProcedure(procDecl)
      case typeDecl : UclTypeDecl => visitTypeDecl(typeDecl)
      case stateVar : UclStateVarDecl => visitStateVar(stateVar)
      case inputVar : UclInputVarDecl => visitInputVar(inputVar)
      case outputVar : UclOutputVarDecl => visitOutputVar(outputVar)
      case constDecl : UclConstantDecl => visitConstant(constDecl)
      case funcDecl : UclFunctionDecl => visitFunction(funcDecl)
      case initDecl : UclInitDecl => visitInit(initDecl)
      case nextDecl : UclNextDecl => visitNext(nextDecl)
      case specDecl : UclSpecDecl => visitSpec(specDecl)
    }).flatMap(v.rewriteDecl(_))
  }
  def visitProcedure(proc : UclProcedureDecl) : Option[UclProcedureDecl] = {
    val id = visitIdentifier(proc.id)
    val sig = visitProcedureSig(proc.sig)
    val decls = proc.decls.map(visitLocalVar(_)).flatten
    val stmts = proc.body.map(visitStatement(_)).flatten
    (id, sig) match {
      case (Some(i), Some(s)) => v.rewriteProcedure(UclProcedureDecl(i, s, decls, stmts))
      case _ => None 
    }
  }
  
  def visitFunction(func : UclFunctionDecl) : Option[UclFunctionDecl] = {
    val id = visitIdentifier(func.id)
    val sig = visitFunctionSig(func.sig)
    (id, sig) match {
      case (Some(i), Some(s)) => v.rewriteFunction(UclFunctionDecl(i, s))
      case _ => None
    }
  }
  
  def visitStateVar(stvar : UclStateVarDecl) : Option[UclStateVarDecl] = {
    val idP = visitIdentifier(stvar.id)
    val typP = visitType(stvar.typ)
    (idP, typP) match {
      case (Some(id), Some(typ)) => v.rewriteStateVar(UclStateVarDecl(id, typ))
      case _ => None
    }
  }
  
  def visitInputVar(inpvar : UclInputVarDecl) : Option[UclInputVarDecl] = {
    val idP = visitIdentifier(inpvar.id)
    var typP = visitType(inpvar.typ)
    (idP, typP) match {
      case (Some(id), Some(typ)) => v.rewriteInputVar(UclInputVarDecl(id, typ))
      case _ => None
    }
  }
  
  def visitOutputVar(outvar : UclOutputVarDecl) : Option[UclOutputVarDecl] = {
    val idP = visitIdentifier(outvar.id)
    val typP = visitType(outvar.typ)
    (idP, typP) match {
      case (Some(id), Some(typ)) => v.rewriteOutputVar(UclOutputVarDecl(id, typ))
      case _ => None
    }
  }
  
  def visitConstant(cnst : UclConstantDecl) : Option[UclConstantDecl] = {
    val idP = visitIdentifier(cnst.id)
    val typP = visitType(cnst.typ)
    (idP, typP) match {
      case (Some(id), Some(typ)) => v.rewriteConstant(UclConstantDecl(id, typ))
      case _ => None
    }
  }
  
  def visitSpec(spec : UclSpecDecl) : Option[UclSpecDecl] = {
    val idP = visitIdentifier(spec.id)
    val exprP = visitExpr(spec.expr)
    (idP, exprP) match {
      case (Some(id), Some(expr)) => v.rewriteSpec(UclSpecDecl(id, expr))
      case _ => None
    }
  }
  
  def visitTypeDecl(typDec : UclTypeDecl) : Option[UclTypeDecl] = {
    val idP = visitIdentifier(typDec.id)
    val typeP = visitType(typDec.typ)
    (idP, typeP) match {
      case (Some(id), Some(typ)) => v.rewriteTypeDecl(UclTypeDecl(id, typ))
      case _ => None
    }
  }
  
  def visitInit(init : UclInitDecl) : Option[UclInitDecl] = {
    val body = init.body.map(visitStatement(_)).flatten
    return v.rewriteInit(UclInitDecl(body))
  }
  
  def visitNext(next : UclNextDecl) : Option[UclNextDecl] = {
    val body = next.body.map(visitStatement(_)).flatten
    return v.rewriteNext(UclNextDecl(body))
  }
  
  def visitCommand(cmd : UclCmd) : Option[UclCmd] = {
    return v.rewriteCommand(cmd)
  }
  
  def visitType(typ: Type) : Option[Type] = {
    return v.rewriteType(typ)
  }

  def visitProcedureSig(sig : UclProcedureSig) : Option[UclProcedureSig] = {
    val inParamsP : List[(Identifier, Type)] = sig.inParams.map((inP) => {
      (visitIdentifier(inP._1), visitType(inP._2)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    
    val outParamsP : List[(Identifier, Type)] = sig.outParams.map((outP) => {
      (visitIdentifier(outP._1), visitType(outP._2)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    
    return (inParamsP, outParamsP) match {
      case (in, out) => v.rewriteProcedureSig(UclProcedureSig(in, out))
      case _ => None
    }
  }
  
  def visitFunctionSig(sig : UclFunctionSig) : Option[UclFunctionSig] = {
    val args : List[(Identifier, Type)] = sig.args.map((inP) => {
      (visitIdentifier(inP._1), visitType(inP._2)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    return visitType(sig.retType).flatMap((t) => v.rewriteFunctionSig(UclFunctionSig(args, t)))
  }
  
  def visitLocalVar(lvar : UclLocalVarDecl) : Option[UclLocalVarDecl] = {
    visitIdentifier(lvar.id).flatMap((id) => {
      visitType(lvar.typ).flatMap((t) => v.rewriteLocalVar(UclLocalVarDecl(id, t)))
    })
  }
  
  def visitStatement(st : UclStatement) : Option[UclStatement] = {
    return (st match {
      case skipStmt : UclSkipStmt => visitSkipStatement(skipStmt)
      case assertStmt : UclAssertStmt => visitAssertStatement(assertStmt)
      case assumeStmt : UclAssumeStmt => visitAssumeStatement(assumeStmt)
      case havocStmt : UclHavocStmt => visitHavocStatement(havocStmt)
      case assignStmt : UclAssignStmt => visitAssignStatement(assignStmt)
      case ifElseStmt : UclIfElseStmt => visitIfElseStatement(ifElseStmt)
      case forStmt : UclForStmt => visitForStatement(forStmt)
      case caseStmt : UclCaseStmt => visitCaseStatement(caseStmt)
      case procCallStmt : UclProcedureCallStmt => visitProcedureCallStatement(procCallStmt)
    }).flatMap(v.rewriteStatement(_))
  }

  def visitSkipStatement(st : UclSkipStmt) : Option[UclSkipStmt] = {
    return v.rewriteSkip(st)
  }
  
  def visitAssertStatement(st : UclAssertStmt) : Option[UclAssertStmt] = {
    return v.rewriteAssert(st)
  }
  
  def visitAssumeStatement(st : UclAssumeStmt) : Option[UclAssumeStmt] = {
    return v.rewriteAssume(st)
  }
  
  def visitHavocStatement(st: UclHavocStmt) : Option[UclHavocStmt] = {
    return v.rewriteHavoc(st)
  }
  
  def visitAssignStatement(st : UclAssignStmt) : Option[UclAssignStmt] = {
    return v.rewriteAssign(st)
  }
  
  def visitIfElseStatement(st : UclIfElseStmt) : Option[UclIfElseStmt] = {
    return v.rewriteIfElse(st)
  }
  
  def visitForStatement(st : UclForStmt) : Option[UclForStmt] = {
    val idP = visitIdentifier(st.id)
    val lit1P = visitIntLiteral(st.range._1)
    val lit2P = visitIntLiteral(st.range._2)
    val stmts = st.body.map(visitStatement(_)).flatten
    
    return (idP, lit1P, lit2P) match {
      case (Some(id), Some(lit1), Some(lit2)) => v.rewriteFor(UclForStmt(id, (lit1, lit2), stmts))
      case _ => None
    }
  }
  
  def visitCaseStatement(st : UclCaseStmt) : Option[UclCaseStmt] = {
    val bodyP = st.body.map((c) => {
      // if rewriting the expression doesn't produce None.
      visitExpr(c._1).flatMap((e) => {
        // then rewrite each of statements associated with the case expression.
        Some(e, c._2.map(visitStatement(_)).flatten)
      })
    }).flatten // and finally get rid of all the Options.
    return v.rewriteCase(UclCaseStmt(bodyP))
  }
  
  def visitProcedureCallStatement(st : UclProcedureCallStmt) : Option[UclProcedureCallStmt] = {
    val idP = visitIdentifier(st.id)
    val lhssP = st.callLhss.map(visitLhs(_)).flatten
    val argsP = st.args.map(visitExpr(_)).flatten
    idP.flatMap((id) => v.rewriteProcedureCall(UclProcedureCallStmt(id, lhssP, argsP)))
  }
  
  def visitLhs(lhs : UclLhs) : Option[UclLhs] = {
    val idP = visitIdentifier(lhs.id)
    val arraySelectP = lhs.arraySelect.flatMap((as) => Some(as.map((e) => visitExpr(e)).flatten))
    val recordSelectP = lhs.recordSelect.flatMap((rs) => Some(rs.map((i) => visitIdentifier(i)).flatten))
    idP.flatMap((id) => {
      Some(UclLhs(id, arraySelectP, recordSelectP))
    })
  }
  
  def visitExpr(e : Expr) : Option[Expr] = {
    return (e match {
      case i : Identifier => visitIdentifier(i)
      case lit : Literal => visitLiteral(lit)
      case rec : Record => visitRecord(rec)
      case opapp : UclOperatorApplication => visitOperatorApp(opapp)
      case arrSel : UclArraySelectOperation => visitArraySelectOp(arrSel)
      case arrUpd : UclArrayStoreOperation => visitArrayStoreOp(arrUpd)
      case fapp : UclFuncApplication => visitFuncApp(fapp)
      case ite : UclITE => visitITE(ite)
      case lambda : UclLambda => visitLambda(lambda)
    }).flatMap(visitExpr(_))
  }
  
  def visitIdentifier(id : Identifier) : Option[Identifier] = {
    return v.rewriteIdentifier(id)
  }
  
  def visitLiteral(lit : Literal) : Option[Literal] = {
    return (lit match {
      case b : BoolLit => visitBoolLiteral(b)
      case i : IntLit => visitIntLiteral(i)
      case bv : BitVectorLit => visitBitVectorLiteral(bv)
    }).flatMap(v.rewriteLit(_))
  }
  
  def visitBoolLiteral(b : BoolLit) : Option[BoolLit] = {
    return v.rewriteBoolLit(b)
  }
  
  def visitIntLiteral(i : IntLit) : Option[IntLit] = {
    return v.rewriteIntLit(i)
  }
  
  def visitBitVectorLiteral(bv : BitVectorLit) : Option[BitVectorLit] = {
    return v.rewriteBitVectorLit(bv)
  }
  
  def visitRecord(rec : Record) : Option[Record] = {
    v.rewriteRecord(Record(rec.value.map(visitExpr(_)).flatten))
  }
  
  def visitOperatorApp(opapp : UclOperatorApplication) : Option[UclOperatorApplication] = {
    return visitOperator(opapp.op).flatMap((op) => {
      v.rewriteOperatorApp(UclOperatorApplication(op, opapp.operands.map(visitExpr(_)).flatten))
    })
  }
  
  def visitOperator(op : Operator) : Option[Operator] = {
    return v.rewriteOperator(op)
  }
  
  def visitArraySelectOp(arrSel : UclArraySelectOperation) : Option[UclArraySelectOperation] = {
    return visitExpr(arrSel.e) match {
      case Some(e) => v.rewriteArraySelect(UclArraySelectOperation(e, arrSel.index.map(visitExpr(_)).flatten))
      case _ => None
    }
  }
  
  def visitArrayStoreOp(arrStore : UclArrayStoreOperation) : Option[UclArrayStoreOperation] = {
    val eP = visitExpr(arrStore.e)
    val ind = arrStore.index.map(visitExpr(_)).flatten
    val valP = visitExpr(arrStore.value)
    return (eP, valP) match {
      case (Some(e), Some(value)) => v.rewriteArrayStore(UclArrayStoreOperation(e, ind, value))
      case _ => None
    }
  }
  
  def visitFuncApp(fapp : UclFuncApplication) : Option[UclFuncApplication] = {
    val eP = visitExpr(fapp.e)
    val args = fapp.args.map(visitExpr(_)).flatten
    eP match {
      case Some(e) => v.rewriteFuncApp(UclFuncApplication(e, args))
      case _ => None
    }
  }
  
  def visitITE(ite: UclITE) : Option[UclITE] = {
    val condP = visitExpr(ite.e)
    val tP = visitExpr(ite.t)
    val fP = visitExpr(ite.f)
    
    (condP, tP, fP) match {
      case (Some(cond), Some(t), Some(f)) => v.rewriteITE(UclITE(cond, t, f))
      case _ => None
    }
  }
  
  def visitLambda(lambda: UclLambda) : Option[UclLambda] = {
    val idP = lambda.ids.map((arg) => {
      (visitIdentifier(arg._1), visitType(arg._2)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    return visitExpr(lambda.e).flatMap((e) => v.rewriteLambda(UclLambda(idP, e)))
  }
}

class TypingVisitor extends FoldingASTVisitor[Unit]
{
  type Context = ImmutableMap[Identifier, Type]
  type MemoKey = (Expr, Context)
  type Memo = MutableMap[MemoKey, Type]
  var memo : Memo = MutableMap.empty[MemoKey, Type]
  var context = ImmutableMap.empty[Identifier, Type]
  
  override def applyOnExpr(e : Expr, in : Unit) : Unit = {
    typeOf(e, context)
  }
  
  def typeOf(e : Expr, c : Context) : Type = {
    def opAppType(opapp : UclOperatorApplication) : Type = {
      val argTypes = opapp.operands.map(typeOf(_, c))
      opapp.op match {
        case polyOp : PolymorphicOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes(0) == argTypes(1), "Arguments to operator '" + opapp.op.toString + "' must be of the same type.")
          Utils.assert(argTypes.forall(_.isNumeric), "Arguments to operator '" + opapp.op.toString + "' must be of a numeric type.")
          typeOf(opapp.operands(0), c)
        }
        case intOp : IntArgOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[IntType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Integer.")
          new IntType()
        }
        case bvOp : BVArgOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.")
          typeOf(opapp.operands(0), c)
        }
        case boolOp : BooleanOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[BoolType]), "Arguments to operator '" + opapp.op.toString + "' must be of type Bool.")
          new BoolType()
        }
        case cmpOp : ComparisonOperator => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes(0) == argTypes(1), "Arguments to operator '" + opapp.op.toString + "' must be of the same type.")
          new BoolType()
        }
        case tOp : TemporalOperator => new TemporalType()
        case ExtractOp(hi, lo) => {
          Utils.assert(argTypes.size == 1, "Operator '" + opapp.op.toString + "' must have one argument.")
          Utils.assert(argTypes(0).isInstanceOf[BitVectorType], "Operand to operator '" + opapp.op.toString + "' must be of type BitVector.") 
          Utils.assert(argTypes(0).asInstanceOf[BitVectorType].width > hi.value.toInt, "Operand to operator '" + opapp.op.toString + "' must have width > "  + hi.value.toString + ".") 
          Utils.assert(hi.value >= lo.value , "High-operand must be greater than or equal to low operand for operator '" + opapp.op.toString + "'.") 
          Utils.assert(hi.value.toInt >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.") 
          Utils.assert(lo.value.toInt >= 0, "Operand to operator '" + opapp.op.toString + "' must be non-negative.") 
          new BitVectorType(hi.value.toInt - lo.value.toInt + 1)
        }
        case ConcatOp() => {
          Utils.assert(argTypes.size == 2, "Operator '" + opapp.op.toString + "' must have two arguments.")
          Utils.assert(argTypes.forall(_.isInstanceOf[BitVectorType]), "Arguments to operator '" + opapp.op.toString + "' must be of type BitVector.")
          new BitVectorType(argTypes(0).asInstanceOf[BitVectorType].width + argTypes(1).asInstanceOf[BitVectorType].width)
        }
        case RecordSelect(field) => {
          Utils.assert(argTypes.size == 1, "Record select operator must have exactly one operand.")
          Utils.assert(argTypes(0).isInstanceOf[RecordType], "Argument to record select operator must be of type record.")
          val recordType = argTypes(0).asInstanceOf[RecordType]
          val typOption = recordType.fieldType(field)
          Utils.assert(!typOption.isEmpty, "Field '" + field.toString + "' does not exist in record.")
          return typOption.get
        }
      }
    }
    
    def arraySelectType(arrSel : UclArraySelectOperation) : Type = {
      Utils.assert(typeOf(arrSel.e, c).isInstanceOf[ArrayType], "Type error in the array operand of select operation.")
      val indTypes = arrSel.index.map(typeOf(_, c))
      val arrayType = typeOf(arrSel.e, c).asInstanceOf[ArrayType]
      Utils.assert(arrayType.inTypes == indTypes, "Array index type error.")
      return arrayType.outType
    }
    
    def arrayStoreType(arrStore : UclArrayStoreOperation) : Type = {
      Utils.assert(typeOf(arrStore.e, c).isInstanceOf[ArrayType], "Type error in the array operand of store operation.")
      val indTypes = arrStore.index.map(typeOf(_, c))
      val valueType = typeOf(arrStore.value, c)
      val arrayType = typeOf(arrStore.e, c).asInstanceOf[ArrayType]
      Utils.assert(arrayType.inTypes == indTypes, "Array index type error.")
      Utils.assert(arrayType.outType == valueType, "Array update value type error.")
      return arrayType
    }
    
    def funcAppType(fapp : UclFuncApplication) : Type = {
      Utils.assert(typeOf(fapp.e, c).isInstanceOf[MapType], "Type error in function application (not a function).")
      val funcType = typeOf(fapp.e,c ).asInstanceOf[MapType]
      val argTypes = fapp.args.map(typeOf(_, c))
      Utils.assert(funcType.inTypes == argTypes, "Type error in function application (argument type error).")
      return funcType.outType
    }
    
    def iteType(ite : UclITE) : Type = {
      Utils.assert(typeOf(ite.e, c).isBool, "Type error in ITE condition operand.")
      Utils.assert(typeOf(ite.t, c) == typeOf(ite.f, c), "ITE operand types don't match.")
      return typeOf(ite.t, c)
    }
    
    def lambdaType(lambda : UclLambda) : Type = {
      return MapType(lambda.ids.map(_._2), typeOf(lambda.e, c))
    }
    
    val cachedType = memo.get((e,c))
    if (cachedType.isEmpty) {
      val typ = e match {
        case i : Identifier => (c.get(i).get)
        case b : BoolLit => new BoolType()
        case i : IntLit => new IntType()
        case bv : BitVectorLit => new BitVectorType(bv.width)
        case r : Record => throw new Utils.UnimplementedException("Need to implement anonymous record types.")
        case opapp : UclOperatorApplication => opAppType(opapp)
        case arrSel : UclArraySelectOperation => arraySelectType(arrSel)
        case arrStore : UclArrayStoreOperation => arrayStoreType(arrStore)
        case fapp : UclFuncApplication => funcAppType(fapp)
        case ite : UclITE => iteType(ite)
        case lambda : UclLambda => lambdaType(lambda)
      }
      memo.put((e,c), typ)
      return typ
    } else {
      return cachedType.get
    }
  }
  
}