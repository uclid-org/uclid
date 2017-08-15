package uclid
package lang

object TraversalDirection extends Enumeration {
  type T = Value
  val Up, Down = Value
}


/* AST visitor that walks through the AST and collects information. */
trait FoldingASTVisitor[T] {
  def applyOnModule(d : TraversalDirection.T, module : Module, in : T) : T = { in }
  def applyOnDecl(d : TraversalDirection.T, decl : UclDecl, in : T) : T = { in }
  def applyOnProcedure(d : TraversalDirection.T, proc : UclProcedureDecl, in : T) : T = { in }
  def applyOnFunction(d : TraversalDirection.T, func : UclFunctionDecl, in : T) : T = { in }
  def applyOnStateVar(d : TraversalDirection.T, stvar : UclStateVarDecl, in : T) : T = { in }
  def applyOnInputVar(d : TraversalDirection.T, inpvar : UclInputVarDecl, in : T) : T = { in }
  def applyOnOutputVar(d : TraversalDirection.T, outvar : UclOutputVarDecl, in : T) : T = { in }
  def applyOnConstant(d : TraversalDirection.T, cnst : UclConstantDecl, in : T) : T = { in }
  def applyOnSpec(d : TraversalDirection.T, spec : UclSpecDecl, in : T) : T = { in }
  def applyOnTypeDecl(d : TraversalDirection.T, typDec : UclTypeDecl, in : T) : T = { in }
  def applyOnInit(d : TraversalDirection.T, init : UclInitDecl, in : T) : T = { in }
  def applyOnNext(d : TraversalDirection.T, next : UclNextDecl, in : T) : T = { in }
  def applyOnType(d : TraversalDirection.T, typ: Type, in : T) : T = { in }
  def applyOnProcedureSig(d : TraversalDirection.T, sig : UclProcedureSig, in : T) : T = { in }
  def applyOnFunctionSig(d : TraversalDirection.T, sig : UclFunctionSig, in : T) : T = { in }
  def applyOnLocalVar(d : TraversalDirection.T, lvar : UclLocalVarDecl, in : T) : T = { in }
  def applyOnStatement(d : TraversalDirection.T, st : UclStatement, in : T) : T = { in }
  def applyOnSkip(d : TraversalDirection.T, st : UclSkipStmt, in : T) : T = { in }
  def applyOnAssert(d : TraversalDirection.T, st : UclAssertStmt, in : T) : T = { in }
  def applyOnAssume(d : TraversalDirection.T, st : UclAssumeStmt, in : T) : T = { in }
  def applyOnHavoc(d : TraversalDirection.T, st : UclHavocStmt, in : T) : T = { in }
  def applyOnAssign(d : TraversalDirection.T, st : UclAssignStmt, in : T) : T = { in }
  def applyOnIfElse(d : TraversalDirection.T, st : UclIfElseStmt, in : T) : T = { in }
  def applyOnFor(d : TraversalDirection.T, st : UclForStmt, in : T) : T = { in }
  def applyOnCase(d : TraversalDirection.T, st : UclCaseStmt, in : T) : T = { in }
  def applyOnProcedureCall(d : TraversalDirection.T, st : UclProcedureCallStmt, in : T) : T = { in }
  def applyOnLHS(d : TraversalDirection.T, lhs : UclLhs, in : T) : T = { in }
  def applyOnExpr(d : TraversalDirection.T, e : Expr, in : T) : T = { in }
  def applyOnIdentifier(d : TraversalDirection.T, id : Identifier, in : T) : T = { in }
  def applyOnLit(d : TraversalDirection.T, lit : Literal, in : T) : T = { in }
  def applyOnBoolLit(d : TraversalDirection.T, b : BoolLit, in : T) : T = { in }
  def applyOnIntLit(d : TraversalDirection.T, i : IntLit, in : T) : T = { in }
  def applyOnBitVectorLit(d : TraversalDirection.T, bv : BitVectorLit, in : T) : T = { in }
  def applyOnRecord(d : TraversalDirection.T, rec : Record, in : T) : T = { in }
  def applyOnOperatorApp(d : TraversalDirection.T, opapp : UclOperatorApplication, in : T) : T = { in }
  def applyOnOperator(d : TraversalDirection.T, op : Operator, in : T) : T = { in }
  def applyOnArraySelect(d : TraversalDirection.T, arrSel : UclArraySelectOperation, in : T) : T = { in }
  def applyOnArrayStore(d : TraversalDirection.T, arrStore : UclArrayStoreOperation, in : T) : T = { in }
  def applyOnFuncApp(d : TraversalDirection.T, fapp : UclFuncApplication, in : T) : T = { in }
  def applyOnITE(d : TraversalDirection.T, ite : UclITE, in : T) : T = { in }
  def applyOnLambda(d : TraversalDirection.T, lambda : UclLambda, in : T) : T = { in }
  def applyOnCmd(d : TraversalDirection.T, cmd : UclCmd, in : T) : T = { in }
}

class FoldingVisitor[T] (v: FoldingASTVisitor[T]) {
  def visitModule(module : Module, in : T) : T = {
    var result : T = in
    result = v.applyOnModule(TraversalDirection.Down, module, result)
    result = visitIdentifier(module.id, result)
    result = module.decls.foldLeft(result)((acc, i) => visitDecl(i, acc))
    result = module.cmds.foldLeft(result)((acc, i) => visitCmd(i, acc))
    result = v.applyOnModule(TraversalDirection.Up, module, result)
    return result
  }
  def visitDecl(decl : UclDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnDecl(TraversalDirection.Down, decl, result)
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
    result = v.applyOnDecl(TraversalDirection.Up, decl, result)
    return result
  }
  def visitProcedure(proc : UclProcedureDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnProcedure(TraversalDirection.Down, proc, result)
    result = visitIdentifier(proc.id, result)
    result = visitProcedureSig(proc.sig, result)
    result = proc.decls.foldLeft(result)((acc, i) => visitLocalVar(i, acc))
    result = proc.body.foldLeft(result)((acc, i) => visitStatement(i, acc))
    result = v.applyOnProcedure(TraversalDirection.Up, proc, result)
    return result
  }
  def visitFunction(func : UclFunctionDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnFunction(TraversalDirection.Down, func, result)
    result = visitIdentifier(func.id, result)
    result = visitFunctionSig(func.sig, result)
    result = v.applyOnFunction(TraversalDirection.Up, func, result)
    return result
  }
  def visitStateVar(stvar : UclStateVarDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnStateVar(TraversalDirection.Down, stvar, result)
    result = visitIdentifier(stvar.id, result)
    result = visitType(stvar.typ, result)
    result = v.applyOnStateVar(TraversalDirection.Up, stvar, result)
    return result
  }
  def visitInputVar(inpvar : UclInputVarDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnInputVar(TraversalDirection.Down, inpvar, result)
    result = visitIdentifier(inpvar.id, result)
    result = visitType(inpvar.typ, result)
    result = v.applyOnInputVar(TraversalDirection.Up, inpvar, result)
    return result
  }
  def visitOutputVar(outvar : UclOutputVarDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnOutputVar(TraversalDirection.Down, outvar, result)
    result = visitIdentifier(outvar.id, result)
    result = visitType(outvar.typ, result)
    result = v.applyOnOutputVar(TraversalDirection.Up, outvar, result)
    return result
  }
  def visitConstant(cnst : UclConstantDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnConstant(TraversalDirection.Down, cnst, result)
    result = visitIdentifier(cnst.id, result)
    result = visitType(cnst.typ, result)
    result = v.applyOnConstant(TraversalDirection.Up, cnst, result)
    return result
  }
  def visitSpec(spec : UclSpecDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnSpec(TraversalDirection.Down, spec, result)
    result = visitIdentifier(spec.id, result)
    result = visitExpr(spec.expr, result)
    result = v.applyOnSpec(TraversalDirection.Up, spec, result)
    return result
  }
  def visitTypeDecl(typDec : UclTypeDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnTypeDecl(TraversalDirection.Down, typDec, result)
    result = visitIdentifier(typDec.id, result)
    result = visitType(typDec.typ, result)
    result = v.applyOnTypeDecl(TraversalDirection.Up, typDec, result)
    return result
  }
  def visitInit(init : UclInitDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnInit(TraversalDirection.Down, init, result)
    result = init.body.foldLeft(result)((acc, i) => visitStatement(i, acc))
    result = v.applyOnInit(TraversalDirection.Up, init, result)
    return result
  }
  def visitNext(next : UclNextDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnNext(TraversalDirection.Down, next, result)
    result = next.body.foldLeft(result)((acc, i) => visitStatement(i, acc))
    result = v.applyOnNext(TraversalDirection.Up, next, result)
    return result
  }
  def visitCmd(cmd : UclCmd, in : T) : T = {
    val result : T = in
    return v.applyOnCmd(TraversalDirection.Down, cmd, result)
    return v.applyOnCmd(TraversalDirection.Up, cmd, result)
  }

  def visitType(typ: Type, in : T) : T = {
    var result : T = in
    result = v.applyOnType(TraversalDirection.Down, typ, result)
    result = v.applyOnType(TraversalDirection.Up, typ, result)
    return result
  }

  def visitProcedureSig(sig : UclProcedureSig, in : T) : T = {
    var result : T = in
    result = v.applyOnProcedureSig(TraversalDirection.Down, sig, result)
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitIdentifier(inparam._1, acc))
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitType(inparam._2, acc))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitIdentifier(outparam._1, acc))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitType(outparam._2, acc))
    result = v.applyOnProcedureSig(TraversalDirection.Up, sig, result)
    return result
  }
  def visitFunctionSig(sig : UclFunctionSig, in : T) : T = {
    var result : T = in
    result = v.applyOnFunctionSig(TraversalDirection.Down, sig, result)
    result = sig.args.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc))
    result = sig.args.foldLeft(result)((acc, arg) => visitType(arg._2, acc))
    result = visitType(sig.retType, result)
    result = v.applyOnFunctionSig(TraversalDirection.Up, sig, result)
    return result
  }
  def visitLocalVar(lvar : UclLocalVarDecl, in : T) : T = {
    var result : T = in
    result = v.applyOnLocalVar(TraversalDirection.Down, lvar, result)
    result = v.applyOnLocalVar(TraversalDirection.Up, lvar, result)
    return result
  }
  def visitStatement(st : UclStatement, in : T) : T = {
    var result : T = in
    result = v.applyOnStatement(TraversalDirection.Down, st, result)
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
    result = v.applyOnStatement(TraversalDirection.Up, st, result)
    return result
  }

  def visitSkipStatement(st : UclSkipStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnSkip(TraversalDirection.Down, st, result)
    result = v.applyOnSkip(TraversalDirection.Up, st, result)
    return result
  }
  def visitAssertStatement(st : UclAssertStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnAssert(TraversalDirection.Down, st, result)
    result = visitExpr(st.e, result)
    result = v.applyOnAssert(TraversalDirection.Up, st, result)
    return result
  }
  def visitAssumeStatement(st : UclAssumeStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnAssume(TraversalDirection.Down, st, result)
    result = visitExpr(st.e, result)
    result = v.applyOnAssume(TraversalDirection.Up, st, result)
    return result
  }
  def visitHavocStatement(st: UclHavocStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnHavoc(TraversalDirection.Down, st, result)
    result = visitIdentifier(st.id, result)
    result = v.applyOnHavoc(TraversalDirection.Up, st, result)
    return result
  }
  def visitAssignStatement(st : UclAssignStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnAssign(TraversalDirection.Down, st, result)
    result = st.lhss.foldLeft(result)((arg, i) => visitLhs(i, arg))
    result = st.rhss.foldLeft(result)((arg, i) => visitExpr(i, arg))
    result = v.applyOnAssign(TraversalDirection.Up, st, result)
    return result
  }
  def visitIfElseStatement(st : UclIfElseStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnIfElse(TraversalDirection.Down, st, result)
    result = visitExpr(st.cond, result)
    result = st.ifblock.foldLeft(result)((arg, i) => visitStatement(i, arg))
    result = st.elseblock.foldLeft(result)((arg, i) => visitStatement(i, arg))
    result = v.applyOnIfElse(TraversalDirection.Up, st, result)
    return result
  }
  def visitForStatement(st : UclForStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnFor(TraversalDirection.Down, st, result)
    result = visitIdentifier(st.id, result)
    result = visitLiteral(st.range._1, result)
    result = visitLiteral(st.range._2, result)
    result = st.body.foldLeft(result)((arg, i) => visitStatement(i, arg))
    result = v.applyOnFor(TraversalDirection.Up, st, result)
    return result
  }
  def visitCaseStatement(st : UclCaseStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnCase(TraversalDirection.Down, st, result)
    result = st.body.foldLeft(result)(
      (arg, cases) => {
        cases._2.foldLeft(visitExpr(cases._1, arg))((arg, i) => visitStatement(i, arg))
      }
    )
    result = v.applyOnCase(TraversalDirection.Up, st, result)
    return result
  }
  def visitProcedureCallStatement(st : UclProcedureCallStmt, in : T) : T = {
    var result : T = in
    result = v.applyOnProcedureCall(TraversalDirection.Down, st, result)
    result = visitIdentifier(st.id, result)
    result = st.callLhss.foldLeft(result)((arg, i) => visitLhs(i, arg))
    result = st.args.foldLeft(result)((arg, i) => visitExpr(i, arg))
    result = v.applyOnProcedureCall(TraversalDirection.Up, st, result)
    return result
  }
  def visitLhs(lhs : UclLhs, in : T) : T = {
    var result : T = in
    result = v.applyOnLHS(TraversalDirection.Down, lhs, result)
    result = lhs.arraySelect match {
      case Some(as) => as.foldLeft(result)((acc, i) => visitExpr(i, acc))
      case None => result
    }
    result = lhs.recordSelect match {
      case Some(rs) => rs.foldLeft(result)((acc, i) => visitIdentifier(i, acc))
      case None => result
    }
    result = v.applyOnLHS(TraversalDirection.Up, lhs, result)
    return result
  }
  def visitExpr(e : Expr, in : T) : T = {
    var result : T = in
    result = v.applyOnExpr(TraversalDirection.Down, e, result)
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
    result = v.applyOnExpr(TraversalDirection.Up, e, result)
    return result
  }
  def visitIdentifier(id : Identifier, in : T) : T = {
    var result : T = in
    result = v.applyOnIdentifier(TraversalDirection.Down, id, result)
    result = v.applyOnIdentifier(TraversalDirection.Up, id, result)
    return result
  }
  def visitLiteral(lit : Literal, in : T) : T = {
    var result : T = in
    result = v.applyOnLit(TraversalDirection.Down, lit, result)
    result = lit match {
      case BoolLit(b) => visitBoolLiteral(lit.asInstanceOf[BoolLit], result)
      case IntLit(i) => visitIntLiteral(lit.asInstanceOf[IntLit], result)
      case BitVectorLit(bv, w) => visitBitVectorLiteral(lit.asInstanceOf[BitVectorLit], result)
    }
    result = v.applyOnLit(TraversalDirection.Up, lit, result)
    return result
  }
  def visitBoolLiteral(b : BoolLit, in : T) : T = {
    var result : T = in
    result = v.applyOnBoolLit(TraversalDirection.Down, b, result)
    result = v.applyOnBoolLit(TraversalDirection.Up, b, result)
    return result
  }
  def visitIntLiteral(i : IntLit, in : T) : T = {
    var result : T = in
    result = v.applyOnIntLit(TraversalDirection.Down, i, result)
    result = v.applyOnIntLit(TraversalDirection.Up, i, result)
    return result
  }
  def visitBitVectorLiteral(bv : BitVectorLit, in : T) : T = {
    var result : T = in
    result = v.applyOnBitVectorLit(TraversalDirection.Down, bv, result)
    result = v.applyOnBitVectorLit(TraversalDirection.Up, bv, result)
    return result
  }
  def visitRecord(rec : Record, in : T) : T = {
    var result : T = in
    result = v.applyOnRecord(TraversalDirection.Down, rec, result)
    result = rec.value.foldLeft(result)((acc, i) => visitExpr(i, acc))
    result = v.applyOnRecord(TraversalDirection.Up, rec, result)
    return result
  }
  def visitOperatorApp(opapp : UclOperatorApplication, in : T) : T = {
    var result : T = in
    result = v.applyOnOperatorApp(TraversalDirection.Down, opapp, result)
    result = visitOperator(opapp.op, result)
    result = opapp.operands.foldLeft(result)((acc, i) => visitExpr(i, acc))
    result = v.applyOnOperatorApp(TraversalDirection.Up, opapp, result)
    return result
  }
  def visitOperator(op : Operator, in : T) : T = {
    var result : T = in
    result = v.applyOnOperator(TraversalDirection.Down, op, result)
    result = v.applyOnOperator(TraversalDirection.Up, op, result)
    return result
  }
  def visitArraySelectOp(arrSel : UclArraySelectOperation, in : T) : T = {
    var result : T = in
    result = v.applyOnArraySelect(TraversalDirection.Down, arrSel, result)
    result = visitExpr(arrSel.e, result)
    result = arrSel.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc))
    result = v.applyOnArraySelect(TraversalDirection.Up, arrSel, result)
    return result
  }
  def visitArrayStoreOp(arrStore : UclArrayStoreOperation, in : T) : T = {
    var result : T = in
    result = v.applyOnArrayStore(TraversalDirection.Down, arrStore, result)
    result = visitExpr(arrStore.e, result)
    result = arrStore.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc))
    result = visitExpr(arrStore.value, result)
    result = v.applyOnArrayStore(TraversalDirection.Up, arrStore, result)
    return result
  }
  def visitFuncApp(fapp : UclFuncApplication, in : T) : T = {
    var result : T = in
    result = v.applyOnFuncApp(TraversalDirection.Down, fapp, result)
    result = visitExpr(fapp.e, result)
    result = fapp.args.foldLeft(result)((acc, arg) => visitExpr(arg, acc))
    result = v.applyOnFuncApp(TraversalDirection.Up, fapp, result)
    return result
  }
  def visitITE(ite: UclITE, in : T) : T = {
    var result : T = in
    result = v.applyOnITE(TraversalDirection.Down, ite, result)
    result = visitExpr(ite.e, result)
    result = visitExpr(ite.t, result)
    result = visitExpr(ite.f, result)
    result = v.applyOnITE(TraversalDirection.Up, ite, result)
    return result
  }
  def visitLambda(lambda: UclLambda, in : T) : T = {
    var result : T = in
    result = v.applyOnLambda(TraversalDirection.Down, lambda, result)
    result = lambda.ids.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc))
    result = lambda.ids.foldLeft(result)((acc, arg) => visitType(arg._2, acc))
    result = visitExpr(lambda.e, result)
    result = v.applyOnLambda(TraversalDirection.Up, lambda, result)
    return result
  }
}

/* AST Visitor that rewrites and generates a new AST. */

trait RewritingASTVisitor {
  def visitModule(module : Module) = { }
  def rewriteModule(module : Module) : Option[Module] = { Some(module) }
  def visitDecl(decl : UclDecl) = { }
  def rewriteDecl(decl : UclDecl) : Option[UclDecl] = { Some(decl) }
  def visitCommand(cmd : UclCmd) = { }
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
  def visitModule(module : Module) : Option[Module] = {
    val id = visitIdentifier(module.id)
    val decls = module.decls.map(visitDecl(_)).flatten
    val cmds = module.cmds.map(visitCommand(_)).flatten
    return id.flatMap((i) => v.rewriteModule(Module(i, decls, cmds)))
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
    visitExpr(st.e).flatMap((e) => {
      v.rewriteAssert(UclAssertStmt(e))
    })
  }
  
  def visitAssumeStatement(st : UclAssumeStmt) : Option[UclAssumeStmt] = {
    visitExpr(st.e).flatMap((e) => {
      v.rewriteAssume(UclAssumeStmt(e))
    })
  }
  
  def visitHavocStatement(st: UclHavocStmt) : Option[UclHavocStmt] = {
    visitIdentifier(st.id).flatMap((id) => {
      v.rewriteHavoc(UclHavocStmt(id))
    })
  }
  
  def visitAssignStatement(st : UclAssignStmt) : Option[UclAssignStmt] = {
    val lhss = st.lhss.map(visitLhs(_)).flatten
    val rhss = st.rhss.map(visitExpr(_)).flatten
    return v.rewriteAssign(UclAssignStmt(lhss, rhss))
  }
  
  def visitIfElseStatement(st : UclIfElseStmt) : Option[UclIfElseStmt] = {
    val cond = visitExpr(st.cond)
    val ifblock = st.ifblock.map(visitStatement(_)).flatten
    val elseblock = st.elseblock.map(visitStatement(_)).flatten
    cond match {
      case Some(c) => v.rewriteIfElse(UclIfElseStmt(c, ifblock, elseblock))
      case _ => None
    }
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
    }).flatMap(v.rewriteExpr(_))
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
