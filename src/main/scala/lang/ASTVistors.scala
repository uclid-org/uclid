package uclid
package lang

abstract class ASTAnalysis {
  var _manager : Option[PassManager] = None
  def manager : PassManager = { _manager.get }
  
  def passName : String
  def reset() {}
  def visit (module : Module) : Option[Module]
  def astChanged : Boolean
}

object TraversalDirection extends Enumeration {
  type T = Value
  val Up, Down = Value
}

/* AST visitor that walks through the AST and collects information. */
trait ReadOnlyPass[T] {
  var _analysis : Option[ASTAnalysis] = None
  def analysis : ASTAnalysis = _analysis.get
  def reset() {}
  
  def applyOnModule(d : TraversalDirection.T, module : Module, in : T, context : ScopeMap) : T = { in }
  def applyOnDecl(d : TraversalDirection.T, decl : UclDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnProcedure(d : TraversalDirection.T, proc : UclProcedureDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnFunction(d : TraversalDirection.T, func : UclFunctionDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnStateVar(d : TraversalDirection.T, stvar : UclStateVarDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnInputVar(d : TraversalDirection.T, inpvar : UclInputVarDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnOutputVar(d : TraversalDirection.T, outvar : UclOutputVarDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnConstant(d : TraversalDirection.T, cnst : UclConstantDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnSpec(d : TraversalDirection.T, spec : UclSpecDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnTypeDecl(d : TraversalDirection.T, typDec : UclTypeDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnInit(d : TraversalDirection.T, init : UclInitDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnNext(d : TraversalDirection.T, next : UclNextDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnType(d : TraversalDirection.T, typ: Type, in : T, context : ScopeMap) : T = { in }
  def applyOnProcedureSig(d : TraversalDirection.T, sig : UclProcedureSig, in : T, context : ScopeMap) : T = { in }
  def applyOnFunctionSig(d : TraversalDirection.T, sig : UclFunctionSig, in : T, context : ScopeMap) : T = { in }
  def applyOnLocalVar(d : TraversalDirection.T, lvar : UclLocalVarDecl, in : T, context : ScopeMap) : T = { in }
  def applyOnStatement(d : TraversalDirection.T, st : UclStatement, in : T, context : ScopeMap) : T = { in }
  def applyOnSkip(d : TraversalDirection.T, st : UclSkipStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnAssert(d : TraversalDirection.T, st : UclAssertStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnAssume(d : TraversalDirection.T, st : UclAssumeStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnHavoc(d : TraversalDirection.T, st : UclHavocStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnAssign(d : TraversalDirection.T, st : UclAssignStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnIfElse(d : TraversalDirection.T, st : UclIfElseStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnFor(d : TraversalDirection.T, st : UclForStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnCase(d : TraversalDirection.T, st : UclCaseStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnProcedureCall(d : TraversalDirection.T, st : UclProcedureCallStmt, in : T, context : ScopeMap) : T = { in }
  def applyOnLHS(d : TraversalDirection.T, lhs : UclLhs, in : T, context : ScopeMap) : T = { in }
  def applyOnExpr(d : TraversalDirection.T, e : Expr, in : T, context : ScopeMap) : T = { in }
  def applyOnIdentifier(d : TraversalDirection.T, id : Identifier, in : T, context : ScopeMap) : T = { in }
  def applyOnLit(d : TraversalDirection.T, lit : Literal, in : T, context : ScopeMap) : T = { in }
  def applyOnBoolLit(d : TraversalDirection.T, b : BoolLit, in : T, context : ScopeMap) : T = { in }
  def applyOnIntLit(d : TraversalDirection.T, i : IntLit, in : T, context : ScopeMap) : T = { in }
  def applyOnBitVectorLit(d : TraversalDirection.T, bv : BitVectorLit, in : T, context : ScopeMap) : T = { in }
  def applyOnRecord(d : TraversalDirection.T, rec : Record, in : T, context : ScopeMap) : T = { in }
  def applyOnOperatorApp(d : TraversalDirection.T, opapp : UclOperatorApplication, in : T, context : ScopeMap) : T = { in }
  def applyOnOperator(d : TraversalDirection.T, op : Operator, in : T, context : ScopeMap) : T = { in }
  def applyOnArraySelect(d : TraversalDirection.T, arrSel : UclArraySelectOperation, in : T, context : ScopeMap) : T = { in }
  def applyOnArrayStore(d : TraversalDirection.T, arrStore : UclArrayStoreOperation, in : T, context : ScopeMap) : T = { in }
  def applyOnFuncApp(d : TraversalDirection.T, fapp : UclFuncApplication, in : T, context : ScopeMap) : T = { in }
  def applyOnITE(d : TraversalDirection.T, ite : UclITE, in : T, context : ScopeMap) : T = { in }
  def applyOnLambda(d : TraversalDirection.T, lambda : UclLambda, in : T, context : ScopeMap) : T = { in }
  def applyOnCmd(d : TraversalDirection.T, cmd : UclCmd, in : T, context : ScopeMap) : T = { in }
}

class ASTAnalyzer[T] (_passName : String, _pass: ReadOnlyPass[T]) extends ASTAnalysis {
  // Set a backpointer to the pass from here.
  _pass._analysis = Some(this)

  /** The pass itself. */
  def pass : ReadOnlyPass[T] = _pass
  /** The input/outputs of the pass. */
  private[this] var _in : Option[T] = None
  private[this] var _out : Option[T] = None
  /** The pseudo-variable 'in' sets the input to the analysis. */
  def in : Option[T] = _in
  def in_=(i : Option[T]): Unit = {
    _in = i
    _out = None
  }
  /** out contains the result of the analysis. */
  def out : Option[T] = _out
  /** Name of the pass. */
  override def passName = _passName
  /** The main 'do-er' method. */
  override def visit(module : Module) : Option[Module] = {
    _out = Some(visitModule(module, _in.get))
    return Some(module)
  }
  /** These analyses never change the AST. */
  override def astChanged = false

  // Reset calls reset on the pass.
  override  def reset() = { pass.reset() }
  
  // We now have the code that actually traverses the AST.
  def visitModule(module : Module, in : T) : T = {
    var result : T = in
    val emptyContext = new ScopeMap()
    val context = emptyContext + module

    result = pass.applyOnModule(TraversalDirection.Down, module, result, emptyContext)
    result = visitIdentifier(module.id, result, context)
    result = module.decls.foldLeft(result)((acc, i) => visitDecl(i, acc, context))
    result = module.cmds.foldLeft(result)((acc, i) => visitCmd(i, acc, context))
    result = pass.applyOnModule(TraversalDirection.Up, module, result, emptyContext)
    return result
  }
  def visitDecl(decl : UclDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnDecl(TraversalDirection.Down, decl, result, context)
    result = decl match {
      case UclProcedureDecl(id, sig, vars, body) => visitProcedure(decl.asInstanceOf[UclProcedureDecl], result, context)
      case UclTypeDecl(id, typ) => visitTypeDecl(decl.asInstanceOf[UclTypeDecl], result, context)
      case UclStateVarDecl(id, typ) => visitStateVar(decl.asInstanceOf[UclStateVarDecl], result, context)
      case UclInputVarDecl(id, typ) => visitInputVar(decl.asInstanceOf[UclInputVarDecl], result, context)
      case UclOutputVarDecl(id, typ) => visitOutputVar(decl.asInstanceOf[UclOutputVarDecl], result, context)
      case UclConstantDecl(id, typ) => visitConstant(decl.asInstanceOf[UclConstantDecl], result, context)
      case UclFunctionDecl(id, sig) => visitFunction(decl.asInstanceOf[UclFunctionDecl], result, context)
      case UclInitDecl(body) => visitInit(decl.asInstanceOf[UclInitDecl], result, context)
      case UclNextDecl(body) => visitNext(decl.asInstanceOf[UclNextDecl], result, context)
      case UclSpecDecl(id, expr) => visitSpec(decl.asInstanceOf[UclSpecDecl], result, context)
    }
    result = pass.applyOnDecl(TraversalDirection.Up, decl, result, context)
    return result
  }
  def visitProcedure(proc : UclProcedureDecl, in : T, contextIn : ScopeMap) : T = {
    var result : T = in
    val context = contextIn + proc
    result = pass.applyOnProcedure(TraversalDirection.Down, proc, result, contextIn)
    result = visitIdentifier(proc.id, result, context)
    result = visitProcedureSig(proc.sig, result, context)
    result = proc.decls.foldLeft(result)((acc, i) => visitLocalVar(i, acc, context))
    result = proc.body.foldLeft(result)((acc, i) => visitStatement(i, acc, context))
    result = pass.applyOnProcedure(TraversalDirection.Up, proc, result, contextIn)
    return result
  }
  def visitFunction(func : UclFunctionDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnFunction(TraversalDirection.Down, func, result, context)
    result = visitIdentifier(func.id, result, context)
    result = visitFunctionSig(func.sig, result, context)
    result = pass.applyOnFunction(TraversalDirection.Up, func, result, context)
    return result
  }
  def visitStateVar(stvar : UclStateVarDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnStateVar(TraversalDirection.Down, stvar, result, context)
    result = visitIdentifier(stvar.id, result, context)
    result = visitType(stvar.typ, result, context)
    result = pass.applyOnStateVar(TraversalDirection.Up, stvar, result, context)
    return result
  }
  def visitInputVar(inpvar : UclInputVarDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnInputVar(TraversalDirection.Down, inpvar, result, context)
    result = visitIdentifier(inpvar.id, result, context)
    result = visitType(inpvar.typ, result, context)
    result = pass.applyOnInputVar(TraversalDirection.Up, inpvar, result, context)
    return result
  }
  def visitOutputVar(outvar : UclOutputVarDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnOutputVar(TraversalDirection.Down, outvar, result, context)
    result = visitIdentifier(outvar.id, result, context)
    result = visitType(outvar.typ, result, context)
    result = pass.applyOnOutputVar(TraversalDirection.Up, outvar, result, context)
    return result
  }
  def visitConstant(cnst : UclConstantDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnConstant(TraversalDirection.Down, cnst, result, context)
    result = visitIdentifier(cnst.id, result, context)
    result = visitType(cnst.typ, result, context)
    result = pass.applyOnConstant(TraversalDirection.Up, cnst, result, context)
    return result
  }
  def visitSpec(spec : UclSpecDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnSpec(TraversalDirection.Down, spec, result, context)
    result = visitIdentifier(spec.id, result, context)
    result = visitExpr(spec.expr, result, context)
    result = pass.applyOnSpec(TraversalDirection.Up, spec, result, context)
    return result
  }
  def visitTypeDecl(typDec : UclTypeDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnTypeDecl(TraversalDirection.Down, typDec, result, context)
    result = visitIdentifier(typDec.id, result, context)
    result = visitType(typDec.typ, result, context)
    result = pass.applyOnTypeDecl(TraversalDirection.Up, typDec, result, context)
    return result
  }
  def visitInit(init : UclInitDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnInit(TraversalDirection.Down, init, result, context)
    result = init.body.foldLeft(result)((acc, i) => visitStatement(i, acc, context))
    result = pass.applyOnInit(TraversalDirection.Up, init, result, context)
    return result
  }
  def visitNext(next : UclNextDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnNext(TraversalDirection.Down, next, result, context)
    result = next.body.foldLeft(result)((acc, i) => visitStatement(i, acc, context))
    result = pass.applyOnNext(TraversalDirection.Up, next, result, context)
    return result
  }
  def visitCmd(cmd : UclCmd, in : T, context : ScopeMap) : T = {
    val result : T = in
    return pass.applyOnCmd(TraversalDirection.Down, cmd, result, context)
    return pass.applyOnCmd(TraversalDirection.Up, cmd, result, context)
  }

  def visitType(typ: Type, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnType(TraversalDirection.Down, typ, result, context)
    result = pass.applyOnType(TraversalDirection.Up, typ, result, context)
    return result
  }

  def visitProcedureSig(sig : UclProcedureSig, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnProcedureSig(TraversalDirection.Down, sig, result, context)
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitIdentifier(inparam._1, acc, context))
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitType(inparam._2, acc, context))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitIdentifier(outparam._1, acc, context))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitType(outparam._2, acc, context))
    result = pass.applyOnProcedureSig(TraversalDirection.Up, sig, result, context)
    return result
  }
  def visitFunctionSig(sig : UclFunctionSig, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnFunctionSig(TraversalDirection.Down, sig, result, context)
    result = sig.args.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc, context))
    result = sig.args.foldLeft(result)((acc, arg) => visitType(arg._2, acc, context))
    result = visitType(sig.retType, result, context)
    result = pass.applyOnFunctionSig(TraversalDirection.Up, sig, result, context)
    return result
  }
  def visitLocalVar(lvar : UclLocalVarDecl, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnLocalVar(TraversalDirection.Down, lvar, result, context)
    result = pass.applyOnLocalVar(TraversalDirection.Up, lvar, result, context)
    return result
  }
  def visitStatement(st : UclStatement, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnStatement(TraversalDirection.Down, st, result, context)
    result = st match {
      case UclSkipStmt() => visitSkipStatement(st.asInstanceOf[UclSkipStmt], result, context)
      case UclAssertStmt(e) => visitAssertStatement(st.asInstanceOf[UclAssertStmt], result, context)
      case UclAssumeStmt(e) => visitAssumeStatement(st.asInstanceOf[UclAssumeStmt], result, context)
      case UclHavocStmt(id) => visitHavocStatement(st.asInstanceOf[UclHavocStmt], result, context)
      case UclAssignStmt(lhss, rhss) => visitAssignStatement(st.asInstanceOf[UclAssignStmt], result, context)
      case UclIfElseStmt(cond, ifblock, elseblock) => visitIfElseStatement(st.asInstanceOf[UclIfElseStmt], result, context)
      case UclForStmt(id, range, body) => visitForStatement(st.asInstanceOf[UclForStmt], result, context)
      case UclCaseStmt(body) => visitCaseStatement(st.asInstanceOf[UclCaseStmt], result, context)
      case UclProcedureCallStmt(id, callLhss, args) => visitProcedureCallStatement(st.asInstanceOf[UclProcedureCallStmt], result, context)
    }
    result = pass.applyOnStatement(TraversalDirection.Up, st, result, context)
    return result
  }

  def visitSkipStatement(st : UclSkipStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnSkip(TraversalDirection.Down, st, result, context)
    result = pass.applyOnSkip(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitAssertStatement(st : UclAssertStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnAssert(TraversalDirection.Down, st, result, context)
    result = visitExpr(st.e, result, context)
    result = pass.applyOnAssert(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitAssumeStatement(st : UclAssumeStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnAssume(TraversalDirection.Down, st, result, context)
    result = visitExpr(st.e, result, context)
    result = pass.applyOnAssume(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitHavocStatement(st: UclHavocStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnHavoc(TraversalDirection.Down, st, result, context)
    result = visitIdentifier(st.id, result, context)
    result = pass.applyOnHavoc(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitAssignStatement(st : UclAssignStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnAssign(TraversalDirection.Down, st, result, context)
    result = st.lhss.foldLeft(result)((arg, i) => visitLhs(i, arg, context))
    result = st.rhss.foldLeft(result)((arg, i) => visitExpr(i, arg, context))
    result = pass.applyOnAssign(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitIfElseStatement(st : UclIfElseStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnIfElse(TraversalDirection.Down, st, result, context)
    result = visitExpr(st.cond, result, context)
    result = st.ifblock.foldLeft(result)((arg, i) => visitStatement(i, arg, context))
    result = st.elseblock.foldLeft(result)((arg, i) => visitStatement(i, arg, context))
    result = pass.applyOnIfElse(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitForStatement(st : UclForStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnFor(TraversalDirection.Down, st, result, context)
    result = visitIdentifier(st.id, result, context)
    result = visitLiteral(st.range._1, result, context)
    result = visitLiteral(st.range._2, result, context)
    result = st.body.foldLeft(result)((arg, i) => visitStatement(i, arg, context))
    result = pass.applyOnFor(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitCaseStatement(st : UclCaseStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnCase(TraversalDirection.Down, st, result, context)
    result = st.body.foldLeft(result)(
      (arg, cases) => {
        cases._2.foldLeft(visitExpr(cases._1, arg, context))((arg, i) => visitStatement(i, arg, context))
      }
    )
    result = pass.applyOnCase(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitProcedureCallStatement(st : UclProcedureCallStmt, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnProcedureCall(TraversalDirection.Down, st, result, context)
    result = visitIdentifier(st.id, result, context)
    result = st.callLhss.foldLeft(result)((arg, i) => visitLhs(i, arg, context))
    result = st.args.foldLeft(result)((arg, i) => visitExpr(i, arg, context))
    result = pass.applyOnProcedureCall(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitLhs(lhs : UclLhs, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnLHS(TraversalDirection.Down, lhs, result, context)
    result = lhs.arraySelect match {
      case Some(as) => as.foldLeft(result)((acc, i) => visitExpr(i, acc, context))
      case None => result
    }
    result = lhs.recordSelect match {
      case Some(rs) => rs.foldLeft(result)((acc, i) => visitIdentifier(i, acc, context))
      case None => result
    }
    result = pass.applyOnLHS(TraversalDirection.Up, lhs, result, context)
    return result
  }
  def visitExpr(e : Expr, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnExpr(TraversalDirection.Down, e, result, context)
    result = e match {
      case i : Identifier => visitIdentifier(i, result, context)
      case lit : Literal => visitLiteral(lit, result, context)
      case rec : Record => visitRecord(rec, result, context)
      case opapp : UclOperatorApplication => visitOperatorApp(opapp, result, context)
      case arrSel : UclArraySelectOperation => visitArraySelectOp(arrSel, result, context)
      case arrUpd : UclArrayStoreOperation => visitArrayStoreOp(arrUpd, result, context)
      case fapp : UclFuncApplication => visitFuncApp(fapp, result, context)
      case ite : UclITE => visitITE(ite, result, context)
      case lambda : UclLambda => visitLambda(lambda, result, context)
    }
    result = pass.applyOnExpr(TraversalDirection.Up, e, result, context)
    return result
  }
  def visitIdentifier(id : Identifier, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnIdentifier(TraversalDirection.Down, id, result, context)
    result = pass.applyOnIdentifier(TraversalDirection.Up, id, result, context)
    return result
  }
  def visitLiteral(lit : Literal, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnLit(TraversalDirection.Down, lit, result, context)
    result = lit match {
      case BoolLit(b) => visitBoolLiteral(lit.asInstanceOf[BoolLit], result, context)
      case IntLit(i) => visitIntLiteral(lit.asInstanceOf[IntLit], result, context)
      case BitVectorLit(bv, w) => visitBitVectorLiteral(lit.asInstanceOf[BitVectorLit], result, context)
    }
    result = pass.applyOnLit(TraversalDirection.Up, lit, result, context)
    return result
  }
  def visitBoolLiteral(b : BoolLit, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnBoolLit(TraversalDirection.Down, b, result, context)
    result = pass.applyOnBoolLit(TraversalDirection.Up, b, result, context)
    return result
  }
  def visitIntLiteral(i : IntLit, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnIntLit(TraversalDirection.Down, i, result, context)
    result = pass.applyOnIntLit(TraversalDirection.Up, i, result, context)
    return result
  }
  def visitBitVectorLiteral(bv : BitVectorLit, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnBitVectorLit(TraversalDirection.Down, bv, result, context)
    result = pass.applyOnBitVectorLit(TraversalDirection.Up, bv, result, context)
    return result
  }
  def visitRecord(rec : Record, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnRecord(TraversalDirection.Down, rec, result, context)
    result = rec.value.foldLeft(result)((acc, i) => visitExpr(i, acc, context))
    result = pass.applyOnRecord(TraversalDirection.Up, rec, result, context)
    return result
  }
  def visitOperatorApp(opapp : UclOperatorApplication, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnOperatorApp(TraversalDirection.Down, opapp, result, context)
    result = visitOperator(opapp.op, result, context)
    result = opapp.operands.foldLeft(result)((acc, i) => visitExpr(i, acc, context))
    result = pass.applyOnOperatorApp(TraversalDirection.Up, opapp, result, context)
    return result
  }
  def visitOperator(op : Operator, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnOperator(TraversalDirection.Down, op, result, context)
    result = pass.applyOnOperator(TraversalDirection.Up, op, result, context)
    return result
  }
  def visitArraySelectOp(arrSel : UclArraySelectOperation, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnArraySelect(TraversalDirection.Down, arrSel, result, context)
    result = visitExpr(arrSel.e, result, context)
    result = arrSel.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc, context))
    result = pass.applyOnArraySelect(TraversalDirection.Up, arrSel, result, context)
    return result
  }
  def visitArrayStoreOp(arrStore : UclArrayStoreOperation, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnArrayStore(TraversalDirection.Down, arrStore, result, context)
    result = visitExpr(arrStore.e, result, context)
    result = arrStore.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc, context))
    result = visitExpr(arrStore.value, result, context)
    result = pass.applyOnArrayStore(TraversalDirection.Up, arrStore, result, context)
    return result
  }
  def visitFuncApp(fapp : UclFuncApplication, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnFuncApp(TraversalDirection.Down, fapp, result, context)
    result = visitExpr(fapp.e, result, context)
    result = fapp.args.foldLeft(result)((acc, arg) => visitExpr(arg, acc, context))
    result = pass.applyOnFuncApp(TraversalDirection.Up, fapp, result, context)
    return result
  }
  def visitITE(ite: UclITE, in : T, context : ScopeMap) : T = {
    var result : T = in
    result = pass.applyOnITE(TraversalDirection.Down, ite, result, context)
    result = visitExpr(ite.e, result, context)
    result = visitExpr(ite.t, result, context)
    result = visitExpr(ite.f, result, context)
    result = pass.applyOnITE(TraversalDirection.Up, ite, result, context)
    return result
  }
  def visitLambda(lambda: UclLambda, in : T, contextIn : ScopeMap) : T = {
    var result : T = in
    val context = contextIn + lambda 
    result = pass.applyOnLambda(TraversalDirection.Down, lambda, result, contextIn)
    result = lambda.ids.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc, context))
    result = lambda.ids.foldLeft(result)((acc, arg) => visitType(arg._2, acc, context))
    result = visitExpr(lambda.e, result, context)
    result = pass.applyOnLambda(TraversalDirection.Up, lambda, result, contextIn)
    return result
  }
}

/* AST Visitor that rewrites and generates a new AST. */

trait RewritePass {
  var _analysis : Option[ASTAnalysis] = None
  def analysis : ASTAnalysis = _analysis.get
  def reset() { }
  
  def rewriteModule(module : Module, ctx : ScopeMap) : Option[Module] = { Some(module) }
  def rewriteDecl(decl : UclDecl, ctx : ScopeMap) : Option[UclDecl] = { Some(decl) }
  def rewriteCommand(cmd : UclCmd, ctx : ScopeMap) : Option[UclCmd] = { Some(cmd) }
  def rewriteProcedure(proc : UclProcedureDecl, ctx : ScopeMap) : Option[UclProcedureDecl] = { Some(proc) }
  def rewriteFunction(func : UclFunctionDecl, ctx : ScopeMap) : Option[UclFunctionDecl] = { Some(func) }
  def rewriteStateVar(stvar : UclStateVarDecl, ctx : ScopeMap) : Option[UclStateVarDecl] = { Some(stvar) }
  def rewriteInputVar(inpvar : UclInputVarDecl, ctx : ScopeMap) : Option[UclInputVarDecl] = { Some(inpvar) }
  def rewriteOutputVar(outvar : UclOutputVarDecl, ctx : ScopeMap) : Option[UclOutputVarDecl] = { Some(outvar) }
  def rewriteConstant(cnst : UclConstantDecl, ctx : ScopeMap) : Option[UclConstantDecl] = { Some(cnst) }
  def rewriteSpec(spec : UclSpecDecl, ctx : ScopeMap) : Option[UclSpecDecl] = { Some(spec) }
  def rewriteTypeDecl(typDec : UclTypeDecl, ctx : ScopeMap) : Option[UclTypeDecl] = { Some(typDec) }
  def rewriteInit(init : UclInitDecl, ctx : ScopeMap) : Option[UclInitDecl] = { Some(init) }
  def rewriteNext(next : UclNextDecl, ctx : ScopeMap) : Option[UclNextDecl] = { Some(next) }
  def rewriteType(typ: Type, ctx : ScopeMap) : Option[Type] = { Some(typ) }
  def rewriteProcedureSig(sig : UclProcedureSig, ctx : ScopeMap) : Option[UclProcedureSig] = { Some(sig) }
  def rewriteFunctionSig(sig : UclFunctionSig, ctx : ScopeMap) : Option[UclFunctionSig] = { Some(sig) }
  def rewriteLocalVar(lvar : UclLocalVarDecl, ctx : ScopeMap) : Option[UclLocalVarDecl] = { Some(lvar) }
  def rewriteStatement(st : UclStatement, ctx : ScopeMap) : Option[UclStatement] = { Some(st) }
  def rewriteSkip(st : UclSkipStmt, ctx : ScopeMap) : Option[UclSkipStmt] = { Some(st) }
  def rewriteAssert(st : UclAssertStmt, ctx : ScopeMap) : Option[UclAssertStmt] = { Some(st) }
  def rewriteAssume(st : UclAssumeStmt, ctx : ScopeMap) : Option[UclAssumeStmt] = { Some(st) }
  def rewriteHavoc(st : UclHavocStmt, ctx : ScopeMap) : Option[UclHavocStmt] = { Some(st) }
  def rewriteAssign(st : UclAssignStmt, ctx : ScopeMap) : Option[UclAssignStmt] = { Some(st) }
  def rewriteIfElse(st : UclIfElseStmt, ctx : ScopeMap) : Option[UclIfElseStmt] = { Some(st) }
  def rewriteFor(st : UclForStmt, ctx : ScopeMap) : Option[UclForStmt] = { Some(st) }
  def rewriteCase(st : UclCaseStmt, ctx : ScopeMap) : Option[UclCaseStmt] = { Some(st) }
  def rewriteProcedureCall(st : UclProcedureCallStmt, ctx : ScopeMap) : Option[UclProcedureCallStmt] = { Some(st) }
  def rewriteLHS(lhs : UclLhs, ctx : ScopeMap) : Option[UclLhs] = { Some(lhs) }
  def rewriteExpr(e : Expr, ctx : ScopeMap) : Option[Expr] = { Some(e) }
  def rewriteIdentifier(id : Identifier, ctx : ScopeMap) : Option[Identifier] = { Some(id) }
  def rewriteLit(lit : Literal, ctx : ScopeMap) : Option[Literal] = { Some(lit) }
  def rewriteBoolLit(b : BoolLit, ctx : ScopeMap) : Option[BoolLit] = { Some(b) }
  def rewriteIntLit(i : IntLit, ctx : ScopeMap) : Option[IntLit] = { Some(i) }
  def rewriteBitVectorLit(bv : BitVectorLit, ctx : ScopeMap) : Option[BitVectorLit] = { Some(bv) }
  def rewriteRecord(rec : Record, ctx : ScopeMap) : Option[Record] = { Some(rec) }
  def rewriteOperatorApp(opapp : UclOperatorApplication, ctx : ScopeMap) : Option[UclOperatorApplication] = { Some(opapp) }
  def rewriteOperator(op : Operator, ctx : ScopeMap) : Option[Operator] = { Some(op) }
  def rewriteArraySelect(arrSel : UclArraySelectOperation, ctx : ScopeMap) : Option[UclArraySelectOperation] = { Some(arrSel) }
  def rewriteArrayStore(arrStore : UclArrayStoreOperation, ctx : ScopeMap) : Option[UclArrayStoreOperation] = { Some(arrStore) }
  def rewriteFuncApp(fapp : UclFuncApplication, ctx : ScopeMap) : Option[UclFuncApplication] = { Some(fapp) }
  def rewriteITE(ite : UclITE, ctx : ScopeMap) : Option[UclITE] = { Some(ite) }
  def rewriteLambda(lambda : UclLambda, ctx : ScopeMap) : Option[UclLambda] = { Some(lambda) }
}


class ASTRewriter (_passName : String, _pass: RewritePass) extends ASTAnalysis {
  // Set a backpointer to here from the pass.
  _pass._analysis = Some(this)
  
  def pass = _pass
  override def passName = _passName
  override def visit(module : Module) : Option[Module] = visitModule(module)
  
  var astChangeFlag = false
  override def astChanged = astChangeFlag

  override def reset { 
    pass.reset()
    astChangeFlag = false
  }
  
  def visitModule(module : Module) : Option[Module] = {
    astChangeFlag = false
    val emptyContext = new ScopeMap()
    val context = emptyContext + module
    val id = visitIdentifier(module.id, context)
    val decls = module.decls.map(visitDecl(_, context)).flatten
    val cmds = module.cmds.map(visitCommand(_, context)).flatten
    val moduleP = id.flatMap((i) => pass.rewriteModule(Module(i, decls, cmds), emptyContext))
    astChangeFlag = astChangeFlag || (moduleP != Some(module))
    return moduleP
  }
  
  def visitDecl(decl : UclDecl, context : ScopeMap) : Option[UclDecl] = {
    val declP = (decl match {
      case procDecl : UclProcedureDecl => visitProcedure(procDecl, context)
      case typeDecl : UclTypeDecl => visitTypeDecl(typeDecl, context)
      case stateVar : UclStateVarDecl => visitStateVar(stateVar, context)
      case inputVar : UclInputVarDecl => visitInputVar(inputVar, context)
      case outputVar : UclOutputVarDecl => visitOutputVar(outputVar, context)
      case constDecl : UclConstantDecl => visitConstant(constDecl, context)
      case funcDecl : UclFunctionDecl => visitFunction(funcDecl, context)
      case initDecl : UclInitDecl => visitInit(initDecl, context)
      case nextDecl : UclNextDecl => visitNext(nextDecl, context)
      case specDecl : UclSpecDecl => visitSpec(specDecl, context)
    }).flatMap(pass.rewriteDecl(_, context))
    astChangeFlag = astChangeFlag || (declP != Some(decl))
    return declP
  }
  def visitProcedure(proc : UclProcedureDecl, contextIn : ScopeMap) : Option[UclProcedureDecl] = {
    val context = contextIn + proc
    val id = visitIdentifier(proc.id, context)
    val sig = visitProcedureSig(proc.sig, context)
    val decls = proc.decls.map(visitLocalVar(_, context)).flatten
    val stmts = proc.body.map(visitStatement(_, context)).flatten
    val procP = (id, sig) match {
      case (Some(i), Some(s)) => pass.rewriteProcedure(UclProcedureDecl(i, s, decls, stmts), contextIn)
      case _ => None 
    }
    astChangeFlag = astChangeFlag || (procP != Some(proc))
    return procP
  }
  
  def visitFunction(func : UclFunctionDecl, context : ScopeMap) : Option[UclFunctionDecl] = {
    val id = visitIdentifier(func.id, context)
    val sig = visitFunctionSig(func.sig, context)
    val funcP = (id, sig) match {
      case (Some(i), Some(s)) => pass.rewriteFunction(UclFunctionDecl(i, s), context)
      case _ => None
    }
    astChangeFlag = astChangeFlag || (funcP != Some(func))
    return funcP
  }
  
  def visitStateVar(stvar : UclStateVarDecl, context : ScopeMap) : Option[UclStateVarDecl] = {
    val idP = visitIdentifier(stvar.id, context)
    val typP = visitType(stvar.typ, context)
    (idP, typP) match {
      case (Some(id), Some(typ)) => pass.rewriteStateVar(UclStateVarDecl(id, typ), context)
      case _ => None
    }
  }
  
  def visitInputVar(inpvar : UclInputVarDecl, context : ScopeMap) : Option[UclInputVarDecl] = {
    val idP = visitIdentifier(inpvar.id, context)
    var typP = visitType(inpvar.typ, context)
    (idP, typP) match {
      case (Some(id), Some(typ)) => pass.rewriteInputVar(UclInputVarDecl(id, typ), context)
      case _ => None
    }
  }
  
  def visitOutputVar(outvar : UclOutputVarDecl, context : ScopeMap) : Option[UclOutputVarDecl] = {
    val idP = visitIdentifier(outvar.id, context)
    val typP = visitType(outvar.typ, context)
    (idP, typP) match {
      case (Some(id), Some(typ)) => pass.rewriteOutputVar(UclOutputVarDecl(id, typ), context)
      case _ => None
    }
  }
  
  def visitConstant(cnst : UclConstantDecl, context : ScopeMap) : Option[UclConstantDecl] = {
    val idP = visitIdentifier(cnst.id, context)
    val typP = visitType(cnst.typ, context)
    (idP, typP) match {
      case (Some(id), Some(typ)) => pass.rewriteConstant(UclConstantDecl(id, typ), context)
      case _ => None
    }
  }
  
  def visitSpec(spec : UclSpecDecl, context : ScopeMap) : Option[UclSpecDecl] = {
    val idP = visitIdentifier(spec.id, context)
    val exprP = visitExpr(spec.expr, context)
    (idP, exprP) match {
      case (Some(id), Some(expr)) => pass.rewriteSpec(UclSpecDecl(id, expr), context)
      case _ => None
    }
  }
  
  def visitTypeDecl(typDec : UclTypeDecl, context : ScopeMap) : Option[UclTypeDecl] = {
    val idP = visitIdentifier(typDec.id, context)
    val typeP = visitType(typDec.typ, context)
    (idP, typeP) match {
      case (Some(id), Some(typ)) => pass.rewriteTypeDecl(UclTypeDecl(id, typ), context)
      case _ => None
    }
  }
  
  def visitInit(init : UclInitDecl, context : ScopeMap) : Option[UclInitDecl] = {
    val body = init.body.map(visitStatement(_, context)).flatten
    return pass.rewriteInit(UclInitDecl(body), context)
  }
  
  def visitNext(next : UclNextDecl, context : ScopeMap) : Option[UclNextDecl] = {
    val body = next.body.map(visitStatement(_, context)).flatten
    return pass.rewriteNext(UclNextDecl(body), context)
  }
  
  def visitCommand(cmd : UclCmd, context : ScopeMap) : Option[UclCmd] = {
    return pass.rewriteCommand(cmd, context)
  }
  
  def visitType(typ: Type, context : ScopeMap) : Option[Type] = {
    return pass.rewriteType(typ, context)
  }

  def visitProcedureSig(sig : UclProcedureSig, context : ScopeMap) : Option[UclProcedureSig] = {
    val inParamsP : List[(Identifier, Type)] = sig.inParams.map((inP) => {
      (visitIdentifier(inP._1, context), visitType(inP._2, context)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    
    val outParamsP : List[(Identifier, Type)] = sig.outParams.map((outP) => {
      (visitIdentifier(outP._1, context), visitType(outP._2, context)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    
    return (inParamsP, outParamsP) match {
      case (in, out) => pass.rewriteProcedureSig(UclProcedureSig(in, out), context)
      case _ => None
    }
  }
  
  def visitFunctionSig(sig : UclFunctionSig, context : ScopeMap) : Option[UclFunctionSig] = {
    val args : List[(Identifier, Type)] = sig.args.map((inP) => {
      (visitIdentifier(inP._1, context), visitType(inP._2, context)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    return visitType(sig.retType, context).flatMap((t) => pass.rewriteFunctionSig(UclFunctionSig(args, t), context))
  }
  
  def visitLocalVar(lvar : UclLocalVarDecl, context : ScopeMap) : Option[UclLocalVarDecl] = {
    visitIdentifier(lvar.id, context).flatMap((id) => {
      visitType(lvar.typ, context).flatMap((t) => pass.rewriteLocalVar(UclLocalVarDecl(id, t), context))
    })
  }
  
  def visitStatement(st : UclStatement, context : ScopeMap) : Option[UclStatement] = {
    return (st match {
      case skipStmt : UclSkipStmt => visitSkipStatement(skipStmt, context)
      case assertStmt : UclAssertStmt => visitAssertStatement(assertStmt, context)
      case assumeStmt : UclAssumeStmt => visitAssumeStatement(assumeStmt, context)
      case havocStmt : UclHavocStmt => visitHavocStatement(havocStmt, context)
      case assignStmt : UclAssignStmt => visitAssignStatement(assignStmt, context)
      case ifElseStmt : UclIfElseStmt => visitIfElseStatement(ifElseStmt, context)
      case forStmt : UclForStmt => visitForStatement(forStmt, context)
      case caseStmt : UclCaseStmt => visitCaseStatement(caseStmt, context)
      case procCallStmt : UclProcedureCallStmt => visitProcedureCallStatement(procCallStmt, context)
    }).flatMap(pass.rewriteStatement(_, context))
  }

  def visitSkipStatement(st : UclSkipStmt, context : ScopeMap) : Option[UclSkipStmt] = {
    return pass.rewriteSkip(st, context)
  }
  
  def visitAssertStatement(st : UclAssertStmt, context : ScopeMap) : Option[UclAssertStmt] = {
    visitExpr(st.e, context).flatMap((e) => {
      pass.rewriteAssert(UclAssertStmt(e), context)
    })
  }
  
  def visitAssumeStatement(st : UclAssumeStmt, context : ScopeMap) : Option[UclAssumeStmt] = {
    visitExpr(st.e, context).flatMap((e) => {
      pass.rewriteAssume(UclAssumeStmt(e), context)
    })
  }
  
  def visitHavocStatement(st: UclHavocStmt, context : ScopeMap) : Option[UclHavocStmt] = {
    visitIdentifier(st.id, context).flatMap((id) => {
      pass.rewriteHavoc(UclHavocStmt(id), context)
    })
  }
  
  def visitAssignStatement(st : UclAssignStmt, context : ScopeMap) : Option[UclAssignStmt] = {
    val lhss = st.lhss.map(visitLhs(_, context)).flatten
    val rhss = st.rhss.map(visitExpr(_, context)).flatten
    return pass.rewriteAssign(UclAssignStmt(lhss, rhss), context)
  }
  
  def visitIfElseStatement(st : UclIfElseStmt, context : ScopeMap) : Option[UclIfElseStmt] = {
    val cond = visitExpr(st.cond, context)
    val ifblock = st.ifblock.map(visitStatement(_, context)).flatten
    val elseblock = st.elseblock.map(visitStatement(_, context)).flatten
    cond match {
      case Some(c) => pass.rewriteIfElse(UclIfElseStmt(c, ifblock, elseblock), context)
      case _ => None
    }
  }
  
  def visitForStatement(st : UclForStmt, context : ScopeMap) : Option[UclForStmt] = {
    val idP = visitIdentifier(st.id, context)
    val lit1P = visitIntLiteral(st.range._1, context)
    val lit2P = visitIntLiteral(st.range._2, context)
    val stmts = st.body.map(visitStatement(_, context)).flatten
    
    return (idP, lit1P, lit2P) match {
      case (Some(id), Some(lit1), Some(lit2)) => pass.rewriteFor(UclForStmt(id, (lit1, lit2), stmts), context)
      case _ => None
    }
  }
  
  def visitCaseStatement(st : UclCaseStmt, context : ScopeMap) : Option[UclCaseStmt] = {
    val bodyP = st.body.map((c) => {
      // if rewriting the expression doesn't produce None.
      visitExpr(c._1, context).flatMap((e) => {
        // then rewrite each of statements associated with the case expression.
        Some(e, c._2.map(visitStatement(_, context)).flatten)
      })
    }).flatten // and finally get rid of all the Options.
    return pass.rewriteCase(UclCaseStmt(bodyP), context)
  }
  
  def visitProcedureCallStatement(st : UclProcedureCallStmt, context : ScopeMap) : Option[UclProcedureCallStmt] = {
    val idP = visitIdentifier(st.id, context)
    val lhssP = st.callLhss.map(visitLhs(_, context)).flatten
    val argsP = st.args.map(visitExpr(_, context)).flatten
    idP.flatMap((id) => pass.rewriteProcedureCall(UclProcedureCallStmt(id, lhssP, argsP), context))
  }
  
  def visitLhs(lhs : UclLhs, context : ScopeMap) : Option[UclLhs] = {
    val idP = visitIdentifier(lhs.id, context)
    val arraySelectP = lhs.arraySelect.flatMap((as) => Some(as.map((e) => visitExpr(e, context)).flatten))
    val recordSelectP = lhs.recordSelect.flatMap((rs) => Some(rs.map((i) => visitIdentifier(i, context)).flatten))
    idP.flatMap((id) => {
      Some(UclLhs(id, arraySelectP, recordSelectP))
    })
  }
  
  def visitExpr(e : Expr, context : ScopeMap) : Option[Expr] = {
    return (e match {
      case i : Identifier => visitIdentifier(i, context)
      case lit : Literal => visitLiteral(lit, context)
      case rec : Record => visitRecord(rec, context)
      case opapp : UclOperatorApplication => visitOperatorApp(opapp, context)
      case arrSel : UclArraySelectOperation => visitArraySelectOp(arrSel, context)
      case arrUpd : UclArrayStoreOperation => visitArrayStoreOp(arrUpd, context)
      case fapp : UclFuncApplication => visitFuncApp(fapp, context)
      case ite : UclITE => visitITE(ite, context)
      case lambda : UclLambda => visitLambda(lambda, context)
    }).flatMap(pass.rewriteExpr(_, context))
  }
  
  def visitIdentifier(id : Identifier, context : ScopeMap) : Option[Identifier] = {
    return pass.rewriteIdentifier(id, context)
  }
  
  def visitLiteral(lit : Literal, context : ScopeMap) : Option[Literal] = {
    return (lit match {
      case b : BoolLit => visitBoolLiteral(b, context)
      case i : IntLit => visitIntLiteral(i, context)
      case bv : BitVectorLit => visitBitVectorLiteral(bv, context)
    }).flatMap(pass.rewriteLit(_, context))
  }
  
  def visitBoolLiteral(b : BoolLit, context : ScopeMap) : Option[BoolLit] = {
    return pass.rewriteBoolLit(b, context)
  }
  
  def visitIntLiteral(i : IntLit, context : ScopeMap) : Option[IntLit] = {
    return pass.rewriteIntLit(i, context)
  }
  
  def visitBitVectorLiteral(bv : BitVectorLit, context : ScopeMap) : Option[BitVectorLit] = {
    return pass.rewriteBitVectorLit(bv, context)
  }
  
  def visitRecord(rec : Record, context : ScopeMap) : Option[Record] = {
    pass.rewriteRecord(Record(rec.value.map(visitExpr(_, context)).flatten), context)
  }
  
  def visitOperatorApp(opapp : UclOperatorApplication, context : ScopeMap) : Option[UclOperatorApplication] = {
    return visitOperator(opapp.op, context).flatMap((op) => {
      pass.rewriteOperatorApp(UclOperatorApplication(op, opapp.operands.map(visitExpr(_, context)).flatten), context)
    })
  }
  
  def visitOperator(op : Operator, context : ScopeMap) : Option[Operator] = {
    return pass.rewriteOperator(op, context)
  }
  
  def visitArraySelectOp(arrSel : UclArraySelectOperation, context : ScopeMap) : Option[UclArraySelectOperation] = {
    return visitExpr(arrSel.e, context) match {
      case Some(e) => pass.rewriteArraySelect(UclArraySelectOperation(e, arrSel.index.map(visitExpr(_, context)).flatten), context)
      case _ => None
    }
  }
  
  def visitArrayStoreOp(arrStore : UclArrayStoreOperation, context : ScopeMap) : Option[UclArrayStoreOperation] = {
    val eP = visitExpr(arrStore.e, context)
    val ind = arrStore.index.map(visitExpr(_, context)).flatten
    val valP = visitExpr(arrStore.value, context)
    return (eP, valP) match {
      case (Some(e), Some(value)) => pass.rewriteArrayStore(UclArrayStoreOperation(e, ind, value), context)
      case _ => None
    }
  }
  
  def visitFuncApp(fapp : UclFuncApplication, context : ScopeMap) : Option[UclFuncApplication] = {
    val eP = visitExpr(fapp.e, context)
    val args = fapp.args.map(visitExpr(_, context)).flatten
    eP match {
      case Some(e) => pass.rewriteFuncApp(UclFuncApplication(e, args), context)
      case _ => None
    }
  }
  
  def visitITE(ite: UclITE, context : ScopeMap) : Option[UclITE] = {
    val condP = visitExpr(ite.e, context)
    val tP = visitExpr(ite.t, context)
    val fP = visitExpr(ite.f, context)
    
    (condP, tP, fP) match {
      case (Some(cond), Some(t), Some(f)) => pass.rewriteITE(UclITE(cond, t, f), context)
      case _ => None
    }
  }
  
  def visitLambda(lambda: UclLambda, contextIn : ScopeMap) : Option[UclLambda] = {
    val context = contextIn + lambda
    val idP = lambda.ids.map((arg) => {
      (visitIdentifier(arg._1, context), visitType(arg._2, context)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    return visitExpr(lambda.e, context).flatMap((e) => pass.rewriteLambda(UclLambda(idP, e), contextIn))
  }
}
