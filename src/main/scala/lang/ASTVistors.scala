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
 * Author : Pramod Subramanyan
 *
 * INTRODUCTION: The AST Pass Infrastructure
 * =========================================
 *
 * ReadOnlyPass[T] is the base class for all passes that walk through a pass and possibly collect
 * information about the AST. Think of it as akin to a the function passed in to a fold operation.
 *
 * RewritePass is the base class for all passes that modify the AST.
 *
 * ASTAnalyzer takes a ReadOnlyPass[T] and "folds" (reduces/accumulates) the pass's results over the AST.
 *
 * ASTRewriter takes a RewritePass and rewrites each element of the AST using the RewritePass.
 *
 * USAGE
 * =====
 *
 * To write a pass of your own, you will subclass either ReadOnlyPass[T] and ASTAnalyzer or
 * RewritePass and ASTRewriter.
 *
 * A simple readonly pass to look at is SemanticAnalyzer.
 *
 * A simple readwrite pass is CaseEliminator.
 */

package uclid
package lang

abstract class ASTAnalysis {
  var _manager : Option[PassManager] = None
  def manager : PassManager = { _manager.get }

  def passName : String
  def reset() {}
  def rewind() {}
  def visit (module : Module, context : Scope) : Option[Module]
  def finish() {}
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

  def applyOnModule(d : TraversalDirection.T, module : Module, in : T, context : Scope) : T = { in }
  def applyOnDecl(d : TraversalDirection.T, decl : Decl, in : T, context : Scope) : T = { in }
  def applyOnInstance(d : TraversalDirection.T, inst : InstanceDecl, in : T, context : Scope) : T = { in }
  def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : T, context : Scope) : T = { in }
  def applyOnFunction(d : TraversalDirection.T, func : FunctionDecl, in : T, context : Scope) : T = { in }
  def applyOnGrammarTerm(d : TraversalDirection.T, gTerm : GrammarTerm, in : T, context : Scope) : T = { in }
  def applyOnGrammar(d : TraversalDirection.T, grammar: GrammarDecl, in : T, context : Scope) : T = { in }
  def applyOnSynthesisFunction(d : TraversalDirection.T, synFunc : SynthesisFunctionDecl, in : T, context : Scope) : T = { in }
  def applyOnDefine(d : TraversalDirection.T, defDecl : DefineDecl, in : T, context : Scope) : T = { in }
  def applyOnStateVars(d : TraversalDirection.T, stVars : StateVarsDecl, in : T, context : Scope) : T = { in }
  def applyOnInputVars(d : TraversalDirection.T, inpVars : InputVarsDecl, in : T, context : Scope) : T = { in }
  def applyOnOutputVars(d : TraversalDirection.T, outvars : OutputVarsDecl, in : T, context : Scope) : T = { in }
  def applyOnSharedVars(d : TraversalDirection.T, sharedVars : SharedVarsDecl, in : T, context : Scope) : T = { in }
  def applyOnConstant(d : TraversalDirection.T, cnst : ConstantsDecl, in : T, context : Scope) : T = { in }
  def applyOnSpec(d : TraversalDirection.T, spec : SpecDecl, in : T, context : Scope) : T = { in }
  def applyOnAxiom(d : TraversalDirection.T, axiom : AxiomDecl, in : T, context : Scope) : T = { in }
  def applyOnTypeDecl(d : TraversalDirection.T, typDec : TypeDecl, in : T, context : Scope) : T = { in }
  def applyOnInit(d : TraversalDirection.T, init : InitDecl, in : T, context : Scope) : T = { in }
  def applyOnNext(d : TraversalDirection.T, next : NextDecl, in : T, context : Scope) : T = { in }
  def applyOnType(d : TraversalDirection.T, typ: Type, in : T, context : Scope) : T = { in }
  def applyOnUndefinedType(d : TraversalDirection.T, undefT : UndefinedType, in : T, context : Scope) : T = { in }
  def applyOnUninterpretedType(d : TraversalDirection.T, unintT : UninterpretedType, in : T, context : Scope) : T = { in }
  def applyOnBoolType(d : TraversalDirection.T, boolT : BooleanType, in : T, context : Scope) : T = { in }
  def applyOnIntType(d : TraversalDirection.T, intT : IntegerType, in : T, context : Scope) : T = { in }
  def applyOnBitVectorType(d : TraversalDirection.T, bvT : BitVectorType, in : T, context : Scope) : T = { in }
  def applyOnEnumType(d : TraversalDirection.T, enumT : EnumType, in : T, context : Scope) : T = { in }
  def applyOnTupleType(d : TraversalDirection.T, tupleT : TupleType, in : T, context : Scope) : T = { in }
  def applyOnRecordType(d : TraversalDirection.T, recordT : RecordType, in : T, context : Scope) : T = { in }
  def applyOnMapType(d : TraversalDirection.T, mapT : MapType, in : T, context : Scope) : T = { in }
  def applyOnProcedureType(d : TraversalDirection.T, procT : ProcedureType, in : T, context : Scope) : T = { in }
  def applyOnArrayType(d : TraversalDirection.T, arrayT : ArrayType, in : T, context : Scope) : T = { in }
  def applyOnSynonymType(d : TraversalDirection.T, synT : SynonymType, in : T, context : Scope) : T = { in }
  def applyOnExternalType(d : TraversalDirection.T, extT : ExternalType, in : T, context : Scope) : T = { in }
  def applyOnModuleInstanceType(d : TraversalDirection.T, instT : ModuleInstanceType, in : T, context : Scope) : T = { in }
  def applyOnModuleType(d : TraversalDirection.T, modT : ModuleType, in : T, context : Scope) : T = { in }
  def applyOnProcedureSig(d : TraversalDirection.T, sig : ProcedureSig, in : T, context : Scope) : T = { in }
  def applyOnFunctionSig(d : TraversalDirection.T, sig : FunctionSig, in : T, context : Scope) : T = { in }
  def applyOnLocalVar(d : TraversalDirection.T, lvar : LocalVarDecl, in : T, context : Scope) : T = { in }
  def applyOnStatement(d : TraversalDirection.T, st : Statement, in : T, context : Scope) : T = { in }
  def applyOnSkip(d : TraversalDirection.T, st : SkipStmt, in : T, context : Scope) : T = { in }
  def applyOnAssert(d : TraversalDirection.T, st : AssertStmt, in : T, context : Scope) : T = { in }
  def applyOnAssume(d : TraversalDirection.T, st : AssumeStmt, in : T, context : Scope) : T = { in }
  def applyOnHavoc(d : TraversalDirection.T, st : HavocStmt, in : T, context : Scope) : T = { in }
  def applyOnAssign(d : TraversalDirection.T, st : AssignStmt, in : T, context : Scope) : T = { in }
  def applyOnIfElse(d : TraversalDirection.T, st : IfElseStmt, in : T, context : Scope) : T = { in }
  def applyOnFor(d : TraversalDirection.T, st : ForStmt, in : T, context : Scope) : T = { in }
  def applyOnCase(d : TraversalDirection.T, st : CaseStmt, in : T, context : Scope) : T = { in }
  def applyOnProcedureCall(d : TraversalDirection.T, st : ProcedureCallStmt, in : T, context : Scope) : T = { in }
  def applyOnModuleCall(d : TraversalDirection.T, st : ModuleCallStmt, in : T, context : Scope) : T = { in }
  def applyOnLHS(d : TraversalDirection.T, lhs : Lhs, in : T, context : Scope) : T = { in }
  def applyOnBitVectorSlice(d : TraversalDirection.T, slice : BitVectorSlice, in : T, context : Scope) : T = { in }
  def applyOnExpr(d : TraversalDirection.T, e : Expr, in : T, context : Scope) : T = { in }
  def applyOnIdentifier(d : TraversalDirection.T, id : Identifier, in : T, context : Scope) : T = { in }
  def applyOnExternalIdentifier(d : TraversalDirection.T, eId : ExternalIdentifier, in : T, context : Scope) : T = { in }
  def applyOnLit(d : TraversalDirection.T, lit : Literal, in : T, context : Scope) : T = { in }
  def applyOnFreshLit(d : TraversalDirection.T, f : FreshLit, in : T, context : Scope) : T = { in }
  def applyOnBoolLit(d : TraversalDirection.T, b : BoolLit, in : T, context : Scope) : T = { in }
  def applyOnNumericLit(d : TraversalDirection.T, b : NumericLit, in : T, context : Scope) : T = { in }
  def applyOnIntLit(d : TraversalDirection.T, i : IntLit, in : T, context : Scope) : T = { in }
  def applyOnBitVectorLit(d : TraversalDirection.T, bv : BitVectorLit, in : T, context : Scope) : T = { in }
  def applyOnTuple(d : TraversalDirection.T, rec : Tuple, in : T, context : Scope) : T = { in }
  def applyOnOperatorApp(d : TraversalDirection.T, opapp : OperatorApplication, in : T, context : Scope) : T = { in }
  def applyOnOperator(d : TraversalDirection.T, op : Operator, in : T, context : Scope) : T = { in }
  def applyOnArraySelect(d : TraversalDirection.T, arrSel : ArraySelectOperation, in : T, context : Scope) : T = { in }
  def applyOnArrayStore(d : TraversalDirection.T, arrStore : ArrayStoreOperation, in : T, context : Scope) : T = { in }
  def applyOnFuncApp(d : TraversalDirection.T, fapp : FuncApplication, in : T, context : Scope) : T = { in }
  def applyOnITE(d : TraversalDirection.T, ite : ITE, in : T, context : Scope) : T = { in }
  def applyOnLambda(d : TraversalDirection.T, lambda : Lambda, in : T, context : Scope) : T = { in }
  def applyOnExprDecorator(d : TraversalDirection.T, dec : ExprDecorator, in : T, context : Scope) : T = { in }
  def applyOnCmd(d : TraversalDirection.T, cmd : GenericProofCommand, in : T, context : Scope) : T = { in }
}

/* AST Visitor that rewrites and generates a new AST. */
trait RewritePass {
  var _analysis : Option[ASTAnalysis] = None
  def analysis : ASTAnalysis = _analysis.get
  def reset() { }

  def rewriteModule(module : Module, ctx : Scope) : Option[Module] = { Some(module) }
  def rewriteDecl(decl : Decl, ctx : Scope) : Option[Decl] = { Some(decl) }
  def rewriteCommand(cmd : GenericProofCommand, ctx : Scope) : Option[GenericProofCommand] = { Some(cmd) }
  def rewriteInstance(inst : InstanceDecl, ctx : Scope) : Option[InstanceDecl] = { Some(inst) }
  def rewriteProcedure(proc : ProcedureDecl, ctx : Scope) : Option[ProcedureDecl] = { Some(proc) }
  def rewriteFunction(func : FunctionDecl, ctx : Scope) : Option[FunctionDecl] = { Some(func) }
  def rewriteGrammarTerm(gTerm : GrammarTerm, ctx : Scope) : Option[GrammarTerm] = { Some(gTerm) }
  def rewriteGrammar(grammar : GrammarDecl, ctx : Scope) : Option[GrammarDecl] = { Some(grammar) }
  def rewriteSynthesisFunction(synFunc : SynthesisFunctionDecl, ctx : Scope) : Option[SynthesisFunctionDecl] = { Some(synFunc) }
  def rewriteDefine(defDecl : DefineDecl, ctx : Scope) : Option[DefineDecl] = { Some(defDecl) }
  def rewriteStateVars(stVars : StateVarsDecl, ctx : Scope) : Option[StateVarsDecl] = { Some(stVars) }
  def rewriteInputVars(inpVars : InputVarsDecl, ctx : Scope) : Option[InputVarsDecl] = { Some(inpVars) }
  def rewriteOutputVars(outvars : OutputVarsDecl, ctx : Scope) : Option[OutputVarsDecl] = { Some(outvars) }
  def rewriteSharedVars(sharedVars : SharedVarsDecl, ctx : Scope) : Option[SharedVarsDecl] = { Some(sharedVars) }
  def rewriteConstant(cnst : ConstantsDecl, ctx : Scope) : Option[ConstantsDecl] = { Some(cnst) }
  def rewriteSpec(spec : SpecDecl, ctx : Scope) : Option[SpecDecl] = { Some(spec) }
  def rewriteAxiom(axiom : AxiomDecl, ctx : Scope) : Option[AxiomDecl] = { Some(axiom) }
  def rewriteTypeDecl(typDec : TypeDecl, ctx : Scope) : Option[TypeDecl] = { Some(typDec) }
  def rewriteInit(init : InitDecl, ctx : Scope) : Option[InitDecl] = { Some(init) }
  def rewriteNext(next : NextDecl, ctx : Scope) : Option[NextDecl] = { Some(next) }
  def rewriteType(typ: Type, ctx : Scope) : Option[Type] = { Some(typ) }
  def rewriteUndefinedType(undefT : UndefinedType, context : Scope) : Option[Type] = { Some(undefT) }
  def rewriteUninterpretedType(unintT : UninterpretedType, context : Scope) : Option[UninterpretedType] = { Some(unintT) }
  def rewriteBoolType(boolT : BooleanType, context : Scope) : Option[BooleanType] = { Some(boolT) }
  def rewriteIntType(intT : IntegerType, context : Scope) : Option[IntegerType] = { Some(intT)  }
  def rewriteBitVectorType(bvT : BitVectorType, context : Scope) : Option[BitVectorType] = { Some(bvT)  }
  def rewriteEnumType(enumT : EnumType, context : Scope) : Option[EnumType] = { Some(enumT)  }
  def rewriteTupleType(tupleT : TupleType, context : Scope) : Option[TupleType] = { Some(tupleT)  }
  def rewriteRecordType(recordT : RecordType, context : Scope) : Option[RecordType] = { Some(recordT)  }
  def rewriteMapType(mapT : MapType, context : Scope) : Option[MapType] = { Some(mapT)  }
  def rewriteProcedureType(procT : ProcedureType, context : Scope) : Option[ProcedureType] = { Some(procT) }
  def rewriteArrayType(arrayT : ArrayType, context : Scope) : Option[ArrayType] = { Some(arrayT)  }
  def rewriteSynonymType(synT : SynonymType, context : Scope) : Option[Type] = { Some(synT)  }
  def rewriteExternalType(extT : ExternalType, context : Scope) : Option[Type] = { Some(extT) }
  def rewriteModuleInstanceType(instT : ModuleInstanceType, context : Scope) : Option[ModuleInstanceType] = { Some(instT)  }
  def rewriteModuleType(modT : ModuleType, context : Scope) : Option[ModuleType] = { Some(modT)  }
  def rewriteProcedureSig(sig : ProcedureSig, ctx : Scope) : Option[ProcedureSig] = { Some(sig) }
  def rewriteFunctionSig(sig : FunctionSig, ctx : Scope) : Option[FunctionSig] = { Some(sig) }
  def rewriteLocalVar(lvar : LocalVarDecl, ctx : Scope) : Option[LocalVarDecl] = { Some(lvar) }
  def rewriteStatement(st : Statement, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteSkip(st : SkipStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteAssert(st : AssertStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteAssume(st : AssumeStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteHavoc(st : HavocStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteAssign(st : AssignStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteIfElse(st : IfElseStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteFor(st : ForStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteCase(st : CaseStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteProcedureCall(st : ProcedureCallStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteModuleCall(st : ModuleCallStmt, ctx : Scope) : List[Statement] = { List(st) }
  def rewriteLHS(lhs : Lhs, ctx : Scope) : Option[Lhs] = { Some(lhs) }
  def rewriteBitVectorSlice(slice : BitVectorSlice, ctx : Scope) : Option[BitVectorSlice] = { Some(slice) }
  def rewriteExpr(e : Expr, ctx : Scope) : Option[Expr] = { Some(e) }
  def rewriteIdentifier(id : Identifier, ctx : Scope) : Option[Identifier] = { Some(id) }
  def rewriteExternalIdentifier(eId : ExternalIdentifier, ctx : Scope) : Option[Expr] = { Some(eId) }
  def rewriteLit(lit : Literal, ctx : Scope) : Option[Literal] = { Some(lit) }
  def rewriteFreshLit(f : FreshLit, ctx : Scope) : Option[Expr] = { Some(f) }
  def rewriteBoolLit(b : BoolLit, ctx : Scope) : Option[BoolLit] = { Some(b) }
  def rewriteIntLit(i : IntLit, ctx : Scope) : Option[IntLit] = { Some(i) }
  def rewriteBitVectorLit(bv : BitVectorLit, ctx : Scope) : Option[BitVectorLit] = { Some(bv) }
  def rewriteNumericLit(n : NumericLit, ctx : Scope) : Option[NumericLit] = { Some(n) }
  def rewriteTuple(rec : Tuple, ctx : Scope) : Option[Tuple] = { Some(rec) }
  def rewriteOperatorApp(opapp : OperatorApplication, ctx : Scope) : Option[Expr] = { Some(opapp) }
  def rewriteOperator(op : Operator, ctx : Scope) : Option[Operator] = { Some(op) }
  def rewriteArraySelect(arrSel : ArraySelectOperation, ctx : Scope) : Option[Expr] = { Some(arrSel) }
  def rewriteArrayStore(arrStore : ArrayStoreOperation, ctx : Scope) : Option[Expr] = { Some(arrStore) }
  def rewriteFuncApp(fapp : FuncApplication, ctx : Scope) : Option[Expr] = { Some(fapp) }
  def rewriteITE(ite : ITE, ctx : Scope) : Option[Expr] = { Some(ite) }
  def rewriteExprDecorator(dec : ExprDecorator, ctx : Scope) : Option[ExprDecorator] = { Some(dec) }
  def rewriteLambda(lambda : Lambda, ctx : Scope) : Option[Lambda] = { Some(lambda) }
}

class ASTAnalyzer[T] (_passName : String, _pass: ReadOnlyPass[T]) extends ASTAnalysis {
  // Set a backpointer to the pass from here.
  _pass._analysis = Some(this)

  /** The pass itself. */
  def pass : ReadOnlyPass[T] = _pass
  /** The input/outputs of the pass. */
  protected[this] var _in : Option[T] = None
  protected[this] var _out : Option[T] = None
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
  /** Sets in to out in order to chain modules. **/
  override def rewind() {
    _in = _out
  }
  /** The main 'do-er' method. */
  override def visit(module : Module, context : Scope) : Option[Module] = {
    _out = Some(visitModule(module, _in.get, context))
    return Some(module)
  }
  // Reset calls reset on the pass.
  override  def reset() = { pass.reset() }

  // We now have the code that actually traverses the AST.
  def visitModule(module : Module, in : T, initContext : Scope) : T = {
    var result : T = in
    val context = initContext + module

    result = pass.applyOnModule(TraversalDirection.Down, module, result, initContext)
    result = visitIdentifier(module.id, result, context)
    result = module.decls.foldLeft(result)((acc, i) => visitDecl(i, acc, context))
    val initR : (T, Scope) = (result, context)
    result = module.cmds.foldLeft(initR)((acc, i) => (visitCmd(i, acc._1, acc._2), acc._2 + i))._1
    result = pass.applyOnModule(TraversalDirection.Up, module, result, initContext)
    return result
  }
  def visitDecl(decl : Decl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnDecl(TraversalDirection.Down, decl, result, context)
    result = decl match {
      case inst : InstanceDecl => visitInstance(inst, result, context)
      case proc: ProcedureDecl => visitProcedure(proc, result, context)
      case typ : TypeDecl => visitTypeDecl(typ, result, context)
      case stVars : StateVarsDecl => visitStateVars(stVars, result, context)
      case inpVars : InputVarsDecl => visitInputVars(inpVars, result, context)
      case outVars : OutputVarsDecl => visitOutputVars(outVars, result, context)
      case sharedVars : SharedVarsDecl => visitSharedVars(sharedVars, result, context)
      case const : ConstantsDecl => visitConstants(const, result, context)
      case func : FunctionDecl => visitFunction(func, result, context)
      case grammar : GrammarDecl => visitGrammar(grammar, result, context)
      case synFunc : SynthesisFunctionDecl => visitSynthesisFunction(synFunc, result, context)
      case defDecl : DefineDecl => visitDefine(defDecl, in, context)
      case init : InitDecl => visitInit(init, result, context)
      case next : NextDecl => visitNext(next, result, context)
      case spec : SpecDecl => visitSpec(spec, result, context)
      case axiom : AxiomDecl => visitAxiom(axiom, result, context)
    }
    result = pass.applyOnDecl(TraversalDirection.Up, decl, result, context)
    return result
  }
  def visitInstance(inst : InstanceDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnInstance(TraversalDirection.Down, inst, result, context)
    result = visitIdentifier(inst.instanceId, result, context)
    result = visitIdentifier(inst.moduleId, result, context)
    result = inst.arguments.foldLeft(result){
      (acc, arg) => arg._2 match {
        case Some(expr) => visitExpr(expr, acc, context)
        case None => acc
      }
    }
    result = inst.instType match {
      case Some(typ) => visitType(typ, result, context)
      case None => result
    }
    result = inst.modType match {
      case Some(typ) => visitType(typ, result, context)
      case None => result
    }
    result = pass.applyOnInstance(TraversalDirection.Up, inst, result, context)
    return result
  }
  def visitProcedure(proc : ProcedureDecl, in : T, contextIn : Scope) : T = {
    var result : T = in
    val context = contextIn + proc
    result = pass.applyOnProcedure(TraversalDirection.Down, proc, result, contextIn)
    result = visitIdentifier(proc.id, result, context)
    result = visitProcedureSig(proc.sig, result, context)
    result = proc.decls.foldLeft(result)((acc, i) => visitLocalVar(i, acc, context))
    result = proc.body.foldLeft(result)((acc, i) => visitStatement(i, acc, context))
    result = proc.requires.foldLeft(result)((acc, r) => visitExpr(r, acc, context.withVerificationContext(RequiresContext)))
    result = proc.ensures.foldLeft(result)((acc, r) => visitExpr(r, acc, context.withVerificationContext(EnsuresContext)))
    result = proc.modifies.foldLeft(result)((acc, r) => visitIdentifier(r, acc, context))
    result = pass.applyOnProcedure(TraversalDirection.Up, proc, result, contextIn)
    return result
  }
  def visitFunction(func : FunctionDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnFunction(TraversalDirection.Down, func, result, context)
    result = visitIdentifier(func.id, result, context)
    result = visitFunctionSig(func.sig, result, context)
    result = pass.applyOnFunction(TraversalDirection.Up, func, result, context)
    return result
  }
  def visitGrammarTerms(gTerms : List[GrammarTerm], in : T, context : Scope) : T = {
    var result : T = in
    result = gTerms.foldLeft(result)((acc, gt) => pass.applyOnGrammarTerm(TraversalDirection.Down, gt, acc, context))
    result = gTerms.foldLeft(result)((acc, gt) => pass.applyOnGrammarTerm(TraversalDirection.Up, gt, acc, context))
    result
  }
  def visitGrammar(grammar : GrammarDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnGrammar(TraversalDirection.Down, grammar, result, context)
    result = visitIdentifier(grammar.id, result, context)
    result = visitFunctionSig(grammar.sig, result, context)
    result = visitGrammarTerms(grammar.nonterminals, result, context)
    result = pass.applyOnGrammar(TraversalDirection.Up, grammar, result, context)
    result
  }
  def visitSynthesisFunction(synFunc : SynthesisFunctionDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnSynthesisFunction(TraversalDirection.Down, synFunc, result, context)
    result = visitIdentifier(synFunc.id, result, context)
    result = visitFunctionSig(synFunc.sig, result, context)
    val contextP = context + synFunc.sig
    // FIXME
    result = pass.applyOnSynthesisFunction(TraversalDirection.Up, synFunc, result, context)
    return result
  }
  def visitDefine(defDecl : DefineDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnDefine(TraversalDirection.Down, defDecl, result, context)
    result = visitIdentifier(defDecl.id, result, context)
    result = visitFunctionSig(defDecl.sig, result, context)
    val contextP = context + defDecl.sig
    result = visitExpr(defDecl.expr, result, contextP)
    result = pass.applyOnDefine(TraversalDirection.Up, defDecl, result, context)
    return result
  }

  def visitStateVars(stVars : StateVarsDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnStateVars(TraversalDirection.Down, stVars, result, context)
    result = stVars.ids.foldLeft(result)((acc, id) => visitIdentifier(id, acc, context))
    result = visitType(stVars.typ, result, context)
    result = pass.applyOnStateVars(TraversalDirection.Up, stVars, result, context)
    return result
  }
  def visitInputVars(inpVars : InputVarsDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnInputVars(TraversalDirection.Down, inpVars, result, context)
    result = inpVars.ids.foldLeft(result)((acc, id) => visitIdentifier(id, acc, context))
    result = visitType(inpVars.typ, result, context)
    result = pass.applyOnInputVars(TraversalDirection.Up, inpVars, result, context)
    return result
  }
  def visitOutputVars(outVars : OutputVarsDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnOutputVars(TraversalDirection.Down, outVars, result, context)
    result = outVars.ids.foldLeft(result)((acc, id) => visitIdentifier(id, acc, context))
    result = visitType(outVars.typ, result, context)
    result = pass.applyOnOutputVars(TraversalDirection.Up, outVars, result, context)
    return result
  }
  def visitSharedVars(sharedVars : SharedVarsDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnSharedVars(TraversalDirection.Down, sharedVars, result, context)
    result = sharedVars.ids.foldLeft(result)((acc, id) => visitIdentifier(id, acc, context))
    result = visitType(sharedVars.typ, result, context)
    result = pass.applyOnSharedVars(TraversalDirection.Up, sharedVars, result, context)
    return result
  }
  def visitConstants(cnst : ConstantsDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnConstant(TraversalDirection.Down, cnst, result, context)
    result = cnst.ids.foldLeft(result)((acc, id) => visitIdentifier(id, result, context))
    result = visitType(cnst.typ, result, context)
    result = pass.applyOnConstant(TraversalDirection.Up, cnst, result, context)
    return result
  }
  def visitSpec(spec : SpecDecl, in : T, context : Scope) : T = {
    var result : T = in
    val contextP = if (spec.params.contains(LTLExprDecorator)) {
      context.withLTLSpec
    } else {
      context
    }
    result = pass.applyOnSpec(TraversalDirection.Down, spec, result, context)
    result = visitIdentifier(spec.id, result, context)
    result = visitExpr(spec.expr, result, contextP.withVerificationContext(SpecContext))
    result = spec.params.foldLeft(result)((acc, d) => visitExprDecorator(d, acc, context))
    result = pass.applyOnSpec(TraversalDirection.Up, spec, result, context)
    return result
  }
  def visitAxiom(axiom : AxiomDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnAxiom(TraversalDirection.Down, axiom, result, context)
    result = axiom.id match {
      case Some(id) => visitIdentifier(id, result, context)
      case None => result
    }
    result = visitExpr(axiom.expr, result, context.withVerificationContext(AxiomContext))
    result = pass.applyOnAxiom(TraversalDirection.Up, axiom, result, context)
    return result
  }
  def visitTypeDecl(typDec : TypeDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnTypeDecl(TraversalDirection.Down, typDec, result, context)
    result = visitIdentifier(typDec.id, result, context)
    result = visitType(typDec.typ, result, context)
    result = pass.applyOnTypeDecl(TraversalDirection.Up, typDec, result, context)
    return result
  }
  def visitInit(init : InitDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnInit(TraversalDirection.Down, init, result, context)
    result = init.body.foldLeft(result)((acc, i) => visitStatement(i, acc, context))
    result = pass.applyOnInit(TraversalDirection.Up, init, result, context)
    return result
  }
  def visitNext(next : NextDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnNext(TraversalDirection.Down, next, result, context)
    result = next.body.foldLeft(result)((acc, i) => visitStatement(i, acc, context))
    result = pass.applyOnNext(TraversalDirection.Up, next, result, context)
    return result
  }
  def visitCmd(cmd : GenericProofCommand, in : T, context : Scope) : T = {
    var result : T = in
    val contextP = cmd.getContext(context + cmd)
    result = pass.applyOnCmd(TraversalDirection.Down, cmd, result, context)
    result = cmd.args.foldLeft(result)((r, expr) => visitExpr(expr, r, contextP))
    result = cmd.resultVar match {
      case Some(id) => visitIdentifier(id, result, contextP)
      case None => result
    }
    result = cmd.argObj match {
      case Some(id) => visitIdentifier(id, result, contextP)
      case None => result
    }
    result = pass.applyOnCmd(TraversalDirection.Up, cmd, result, context)
    return result
  }

  def visitType(typ: Type, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnType(TraversalDirection.Down, typ, result, context)
    result = typ match {
      case undefT : UndefinedType => visitUndefinedType(undefT, result, context)
      case unintT : UninterpretedType => visitUninterpretedType(unintT, result, context)
      case boolT : BooleanType => visitBoolType(boolT, result, context)
      case intT : IntegerType => visitIntType(intT, result, context)
      case bvT : BitVectorType => visitBitVectorType(bvT, result, context)
      case enumT : EnumType => visitEnumType(enumT, result, context)
      case tupleT : TupleType => visitTupleType(tupleT, result, context)
      case recT : RecordType => visitRecordType(recT, result, context)
      case mapT : MapType => visitMapType(mapT, result, context)
      case procT : ProcedureType => visitProcedureType(procT, result, context)
      case arrT : ArrayType => visitArrayType(arrT, result, context)
      case synT : SynonymType => visitSynonymType(synT, result, context)
      case extT : ExternalType => visitExternalType(extT, result, context)
      case instT : ModuleInstanceType => visitModuleInstanceType(instT, result, context)
      case modT : ModuleType => visitModuleType(modT, result, context)
    }
    result = pass.applyOnType(TraversalDirection.Up, typ, result, context)
    return result
  }
  def visitUndefinedType(undefT : UndefinedType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnUndefinedType(TraversalDirection.Down, undefT, result, context)
    result = pass.applyOnUndefinedType(TraversalDirection.Up, undefT, result, context)
    return result
  }
  def visitUninterpretedType(unintT : UninterpretedType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnUninterpretedType(TraversalDirection.Down, unintT, result, context)
    result = pass.applyOnUninterpretedType(TraversalDirection.Up, unintT, result, context)
    return result
  }
  def visitBoolType(boolT : BooleanType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnBoolType(TraversalDirection.Down, boolT, result, context)
    result = pass.applyOnBoolType(TraversalDirection.Up, boolT, result, context)
    return result
  }
  def visitIntType(intT : IntegerType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnIntType(TraversalDirection.Down, intT, result, context)
    result = pass.applyOnIntType(TraversalDirection.Up, intT, result, context)
    return result
  }
  def visitBitVectorType(bvT : BitVectorType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnBitVectorType(TraversalDirection.Down, bvT, result, context)
    result = pass.applyOnBitVectorType(TraversalDirection.Up, bvT, result, context)
    return result
  }
  def visitEnumType(enumT : EnumType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnEnumType(TraversalDirection.Down, enumT, result, context)
    result = pass.applyOnEnumType(TraversalDirection.Up, enumT, result, context)
    return result
  }
  def visitTupleType(tupleT : TupleType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnTupleType(TraversalDirection.Down, tupleT, result, context)
    result = tupleT.fieldTypes.foldLeft(result)((acc, typ) => visitType(typ, acc, context))
    result = pass.applyOnTupleType(TraversalDirection.Up, tupleT, result, context)
    return result
  }
  def visitRecordType(recordT : RecordType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnRecordType(TraversalDirection.Down, recordT, result, context)
    result = recordT.fields.foldLeft(result)((acc, fld) => {
      visitType(fld._2, visitIdentifier(fld._1, acc, context), context)
    })
    result = pass.applyOnRecordType(TraversalDirection.Up, recordT, result, context)
    return result
  }
  def visitMapType(mapT : MapType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnMapType(TraversalDirection.Down, mapT, result, context)
    result = mapT.inTypes.foldLeft(result)((acc, t) => visitType(t, acc, context))
    result = visitType(mapT.outType, result, context)
    result = pass.applyOnMapType(TraversalDirection.Up, mapT, result, context)
    return result
  }
  def visitProcedureType(procT : ProcedureType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnProcedureType(TraversalDirection.Down, procT, result, context)
    result = procT.inTypes.foldLeft(result)((acc, t) => visitType(t, acc, context))
    result = procT.outTypes.foldLeft(result)((acc, t) => visitType(t, acc, context))
    result = pass.applyOnProcedureType(TraversalDirection.Up, procT, result, context)
    return result
  }
  def visitArrayType(arrT : ArrayType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnArrayType(TraversalDirection.Down, arrT, result, context)
    result = arrT.inTypes.foldLeft(result)((acc, t) => visitType(t, acc, context))
    result = visitType(arrT.outType, result, context)
    result = pass.applyOnArrayType(TraversalDirection.Up, arrT, result, context)
    return result
  }
  def visitSynonymType(synT : SynonymType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnSynonymType(TraversalDirection.Down, synT, result, context)
    result = visitIdentifier(synT.id, result, context)
    result = pass.applyOnSynonymType(TraversalDirection.Up, synT, result, context)
    return result
  }
  def visitExternalType(extT : ExternalType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnExternalType(TraversalDirection.Down, extT, result, context)
    result = visitIdentifier(extT.moduleId, result, context)
    result = visitIdentifier(extT.typeId, result, context)
    result = pass.applyOnExternalType(TraversalDirection.Up, extT, result, context)
    return result
  }
  def visitModuleInstanceType(instT : ModuleInstanceType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnModuleInstanceType(TraversalDirection.Down, instT, result, context)
    result = pass.applyOnModuleInstanceType(TraversalDirection.Up, instT, result, context)
    return result
  }
  def visitModuleType(modT : ModuleType, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnModuleType(TraversalDirection.Down, modT, result, context)
    result = pass.applyOnModuleType(TraversalDirection.Up, modT, result, context)
    return result
  }

  def visitProcedureSig(sig : ProcedureSig, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnProcedureSig(TraversalDirection.Down, sig, result, context)
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitIdentifier(inparam._1, acc, context))
    result = sig.inParams.foldLeft(result)((acc, inparam) => visitType(inparam._2, acc, context))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitIdentifier(outparam._1, acc, context))
    result = sig.outParams.foldLeft(result)((acc, outparam) => visitType(outparam._2, acc, context))
    result = pass.applyOnProcedureSig(TraversalDirection.Up, sig, result, context)
    return result
  }
  def visitFunctionSig(sig : FunctionSig, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnFunctionSig(TraversalDirection.Down, sig, result, context)
    result = sig.args.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc, context))
    result = sig.args.foldLeft(result)((acc, arg) => visitType(arg._2, acc, context))
    result = visitType(sig.retType, result, context)
    result = pass.applyOnFunctionSig(TraversalDirection.Up, sig, result, context)
    return result
  }
  def visitLocalVar(lvar : LocalVarDecl, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnLocalVar(TraversalDirection.Down, lvar, result, context)
    result = pass.applyOnLocalVar(TraversalDirection.Up, lvar, result, context)
    return result
  }
  def visitStatement(st : Statement, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnStatement(TraversalDirection.Down, st, result, context)
    result = st match {
      case skipStmt   : SkipStmt    => visitSkipStatement(skipStmt, result, context)
      case assertStmt : AssertStmt => visitAssertStatement(assertStmt, result, context)
      case assumeStmt : AssumeStmt => visitAssumeStatement(assumeStmt, result, context)
      case havocStmt  : HavocStmt => visitHavocStatement(havocStmt, result, context)
      case assignStmt : AssignStmt => visitAssignStatement(assignStmt, result, context)
      case ifElseStmt : IfElseStmt => visitIfElseStatement(ifElseStmt, result, context)
      case forStmt : ForStmt => visitForStatement(forStmt, result, context)
      case caseStmt : CaseStmt => visitCaseStatement(caseStmt, result, context)
      case procCallStmt : ProcedureCallStmt => visitProcedureCallStatement(procCallStmt, result, context)
      case modCallStmt : ModuleCallStmt => visitModuleCallStatement(modCallStmt, result, context)
    }
    result = pass.applyOnStatement(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitSkipStatement(st : SkipStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnSkip(TraversalDirection.Down, st, result, context)
    result = pass.applyOnSkip(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitAssertStatement(st : AssertStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnAssert(TraversalDirection.Down, st, result, context)
    result = st.id match {
      case None     => result
      case Some(id) => visitIdentifier(id, result, context)
    }
    result = visitExpr(st.e, result, context.withVerificationContext(AssertContext))
    result = pass.applyOnAssert(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitAssumeStatement(st : AssumeStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnAssume(TraversalDirection.Down, st, result, context)
    result = visitExpr(st.e, result, context.withVerificationContext(AssumeContext))
    result = pass.applyOnAssume(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitHavocStatement(st: HavocStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnHavoc(TraversalDirection.Down, st, result, context)
    result = visitIdentifier(st.id, result, context)
    result = pass.applyOnHavoc(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitAssignStatement(st : AssignStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnAssign(TraversalDirection.Down, st, result, context)
    result = st.lhss.foldLeft(result)((arg, i) => visitLhs(i, arg, context))
    result = st.rhss.foldLeft(result)((arg, i) => visitExpr(i, arg, context))
    result = pass.applyOnAssign(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitIfElseStatement(st : IfElseStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnIfElse(TraversalDirection.Down, st, result, context)
    result = visitExpr(st.cond, result, context)
    result = st.ifblock.foldLeft(result)((arg, i) => visitStatement(i, arg, context))
    result = st.elseblock.foldLeft(result)((arg, i) => visitStatement(i, arg, context))
    result = pass.applyOnIfElse(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitForStatement(st : ForStmt, in : T, contextIn : Scope) : T = {
    var result : T = in
    val context = contextIn + Scope.ForIndexVar(st.id, st.range._1.typeOf)
    result = pass.applyOnFor(TraversalDirection.Down, st, result, contextIn)
    result = visitIdentifier(st.id, result, contextIn)
    result = visitLiteral(st.range._1, result, contextIn)
    result = visitLiteral(st.range._2, result, contextIn)
    result = st.body.foldLeft(result)((arg, i) => visitStatement(i, arg, context))
    result = pass.applyOnFor(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitCaseStatement(st : CaseStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnCase(TraversalDirection.Down, st, result, context)
    result = st.body.foldLeft(result)(
      (arg1, cases) => {
        cases._2.foldLeft(visitExpr(cases._1, arg1, context))((arg2, i) => visitStatement(i, arg2, context))
      }
    )
    result = pass.applyOnCase(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitProcedureCallStatement(st : ProcedureCallStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnProcedureCall(TraversalDirection.Down, st, result, context)
    result = visitIdentifier(st.id, result, context)
    result = st.callLhss.foldLeft(result)((arg, i) => visitLhs(i, arg, context))
    result = st.args.foldLeft(result)((arg, i) => visitExpr(i, arg, context))
    result = pass.applyOnProcedureCall(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitModuleCallStatement(st : ModuleCallStmt, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnModuleCall(TraversalDirection.Down, st, result, context)
    result = visitIdentifier(st.id, result, context)
    result = pass.applyOnModuleCall(TraversalDirection.Up, st, result, context)
    return result
  }
  def visitLhs(lhs : Lhs, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnLHS(TraversalDirection.Down, lhs, result, context)
    result = visitIdentifier(lhs.ident, result, context)
    result = lhs match {
      case LhsId(id) => result
      case LhsArraySelect(id, indices) => indices.foldLeft(result)((acc, ind) => visitExpr(ind, acc, context))
      case LhsRecordSelect(id, fields) => fields.foldLeft(result)((acc, fld) => visitIdentifier(fld, acc, context))
      case LhsSliceSelect(id, slice) => visitBitVectorSlice(slice, result, context)
      case LhsVarSliceSelect(id, slice) => visitBitVectorSlice(slice, result, context)
    }
    result = pass.applyOnLHS(TraversalDirection.Up, lhs, result, context)
    return result
  }

  def visitBitVectorSlice(slice : BitVectorSlice, in : T, context : Scope) : T = {
    var result = pass.applyOnBitVectorSlice(TraversalDirection.Down, slice, in, context)
    slice match {
      case varSlice : VarBitVectorSlice =>
        result = visitExpr(varSlice.hi, result, context)
        result = visitExpr(varSlice.lo, result, context)
      case _ =>
    }
    result = pass.applyOnBitVectorSlice(TraversalDirection.Up, slice, result, context)
    return result
  }

  def visitExpr(e : Expr, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnExpr(TraversalDirection.Down, e, result, context)
    result = e match {
      case i : Identifier => visitIdentifier(i, result, context)
      case ei : ExternalIdentifier => visitExternalIdentifier(ei, result, context)
      case lit : Literal => visitLiteral(lit, result, context)
      case rec : Tuple => visitTuple(rec, result, context)
      case opapp : OperatorApplication => visitOperatorApp(opapp, result, context)
      case arrSel : ArraySelectOperation => visitArraySelectOp(arrSel, result, context)
      case arrUpd : ArrayStoreOperation => visitArrayStoreOp(arrUpd, result, context)
      case fapp : FuncApplication => visitFuncApp(fapp, result, context)
      case ite : ITE => visitITE(ite, result, context)
      case lambda : Lambda => visitLambda(lambda, result, context)
    }
    result = pass.applyOnExpr(TraversalDirection.Up, e, result, context)
    return result
  }
  def visitIdentifier(id : Identifier, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnIdentifier(TraversalDirection.Down, id, result, context)
    result = pass.applyOnIdentifier(TraversalDirection.Up, id, result, context)
    return result
  }
  def visitExternalIdentifier(eId : ExternalIdentifier, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnExternalIdentifier(TraversalDirection.Down, eId, result, context)
    result = pass.applyOnExternalIdentifier(TraversalDirection.Up, eId, result, context)
    return result
  }
  def visitLiteral(lit : Literal, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnLit(TraversalDirection.Down, lit, result, context)
    result = lit match {
      case f : FreshLit => visitFreshLiteral(f, result, context)
      case b : BoolLit => visitBoolLiteral(b, result, context)
      case n : NumericLit => visitNumericLit(n, result, context)
    }
    result = pass.applyOnLit(TraversalDirection.Up, lit, result, context)
    return result
  }
  def visitFreshLiteral(f : FreshLit, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnFreshLit(TraversalDirection.Down, f, result, context)
    result = pass.applyOnFreshLit(TraversalDirection.Up, f, result, context)
    return result
  }
  def visitBoolLiteral(b : BoolLit, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnBoolLit(TraversalDirection.Down, b, result, context)
    result = pass.applyOnBoolLit(TraversalDirection.Up, b, result, context)
    return result
  }
  def visitNumericLit(n : NumericLit, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnNumericLit(TraversalDirection.Down, n, result, context)
    n match {
      case i : IntLit =>
        result = pass.applyOnIntLit(TraversalDirection.Down, i, result, context)
        result = pass.applyOnIntLit(TraversalDirection.Up, i, result, context)
      case bv : BitVectorLit =>
        result = pass.applyOnBitVectorLit(TraversalDirection.Down, bv, result, context)
        result = pass.applyOnBitVectorLit(TraversalDirection.Up, bv, result, context)
    }
    result = pass.applyOnNumericLit(TraversalDirection.Up, n, result, context)
    return result
  }
  def visitIntLiteral(i : IntLit, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnIntLit(TraversalDirection.Down, i, result, context)
    result = pass.applyOnIntLit(TraversalDirection.Up, i, result, context)
    return result
  }
  def visitBitVectorLiteral(bv : BitVectorLit, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnBitVectorLit(TraversalDirection.Down, bv, result, context)
    result = pass.applyOnBitVectorLit(TraversalDirection.Up, bv, result, context)
    return result
  }
  def visitTuple(rec : Tuple, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnTuple(TraversalDirection.Down, rec, result, context)
    result = rec.values.foldLeft(result)((acc, i) => visitExpr(i, acc, context))
    result = pass.applyOnTuple(TraversalDirection.Up, rec, result, context)
    return result
  }
  def visitOperatorApp(opapp : OperatorApplication, in : T, contextIn : Scope) : T = {
    var result : T = in
    result = pass.applyOnOperatorApp(TraversalDirection.Down, opapp, result, contextIn)
    result = visitOperator(opapp.op, result, contextIn)
    result = opapp.operands.foldLeft(result)((acc, i) => visitExpr(i, acc, contextIn + opapp))
    result = pass.applyOnOperatorApp(TraversalDirection.Up, opapp, result, contextIn)
    return result
  }
  def visitOperator(op : Operator, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnOperator(TraversalDirection.Down, op, result, context)
    lazy val quantifierCtx = context + op
    op match {
      case ConstExtractOp(slice) =>
        result = visitBitVectorSlice(slice, result, context)
      case VarExtractOp(slice) =>
        result = visitBitVectorSlice(slice, result, context)
      case ForallOp(args) =>
        result = visitQuantifierArgs(args, result, quantifierCtx)
      case ExistsOp(args) =>
        result = visitQuantifierArgs(args, result, quantifierCtx)
      case _ =>
    }
    result = pass.applyOnOperator(TraversalDirection.Up, op, result, context)
    return result
  }
  def visitQuantifierArgs(args : List[(Identifier, Type)], in : T, context : Scope) : T = {
    args.foldLeft(in) {
      (acc, arg) => {
        val accP1 = visitIdentifier(arg._1, acc, context)
        val accP2 = visitType(arg._2, accP1, context)
        accP2
      }
    }
  }
  def visitArraySelectOp(arrSel : ArraySelectOperation, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnArraySelect(TraversalDirection.Down, arrSel, result, context)
    result = visitExpr(arrSel.e, result, context)
    result = arrSel.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc, context))
    result = pass.applyOnArraySelect(TraversalDirection.Up, arrSel, result, context)
    return result
  }
  def visitArrayStoreOp(arrStore : ArrayStoreOperation, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnArrayStore(TraversalDirection.Down, arrStore, result, context)
    result = visitExpr(arrStore.e, result, context)
    result = arrStore.index.foldLeft(result)((acc, arg) => visitExpr(arg, acc, context))
    result = visitExpr(arrStore.value, result, context)
    result = pass.applyOnArrayStore(TraversalDirection.Up, arrStore, result, context)
    return result
  }
  def visitFuncApp(fapp : FuncApplication, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnFuncApp(TraversalDirection.Down, fapp, result, context)
    result = visitExpr(fapp.e, result, context)
    result = fapp.args.foldLeft(result)((acc, arg) => visitExpr(arg, acc, context))
    result = pass.applyOnFuncApp(TraversalDirection.Up, fapp, result, context)
    return result
  }
  def visitITE(ite: ITE, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnITE(TraversalDirection.Down, ite, result, context)
    result = visitExpr(ite.e, result, context)
    result = visitExpr(ite.t, result, context)
    result = visitExpr(ite.f, result, context)
    result = pass.applyOnITE(TraversalDirection.Up, ite, result, context)
    return result
  }
  def visitLambda(lambda: Lambda, in : T, contextIn : Scope) : T = {
    var result : T = in
    val context = contextIn + lambda
    result = pass.applyOnLambda(TraversalDirection.Down, lambda, result, contextIn)
    result = lambda.ids.foldLeft(result)((acc, arg) => visitIdentifier(arg._1, acc, context))
    result = lambda.ids.foldLeft(result)((acc, arg) => visitType(arg._2, acc, context))
    result = visitExpr(lambda.e, result, context)
    result = pass.applyOnLambda(TraversalDirection.Up, lambda, result, contextIn)
    return result
  }
  def visitExprDecorator(dec : ExprDecorator, in : T, context : Scope) : T = {
    var result : T = in
    result = pass.applyOnExprDecorator(TraversalDirection.Down, dec, result, context)
    result = pass.applyOnExprDecorator(TraversalDirection.Up, dec, result, context)
    return result
  }
}


class ASTRewriter (_passName : String, _pass: RewritePass, setFilename : Boolean = true, setPosition : Boolean = true) extends ASTAnalysis {
  // Set a backpo inter to here from the pass.
  _pass._analysis = Some(this)

  def pass = _pass
  override def passName = _passName
  def _setFilename = setFilename
  override def visit(module : Module, context : Scope) : Option[Module] = visitModule(module, context)

  override def reset() {
    pass.reset()
  }

  def visitModule(module : Module, initContext : Scope) : Option[Module] = {
    val context = initContext + module
    val id = visitIdentifier(module.id, context)
    val decls = module.decls.map(visitDecl(_, context)).flatten
    val initR : (List[Option[GenericProofCommand]], Scope) = (List.empty, initContext)
    val cmds = module.cmds.foldRight(initR)((cmd, acc) => (visitCommand(cmd, acc._2) :: acc._1, acc._2 + cmd))._1.flatten
    val moduleIn = id.flatMap((i) => Some(Module(i, decls, cmds)))
    val moduleP = moduleIn.flatMap((m) => pass.rewriteModule(m, initContext))

    return (ASTNode.introducePos(setPosition, setFilename, moduleP, module.position) match {
      case Some(m) =>
        module.filename match {
          case Some(fn) => Some(m.withFilename(fn))
          case None     => Some(m)
        }
      case None =>
        None
    })
  }

  def visitDecl(decl : Decl, context : Scope) : Option[Decl] = {
    val declP = (decl match {
      case instDecl : InstanceDecl => visitInstance(instDecl, context)
      case procDecl : ProcedureDecl => visitProcedure(procDecl, context)
      case typeDecl : TypeDecl => visitTypeDecl(typeDecl, context)
      case stateVars : StateVarsDecl => visitStateVars(stateVars, context)
      case inputVars : InputVarsDecl => visitInputVars(inputVars, context)
      case outputVars : OutputVarsDecl => visitOutputVars(outputVars, context)
      case sharedVars : SharedVarsDecl => visitSharedVars(sharedVars, context)
      case constDecl : ConstantsDecl => visitConstants(constDecl, context)
      case funcDecl : FunctionDecl => visitFunction(funcDecl, context)
      case synFuncDecl : SynthesisFunctionDecl => visitSynthesisFunction(synFuncDecl, context)
      case defDecl : DefineDecl => visitDefine(defDecl, context)
      case initDecl : InitDecl => visitInit(initDecl, context)
      case nextDecl : NextDecl => visitNext(nextDecl, context)
      case specDecl : SpecDecl => visitSpec(specDecl, context)
      case axiomDecl : AxiomDecl => visitAxiom(axiomDecl, context)
    }).flatMap(pass.rewriteDecl(_, context))
    return ASTNode.introducePos(setPosition, setFilename, declP, decl.position)
  }

  def visitInstance(inst : InstanceDecl, context : Scope) : Option[InstanceDecl] = {
    val instIdP = visitIdentifier(inst.instanceId, context)
    val modIdP = visitIdentifier(inst.moduleId, context)
    val argP = inst.arguments.map {
      (a) => a._2 match {
          case Some(e) => (a._1, visitExpr(e, context))
          case None => (a._1, None)
        }
      }
    val instTP = inst.instType.flatMap((t) => visitType(t, context)).flatMap {
      (t) => t match {
        case tp : ModuleInstanceType => Some(tp)
        case _ => None
      }
    }
    val modTP = inst.modType.flatMap((t) => visitType(t, context)).flatMap {
      (t) => t match {
        case tp : ModuleType => Some(tp)
        case _ => None
      }
    }
    val instP = (instIdP, modIdP) match {
      case (Some(instId), Some(modId)) =>
        pass.rewriteInstance(InstanceDecl(instId, modId, argP, instTP, modTP), context)
      case _ =>
        None
    }
    return ASTNode.introducePos(setPosition, setFilename, instP, inst.position)
  }

  def visitProcedure(proc : ProcedureDecl, contextIn : Scope) : Option[ProcedureDecl] = {
    val context = contextIn + proc
    val id = visitIdentifier(proc.id, context)
    val sig = visitProcedureSig(proc.sig, context)
    val decls = proc.decls.map(visitLocalVar(_, context)).flatten
    val stmts = proc.body.map(visitStatement(_, context)).flatten
    val reqs = proc.requires.map(r => visitExpr(r, context.withVerificationContext(RequiresContext))).flatten
    val enss = proc.ensures.map(e => visitExpr(e, context.withVerificationContext(EnsuresContext))).flatten
    val mods = proc.modifies.map(v => visitIdentifier(v, context)).flatten
    val procP = (id, sig) match {
      case (Some(i), Some(s)) => pass.rewriteProcedure(ProcedureDecl(i, s, decls, stmts, reqs, enss, mods), contextIn)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, procP, proc.position)
  }

  def visitFunction(func : FunctionDecl, context : Scope) : Option[FunctionDecl] = {
    val id = visitIdentifier(func.id, context)
    val sig = visitFunctionSig(func.sig, context)
    val funcP = (id, sig) match {
      case (Some(i), Some(s)) => pass.rewriteFunction(FunctionDecl(i, s), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, funcP, func.position)
  }

  def visitSynthesisFunction(synFunc : SynthesisFunctionDecl, context : Scope) : Option[SynthesisFunctionDecl] = {
    val idP = visitIdentifier(synFunc.id, context)
    val sigP = visitFunctionSig(synFunc.sig, context)
    val contextP = context + synFunc.sig
    // FIXME
    val conditionsP = synFunc.conditions
    val gIdP = synFunc.grammarId
    (idP, sigP) match {
      case (Some(id), Some(sig)) =>
        val synFuncP = SynthesisFunctionDecl(id, sig, gIdP, conditionsP)
        pass.rewriteSynthesisFunction(synFuncP, context)
      case _ => None
    }
  }

  def visitDefine(defDecl : DefineDecl, context : Scope) : Option[DefineDecl] = {
    val idP = visitIdentifier(defDecl.id, context)
    val sigP = visitFunctionSig(defDecl.sig, context)
    val contextP = context + defDecl.sig
    val exprP = visitExpr(defDecl.expr, contextP)
    (idP, sigP, exprP) match {
      case (Some(id), Some(sig), Some(expr)) =>
        val defDeclP = DefineDecl(id, sig, expr)
        pass.rewriteDefine(defDeclP, context)
      case _ =>
        None
    }
  }
  def visitStateVars(stVars : StateVarsDecl, context : Scope) : Option[StateVarsDecl] = {
    val idsP = (stVars.ids.map((id) => visitIdentifier(id, context))).flatten
    val typP = visitType(stVars.typ, context)
    val stateVarsP = if (idsP.size > 0 && typP.isDefined) {
      pass.rewriteStateVars(StateVarsDecl(idsP, typP.get), context)
    } else {
      None
    }
    return ASTNode.introducePos(setPosition, setFilename, stateVarsP, stVars.position)
  }

  def visitInputVars(inpVars : InputVarsDecl, context : Scope) : Option[InputVarsDecl] = {
    val idsP = (inpVars.ids.map((id) => visitIdentifier(id, context))).flatten
    val typP = visitType(inpVars.typ, context)
    val inpVarsP = if (idsP.size > 0 && typP.isDefined) {
      pass.rewriteInputVars(InputVarsDecl(idsP, typP.get), context)
    } else {
      None
    }
    return ASTNode.introducePos(setPosition, setFilename, inpVarsP, inpVars.position)
  }


  def visitOutputVars(outVars : OutputVarsDecl, context : Scope) : Option[OutputVarsDecl] = {
    val idsP = (outVars.ids.map((id) => visitIdentifier(id, context))).flatten
    val typP = visitType(outVars.typ, context)
    val outVarsP = if (idsP.size > 0 && typP.isDefined) {
      pass.rewriteOutputVars(OutputVarsDecl(idsP, typP.get), context)
    } else {
      None
    }
    return ASTNode.introducePos(setPosition, setFilename, outVarsP, outVars.position)
  }

  def visitSharedVars(sharedVars : SharedVarsDecl, context : Scope) : Option[SharedVarsDecl] = {
    val idsP = (sharedVars.ids.map((id) => visitIdentifier(id, context))).flatten
    val typP = visitType(sharedVars.typ, context)
    val sharedVarsP = if (idsP.size > 0 && typP.isDefined) {
      pass.rewriteSharedVars(SharedVarsDecl(idsP, typP.get), context)
    } else {
      None
    }
    return ASTNode.introducePos(setPosition, setFilename, sharedVarsP, sharedVars.position)
  }

  def visitConstants(cnst : ConstantsDecl, context : Scope) : Option[ConstantsDecl] = {
    val idsP = cnst.ids.map(id => visitIdentifier(id, context)).flatten
    val typP = visitType(cnst.typ, context)
    val cnstP = typP match {
      case Some(typ) => pass.rewriteConstant(ConstantsDecl(idsP, typ), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, cnstP, cnst.position)
  }

  def visitSpec(spec : SpecDecl, context : Scope) : Option[SpecDecl] = {
    val contextP = if (spec.params.contains(LTLExprDecorator)) {
      context.withLTLSpec
    } else {
      context
    }
    val idP = visitIdentifier(spec.id, context)
    val exprP = visitExpr(spec.expr, contextP.withVerificationContext(SpecContext))
    val decsP = spec.params.map(visitExprDecorator(_, context)).flatten
    val specP = (idP, exprP) match {
      case (Some(id), Some(expr)) => pass.rewriteSpec(SpecDecl(id, expr, decsP), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, specP, spec.position)
  }

  def visitAxiom(axiom : AxiomDecl, context : Scope) : Option[AxiomDecl] = {
    val idP = axiom.id.flatMap((id) => visitIdentifier(id, context))
    val exprP = visitExpr(axiom.expr, context.withVerificationContext(AxiomContext))
    val axiomP = exprP.flatMap((e) => pass.rewriteAxiom(AxiomDecl(idP, e), context))
    return ASTNode.introducePos(setPosition, setFilename, axiomP, axiom.position)
  }
  def visitTypeDecl(typDec : TypeDecl, context : Scope) : Option[TypeDecl] = {
    val idP = visitIdentifier(typDec.id, context)
    val typeP = visitType(typDec.typ, context)
    val typDecP = (idP, typeP) match {
      case (Some(id), Some(typ)) => pass.rewriteTypeDecl(TypeDecl(id, typ), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, typDecP, typDec.position)
  }

  def visitInit(init : InitDecl, context : Scope) : Option[InitDecl] = {
    val body = init.body.map(visitStatement(_, context)).flatten
    val initP = pass.rewriteInit(InitDecl(body), context)
    return ASTNode.introducePos(setPosition, setFilename, initP, init.position)
  }

  def visitNext(next : NextDecl, context : Scope) : Option[NextDecl] = {
    val body = next.body.map(visitStatement(_, context)).flatten
    val nextP = pass.rewriteNext(NextDecl(body), context)
    return ASTNode.introducePos(setPosition, setFilename, nextP, next.position)
  }

  def visitCommand(cmd : GenericProofCommand, context : Scope) : Option[GenericProofCommand] = {
    val contextP = cmd.getContext(context + cmd)
    val argsP = cmd.args.map(e => visitExpr(e, contextP)).flatten
    val resultVarP = cmd.resultVar.flatMap(r => visitIdentifier(r, contextP))
    val argObjP = cmd.argObj.flatMap(r => visitIdentifier(r, contextP))
    val cmdP = pass.rewriteCommand(GenericProofCommand(cmd.name, cmd.params, argsP, resultVarP, argObjP), context)
    return ASTNode.introducePos(setPosition, setFilename, cmdP, cmd.position)
  }

  def visitType(typ: Type, context : Scope) : Option[Type] = {
    val typP = (typ match {
      case undefT : UndefinedType => visitUndefinedType(undefT, context)
      case unintT : UninterpretedType => visitUninterpretedType(unintT, context)
      case boolT : BooleanType => visitBoolType(boolT, context)
      case intT : IntegerType => visitIntType(intT, context)
      case bvT : BitVectorType => visitBitVectorType(bvT, context)
      case enumT : EnumType => visitEnumType(enumT, context)
      case tupleT : TupleType => visitTupleType(tupleT, context)
      case recT : RecordType => visitRecordType(recT, context)
      case mapT : MapType => visitMapType(mapT, context)
      case procT : ProcedureType => visitProcedureType(procT, context)
      case arrT : ArrayType => visitArrayType(arrT, context)
      case synT : SynonymType => visitSynonymType(synT, context)
      case extT : ExternalType => visitExternalType(extT, context)
      case instT : ModuleInstanceType => visitModuleInstanceType(instT, context)
      case modT : ModuleType => visitModuleType(modT, context)
    }).flatMap(pass.rewriteType(_, context))
    return ASTNode.introducePos(setPosition, setFilename, typP, typ.position)
  }

  def visitUndefinedType(undefT : UndefinedType, context : Scope) : Option[Type] = {
    val undefTP = pass.rewriteUndefinedType(undefT, context)
    return ASTNode.introducePos(setPosition, setFilename, undefTP, undefT.position)
  }

  def visitUninterpretedType(unintT : UninterpretedType, context : Scope) : Option[UninterpretedType] = {
    val unintTP = pass.rewriteUninterpretedType(unintT, context)
    return ASTNode.introducePos(setPosition, setFilename, unintTP, unintT.position)
  }

  def visitBoolType(boolT : BooleanType, context : Scope) : Option[BooleanType] = {
    val boolTP = pass.rewriteBoolType(boolT, context)
    return ASTNode.introducePos(setPosition, setFilename, boolTP, boolT.position)
  }

  def visitIntType(intT : IntegerType, context : Scope) : Option[IntegerType] = {
    val intTP = pass.rewriteIntType(intT, context)
    return ASTNode.introducePos(setPosition, setFilename, intTP, intT.position)
  }

  def visitBitVectorType(bvT : BitVectorType, context : Scope) : Option[BitVectorType] = {
    val bvTP = pass.rewriteBitVectorType(bvT, context)
    return ASTNode.introducePos(setPosition, setFilename, bvTP, bvT.position)
  }

  def visitEnumType(enumT : EnumType, context : Scope) : Option[EnumType] = {
    val idP = enumT.ids.map(visitIdentifier(_, context)).flatten
    val enumTP = pass.rewriteEnumType(EnumType(idP), context)
    return ASTNode.introducePos(setPosition, setFilename, enumTP, enumT.position)
  }

  def visitTupleType(tupleT : TupleType, context : Scope) : Option[TupleType] = {
    val fieldsP = tupleT.fieldTypes.map((t) => visitType(t, context)).flatten
    val tupleTP = pass.rewriteTupleType(TupleType(fieldsP), context)
    return ASTNode.introducePos(setPosition, setFilename, tupleTP, tupleT.position)
  }

  def visitRecordType(recT : RecordType, context : Scope) : Option[RecordType] = {
    val fieldsP = recT.fields.map((f) => {
      (visitIdentifier(f._1, context), visitType(f._2, context)) match {
        case (Some(i), Some(t)) => Some((i,t))
        case _ => None
      }
    }).flatten
    val recTP = pass.rewriteRecordType(RecordType(fieldsP), context)
    return ASTNode.introducePos(setPosition, setFilename, recTP, recT.position)
  }

  def visitMapType(mapT : MapType, context : Scope) : Option[MapType] = {
    val inTypesP = mapT.inTypes.map(visitType(_, context)).flatten
    val mapTP = (visitType(mapT.outType, context)) match {
      case Some(outTypeP) => pass.rewriteMapType(MapType(inTypesP, outTypeP), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, mapTP, mapT.position)
  }

  def visitProcedureType(procT : ProcedureType, context : Scope) : Option[ProcedureType] = {
    val inTypesP = procT.inTypes.map(visitType(_, context)).flatten
    val outTypesP = procT.outTypes.map(visitType(_, context)).flatten
    val procTP1 = ProcedureType(inTypesP, outTypesP)
    val procTP = pass.rewriteProcedureType(procTP1, context)
    return ASTNode.introducePos(setPosition, setFilename, procTP, procT.position)
  }

  def visitArrayType(arrT : ArrayType, context : Scope) : Option[ArrayType] = {
    val inTypesP = arrT.inTypes.map(visitType(_, context)).flatten
    val arrTP = (visitType(arrT.outType, context)) match {
      case Some(outTypeP) => pass.rewriteArrayType(ArrayType(inTypesP, outTypeP), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, arrTP, arrT.position)
  }

  def visitSynonymType(synT : SynonymType, context : Scope) : Option[Type] = {
    val idP = visitIdentifier(synT.id, context)
    val synTP = idP.flatMap(id => pass.rewriteSynonymType(SynonymType(id), context))
    return ASTNode.introducePos(setPosition, setFilename, synTP, synT.position)
  }

  def visitExternalType(extT : ExternalType, context : Scope) : Option[Type] = {
    val moduleIdP = visitIdentifier(extT.moduleId, context)
    val typeIdP = visitIdentifier(extT.typeId, context)
    val extTP = (moduleIdP, typeIdP) match {
      case (Some(moduleId), Some(typeId)) =>
        pass.rewriteExternalType(ExternalType(moduleId, typeId), context)
      case _ =>
        None
    }
    return ASTNode.introducePos(setPosition, setFilename, extTP, extT.position)
  }

  def visitModuleInstanceType(instT : ModuleInstanceType, context : Scope) : Option[ModuleInstanceType] = {
    val instTP = pass.rewriteModuleInstanceType(instT, context)
    return ASTNode.introducePos(setPosition, setFilename, instTP, instT.position)
  }

  def visitModuleType(modT : ModuleType, context : Scope) : Option[ModuleType] = {
    val modTP = pass.rewriteModuleType(modT, context)
    return ASTNode.introducePos(setPosition, setFilename, modTP, modT.position)
  }

  def visitProcedureSig(sig : ProcedureSig, context : Scope) : Option[ProcedureSig] = {
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

    val sigP = (inParamsP, outParamsP) match {
      case (in, out) => pass.rewriteProcedureSig(ProcedureSig(in, out), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, sigP, sig.position)
  }

  def visitFunctionSig(sig : FunctionSig, context : Scope) : Option[FunctionSig] = {
    val args : List[(Identifier, Type)] = sig.args.map((inP) => {
      (visitIdentifier(inP._1, context), visitType(inP._2, context)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    val sigP = visitType(sig.retType, context).flatMap((t) => pass.rewriteFunctionSig(FunctionSig(args, t), context))
    return ASTNode.introducePos(setPosition, setFilename, sigP, sig.position)
  }

  def visitLocalVar(lvar : LocalVarDecl, context : Scope) : Option[LocalVarDecl] = {
    val varP = visitIdentifier(lvar.id, context).flatMap((id) => {
      visitType(lvar.typ, context).flatMap((t) => pass.rewriteLocalVar(LocalVarDecl(id, t), context))
    })
    return ASTNode.introducePos(setPosition, setFilename, varP, lvar.position)
  }

  def visitStatement(st : Statement, context : Scope) : List[Statement] = {
    val stP = (st match {
      case skipStmt : SkipStmt => visitSkipStatement(skipStmt, context)
      case assertStmt : AssertStmt => visitAssertStatement(assertStmt, context)
      case assumeStmt : AssumeStmt => visitAssumeStatement(assumeStmt, context)
      case havocStmt : HavocStmt => visitHavocStatement(havocStmt, context)
      case assignStmt : AssignStmt => visitAssignStatement(assignStmt, context)
      case ifElseStmt : IfElseStmt => visitIfElseStatement(ifElseStmt, context)
      case forStmt : ForStmt => visitForStatement(forStmt, context)
      case caseStmt : CaseStmt => visitCaseStatement(caseStmt, context)
      case procCallStmt : ProcedureCallStmt => visitProcedureCallStatement(procCallStmt, context)
      case modCallStmt : ModuleCallStmt => visitModuleCallStatement(modCallStmt, context)
    }).flatMap(pass.rewriteStatement(_, context))
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitSkipStatement(st : SkipStmt, context : Scope) : List[Statement] = {
    val stP = pass.rewriteSkip(st, context)
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitAssertStatement(st : AssertStmt, context : Scope) : List[Statement] = {
    val idP = st.id.flatMap(id => visitIdentifier(id, context))
    val stP = visitExpr(st.e, context.withVerificationContext(AssertContext)).toList.flatMap((e) => {
      pass.rewriteAssert(AssertStmt(e, idP), context)
    })
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitAssumeStatement(st : AssumeStmt, context : Scope) : List[Statement] = {
    val idP = st.id.flatMap(id => visitIdentifier(id, context))
    val stP = visitExpr(st.e, context.withVerificationContext(AssumeContext)).toList.flatMap((e) => {
      pass.rewriteAssume(AssumeStmt(e, idP), context)
    })
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitHavocStatement(st: HavocStmt, context : Scope) : List[Statement] = {
    val stP = visitIdentifier(st.id, context).toList.flatMap((id) => {
      pass.rewriteHavoc(HavocStmt(id), context)
    })
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitAssignStatement(st : AssignStmt, context : Scope) : List[Statement] = {
    val lhss = st.lhss.map(visitLhs(_, context)).flatten
    val rhss = st.rhss.map(visitExpr(_, context)).flatten
    val stP = pass.rewriteAssign(AssignStmt(lhss, rhss), context)
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitIfElseStatement(st : IfElseStmt, context : Scope) : List[Statement] = {
    val cond = visitExpr(st.cond, context)
    val ifblock = st.ifblock.map(visitStatement(_, context)).flatten
    val elseblock = st.elseblock.map(visitStatement(_, context)).flatten
    val stP = cond match {
      case Some(c) => pass.rewriteIfElse(IfElseStmt(c, ifblock, elseblock), context)
      case _ => List.empty[Statement]
    }
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitForStatement(st : ForStmt, contextIn : Scope) : List[Statement] = {
    val context = contextIn + Scope.ForIndexVar(st.id, st.range._1.typeOf)
    val idP = visitIdentifier(st.id, contextIn)
    val lit1P = visitNumericLiteral(st.range._1, contextIn)
    val lit2P = visitNumericLiteral(st.range._2, contextIn)
    val stmts = st.body.map(visitStatement(_, context)).flatten

    val stP = (idP, lit1P, lit2P) match {
      case (Some(id), Some(lit1), Some(lit2)) => pass.rewriteFor(ForStmt(id, (lit1, lit2), stmts), contextIn)
      case _ => List.empty[Statement]
    }
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitCaseStatement(st : CaseStmt, context : Scope) : List[Statement] = {
    val bodyP = st.body.map((c) => {
      // if rewriting the expression doesn't produce None.
      visitExpr(c._1, context).flatMap((e) => {
        // then rewrite each of statements associated with the case expression.
        Some(e, c._2.map(visitStatement(_, context)).flatten)
      })
    }).flatten // and finally get rid of all the Options.
    val stP = pass.rewriteCase(CaseStmt(bodyP), context)
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitProcedureCallStatement(st : ProcedureCallStmt, context : Scope) : List[Statement] = {
    val idP = visitIdentifier(st.id, context)
    val lhssP = st.callLhss.map(visitLhs(_, context)).flatten
    val argsP = st.args.map(visitExpr(_, context)).flatten
    val stP = idP.toList.flatMap((id) => pass.rewriteProcedureCall(ProcedureCallStmt(id, lhssP, argsP), context))
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitModuleCallStatement(st : ModuleCallStmt,  context : Scope) : List[Statement] = {
    val stP = visitIdentifier(st.id, context) match {
      case Some(id) =>
        val stP1 = ModuleCallStmt(id)
        pass.rewriteModuleCall(stP1, context)
      case None =>
        List.empty
    }
    return ASTNode.introducePos(setPosition, setFilename, stP, st.position)
  }

  def visitLhs(lhs : Lhs, context : Scope) : Option[Lhs] = {
    val lhsIdP = visitIdentifier(lhs.ident, context)
    def newLhsSliceSelect(id : Identifier, slice : BitVectorSlice) = {
      slice match {
        case constBvSlice : ConstBitVectorSlice => LhsSliceSelect(id, constBvSlice)
        case varBvSlice : VarBitVectorSlice => LhsVarSliceSelect(id, varBvSlice)
      }
    }
    val lhsP = lhsIdP.flatMap{(id) =>
      val lhsP1 : Option[Lhs] = lhs match {
        case LhsId(_) => Some(LhsId(id))
        case LhsArraySelect(_, indices) =>
          Some(LhsArraySelect(id, indices.map(visitExpr(_, context)).flatten))
        case LhsRecordSelect(_, fields) =>
          Some(LhsRecordSelect(id, fields.map(visitIdentifier(_, context)).flatten))
        case LhsSliceSelect(id, slice) =>
          val sliceP = visitBitVectorSlice(slice, context)
          sliceP.flatMap((s) => Some(newLhsSliceSelect(id, s)))
        case LhsVarSliceSelect(_, slice) =>
          val sliceP = visitBitVectorSlice(slice, context)
          sliceP.flatMap((s) => Some(newLhsSliceSelect(id, s)))
      }
      lhsP1.flatMap((lhsP) => pass.rewriteLHS(lhsP, context))
    }
    return ASTNode.introducePos(setPosition, setFilename, lhsP, lhs.position)
  }

  def visitBitVectorSlice(slice : BitVectorSlice, context : Scope) : Option[BitVectorSlice] = {
    slice match {
      case varBvSlice : VarBitVectorSlice =>
        var hiP = visitExpr(varBvSlice.hi, context)
        var loP = visitExpr(varBvSlice.lo, context)

        (hiP, loP) match {
          case (Some(hi), Some(lo)) =>
            pass.rewriteBitVectorSlice(VarBitVectorSlice(hi, lo, varBvSlice.wd), context)
          case _ =>
            None
        }
      case constBvSlice : ConstBitVectorSlice =>
        pass.rewriteBitVectorSlice(constBvSlice, context)
    }
  }

  def visitExpr(e : Expr, context : Scope) : Option[Expr] = {
    val eP = (e match {
      case i : Identifier => visitIdentifier(i, context)
      case eId : ExternalIdentifier => visitExternalIdentifier(eId, context)
      case lit : Literal => visitLiteral(lit, context)
      case rec : Tuple => visitTuple(rec, context)
      case opapp : OperatorApplication => visitOperatorApp(opapp, context)
      case arrSel : ArraySelectOperation => visitArraySelectOp(arrSel, context)
      case arrUpd : ArrayStoreOperation => visitArrayStoreOp(arrUpd, context)
      case fapp : FuncApplication => visitFuncApp(fapp, context)
      case ite : ITE => visitITE(ite, context)
      case lambda : Lambda => visitLambda(lambda, context)
    }).flatMap(pass.rewriteExpr(_, context))
    return ASTNode.introducePos(setPosition, setFilename, eP, e.position)
  }

  def visitIdentifier(id : Identifier, context : Scope) : Option[Identifier] = {
    val idP = pass.rewriteIdentifier(id, context)
    return ASTNode.introducePos(setPosition, setFilename, idP, id.position)
  }

  def visitExternalIdentifier(eId : ExternalIdentifier, context : Scope) : Option[Expr] = {
    val eIdP = pass.rewriteExternalIdentifier(eId, context)
    return ASTNode.introducePos(setPosition, setFilename, eIdP, eId.position)
  }

  def visitLiteral(lit : Literal, context : Scope) : Option[Expr] = {
    val litP = (lit match {
      case f : FreshLit => visitFreshLiteral(f, context)
      case b : BoolLit => visitBoolLiteral(b, context)
      case n : NumericLit => visitNumericLiteral(n, context)
    }).flatMap{
      case l : Literal => pass.rewriteLit(l, context)
      case e : Expr => pass.rewriteExpr(e, context)
      case _ => None // should never get here!
    }
    return ASTNode.introducePos(setPosition, setFilename, litP, lit.position)
  }

  def visitFreshLiteral(f : FreshLit, context : Scope) : Option[Expr] = {
    val fP = pass.rewriteFreshLit(f, context)
    return ASTNode.introducePos(setPosition, setFilename, fP, f.position)
  }
  def visitBoolLiteral(b : BoolLit, context : Scope) : Option[BoolLit] = {
    val bP = pass.rewriteBoolLit(b, context)
    return ASTNode.introducePos(setPosition, setFilename, bP, b.position)
  }

  def visitNumericLiteral(n : NumericLit, context : Scope) : Option[NumericLit] = {
    val nP1 = n match {
      case bv : BitVectorLit => visitBitVectorLiteral(bv, context)
      case i : IntLit => visitIntLiteral(i, context)
    }
    val nP2 = nP1.flatMap(pass.rewriteNumericLit(_, context))
    return ASTNode.introducePos(setPosition, setFilename, nP2, n.position)
  }

  def visitIntLiteral(i : IntLit, context : Scope) : Option[IntLit] = {
    val iP = pass.rewriteIntLit(i, context)
    return ASTNode.introducePos(setPosition, setFilename, iP, i.position)
  }

  def visitBitVectorLiteral(bv : BitVectorLit, context : Scope) : Option[BitVectorLit] = {
    val bvP = pass.rewriteBitVectorLit(bv, context)
    return ASTNode.introducePos(setPosition, setFilename, bvP, bv.position)
  }

  def visitTuple(rec : Tuple, context : Scope) : Option[Tuple] = {
    val recP = pass.rewriteTuple(Tuple(rec.values.map(visitExpr(_, context)).flatten), context)
    return ASTNode.introducePos(setPosition, setFilename, recP, rec.position)
  }

  def visitOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    val opAppP = visitOperator(opapp.op, context).flatMap((op) => {
      pass.rewriteOperatorApp(OperatorApplication(op, opapp.operands.map(visitExpr(_, context + opapp)).flatten), context)
    })
    return ASTNode.introducePos(setPosition, setFilename, opAppP, opapp.position)
  }

  def visitOperator(op : Operator, context : Scope) : Option[Operator] = {
    def newExtractOp(slice : BitVectorSlice) : ExtractOp = {
      slice match {
        case constBvSlice : ConstBitVectorSlice => ConstExtractOp(constBvSlice)
        case varBvSlice : VarBitVectorSlice => VarExtractOp(varBvSlice)
      }
    }
    def rewriteQuantifiedVars(args : List[(Identifier, Type)]) = {
      val ctxP = context + op
      args.map {
        (a) => {
          val idP = visitIdentifier(a._1, ctxP)
          val typeP = visitType(a._2, ctxP)
          (idP, typeP) match {
            case (Some(id), Some(typ)) => Some((id, typ))
            case _ => None
          }
        }
      }.flatten
    }

    val opP : Option[Operator] = op match {
      case ConstExtractOp(slice) =>
        val sliceP = visitBitVectorSlice(slice, context)
        val extractOp = sliceP.flatMap((slice) => Some(newExtractOp(slice)))
        extractOp.flatMap((eOp) => pass.rewriteOperator(eOp, context))
      case VarExtractOp(slice) =>
        val sliceP = visitBitVectorSlice(slice, context)
        val extractOp = sliceP.flatMap((slice) => Some(newExtractOp(slice)))
        extractOp.flatMap((eOp) => pass.rewriteOperator(eOp, context))
      case ForallOp(args) =>
        Some(ForallOp(rewriteQuantifiedVars(args)))
      case ExistsOp(args) =>
        Some(ExistsOp(rewriteQuantifiedVars(args)))
      case _ =>
        pass.rewriteOperator(op, context)
    }
    return ASTNode.introducePos(setPosition, setFilename, opP, op.position)
  }

  def visitArraySelectOp(arrSel : ArraySelectOperation, context : Scope) : Option[Expr] = {
    val arrSelP = visitExpr(arrSel.e, context) match {
      case Some(e) => pass.rewriteArraySelect(ArraySelectOperation(e, arrSel.index.map(visitExpr(_, context)).flatten), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, arrSelP, arrSel.position)
  }

  def visitArrayStoreOp(arrStore : ArrayStoreOperation, context : Scope) : Option[Expr] = {
    val eP = visitExpr(arrStore.e, context)
    val ind = arrStore.index.map(visitExpr(_, context)).flatten
    val valP = visitExpr(arrStore.value, context)
    val arrStoreP = (eP, valP) match {
      case (Some(e), Some(value)) => pass.rewriteArrayStore(ArrayStoreOperation(e, ind, value), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, arrStoreP, arrStore.position)
  }

  def visitFuncApp(fapp : FuncApplication, context : Scope) : Option[Expr] = {
    val eP = visitExpr(fapp.e, context)
    val args = fapp.args.map(visitExpr(_, context)).flatten
    val fappP = eP match {
      case Some(e) => pass.rewriteFuncApp(FuncApplication(e, args), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, fappP, fapp.position)
  }

  def visitITE(ite: ITE, context : Scope) : Option[Expr] = {
    val condP = visitExpr(ite.e, context)
    val tP = visitExpr(ite.t, context)
    val fP = visitExpr(ite.f, context)

    val iteP = (condP, tP, fP) match {
      case (Some(cond), Some(t), Some(f)) => pass.rewriteITE(ITE(cond, t, f), context)
      case _ => None
    }
    return ASTNode.introducePos(setPosition, setFilename, iteP, ite.position)
  }

  def visitLambda(lambda: Lambda, contextIn : Scope) : Option[Lambda] = {
    val context = contextIn + lambda
    val idP = lambda.ids.map((arg) => {
      (visitIdentifier(arg._1, context), visitType(arg._2, context)) match {
        case (Some(id), Some(typ)) => Some(id, typ)
        case _ => None
      }
    }).flatten
    val lambdaP = visitExpr(lambda.e, context).flatMap((e) => pass.rewriteLambda(Lambda(idP, e), contextIn))
    return ASTNode.introducePos(setPosition, setFilename, lambdaP, lambda.position)
  }

  def visitExprDecorator(dec : ExprDecorator, context : Scope) : Option[ExprDecorator] = {
    val decP = pass.rewriteExprDecorator(dec, context)
    return ASTNode.introducePos(setPosition, setFilename, decP, dec.position)
  }
}
