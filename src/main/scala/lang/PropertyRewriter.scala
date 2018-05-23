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
 * Author: Pramod Subramanyan
 *
 * Compute the types of each module that is referenced in an instance declaration.
 *
 */
package uclid
package lang

import com.typesafe.scalalogging.Logger

class LTLOperatorArgumentCheckerPass extends ReadOnlyPass[Set[ModuleError]] {
  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  def checkBooleans(operands: List[Expr], context : Scope, in : T) : T = {
    var ret = in
    for (op <- operands) {
      var oType = exprTypeChecker.typeOf(op, context)
      if (!oType.isBool) {
        ret = ret + ModuleError("LTL operator expected argument of type boolean but received argument of type %s".format(oType.toString), op.position)
      }
    }
    ret
  }
  override def applyOnFuncApp(d : TraversalDirection.T, fapp : FuncApplication, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up || !context.inLTLSpec) {
      in
    } else {
      var ret = in
      fapp.e match {
        case Identifier(name) =>
          name match {
            case "G" =>
              var numOps = fapp.args.length
              if (numOps != 1) {
                ret = ret + ModuleError("globally operator expected 1 argument but received %s".format(numOps), fapp.position)
              }
            case "X" =>
              var numOps = fapp.args.length
              if (numOps != 1) {
                ret = ret + ModuleError("next operator expected 1 argument but received %s".format(numOps), fapp.position)
              }
            case "U" =>
              var numOps = fapp.args.length
              if (numOps != 2) {
                ret = ret + ModuleError("until operator expected 2 argument but received %s".format(numOps), fapp.position)
              }
            case "W" =>
              var numOps = fapp.args.length
              if (numOps != 2) {
                ret = ret + ModuleError("Weak-until operator expected 2 argument but received %s".format(numOps), fapp.position)
              }
            case "F" =>
              var numOps = fapp.args.length
              if (numOps != 1) {
                ret = ret + ModuleError("finally operator expected 1 argument but received %s".format(numOps), fapp.position)
              }
            case _ => in
          }
          checkBooleans(fapp.args, context, ret)
        case _ =>
          in
      }
    }
  }
}

class LTLOperatorArgumentChecker extends ASTAnalyzer(
  "LTLOperatorArgumentChecker", new LTLOperatorArgumentCheckerPass())
{
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val out = visitModule(module, Set.empty[ModuleError], context)
    if (out.nonEmpty) {
      val errors = out.map((me) => (me.msg, me.position)).toList
      throw new Utils.ParserErrorList(errors)
    }
    Some(module)
  }
}

class LTLOperatorIntroducerPass extends RewritePass {
  override def rewriteFuncApp(fapp: FuncApplication, context: Scope): Option[Expr] = {
    if (context.inLTLSpec) {
      fapp.e match {
        case Identifier(name : String) => name match {
          case "G" =>
            Some(OperatorApplication(new GloballyTemporalOp, fapp.args))
          case "X" =>
            Some(OperatorApplication(new NextTemporalOp, fapp.args))
          case "U" =>
            Some(OperatorApplication(new UntilTemporalOp, fapp.args))
          case "W" =>
            Some(OperatorApplication(new WUntilTemporalOp, fapp.args))
          case "F" =>
            Some(OperatorApplication(new FinallyTemporalOp, fapp.args))
          case "R" =>
            Some(OperatorApplication(new ReleaseTemporalOp, fapp.args))
          case _ =>
            Some(fapp)
        }
        case _ => Some(fapp)
      }
    } else {
      Some(fapp)
    }
  }
}

class LTLOperatorIntroducer extends ASTRewriter(
    "LTLOperatorIntroducer", new LTLOperatorIntroducerPass())


class LTLOperatorRewriterPass extends RewritePass {
  def and(x : Expr, y : Expr) = Operator.and(x, y)
  def or(x : Expr, y : Expr) = Operator.or(x, y)
  def not(x : Expr) = Operator.not(x)
  def F(x : Expr) = OperatorApplication(FinallyTemporalOp(), List(x))
  def W(x : Expr, y : Expr) = OperatorApplication(WUntilTemporalOp(), List(x, y))
  def U(x : Expr, y : Expr) = OperatorApplication(UntilTemporalOp(), List(x, y))

  def rewriteTemporalOp(tOp : TemporalOperator, args : List[Expr]) : Expr = {
    tOp match {
      case GloballyTemporalOp() | NextTemporalOp() | FinallyTemporalOp() | WUntilTemporalOp() =>
        OperatorApplication(tOp, args)
      case UntilTemporalOp() =>
        val x = args(0)
        val y = args(1)
        and(W(x, y), F(x))
      case ReleaseTemporalOp() =>
        val x = args(0)
        val y = args(1)
        not(U(not(x), not(y)))
    }
  }

  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    val op = opapp.op
    op match {
      case tOp : TemporalOperator =>
        Some(rewriteTemporalOp(tOp, opapp.operands))
      case _ =>
        Some(opapp)
    }
  }
}

class LTLOperatorRewriter extends ASTRewriter(
  "LTLOperatorRewriter", new LTLOperatorRewriterPass())


class LTLPropertyRewriterPass extends RewritePass {
  var conjCounter = 0
  var circuits : List[(Identifier, Expr)] = List[(Identifier, Expr)]()
  var specMap : Map[SpecDecl, (List[(Identifier, Expr)], Identifier, Identifier)] = Map[SpecDecl, (List[(Identifier, Expr)], Identifier, Identifier)]()

  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  val logger = Logger(classOf[LTLPropertyRewriterPass])

  def Y(x : Expr) = Operator.Y(x)
  def and(x : Expr, y : Expr) = Operator.and(x, y)
  def or(x : Expr, y : Expr) = Operator.or(x, y)
  def not(x : Expr) = Operator.not(x)

  def convertToNNF(expr : Expr) : Expr = {
    def recurse(e :  Expr) = convertToNNF(e)
    expr match {
      case id : Identifier => id
      case eId : ExternalIdentifier => eId
      case lit : Literal => lit
      case tup : Tuple => Tuple(tup.values.map(recurse(_)))
      // !G x -> F !x
      case OperatorApplication(NegationOp(), List(OperatorApplication(GloballyTemporalOp(), args))) =>
        OperatorApplication(FinallyTemporalOp(), args.map(a => recurse(not(a))))
      // !F x -> G !x
      case OperatorApplication(NegationOp(), List(OperatorApplication(FinallyTemporalOp(), args))) =>
        OperatorApplication(GloballyTemporalOp(), args.map(a => recurse(not(a))))
      // !(x U y) -> !x R !y
      case OperatorApplication(NegationOp(), List(OperatorApplication(UntilTemporalOp(), args))) =>
        OperatorApplication(ReleaseTemporalOp(), args.map(a => recurse(not(a))))
      // !(x R y) -> !x U !y
      case OperatorApplication(NegationOp(), List(OperatorApplication(ReleaseTemporalOp(), args))) =>
        OperatorApplication(UntilTemporalOp(), args.map(a => recurse(not(a))))
      // !(x W y) -> !y U (!x /\ !y)
      case OperatorApplication(NegationOp(), List(OperatorApplication(WUntilTemporalOp(), args))) =>
        val notA = recurse(not(args(0)))
        val notB = recurse(not(args(1)))
        val wOp = OperatorApplication(WUntilTemporalOp(), List(notB, and(notA, notB)))
        val fOp = OperatorApplication(FinallyTemporalOp(), List(notB))
        and(wOp, fOp)
      // !X a -> X !a
      case OperatorApplication(NegationOp(), List(OperatorApplication(NextTemporalOp(), args))) =>
        OperatorApplication(NextTemporalOp(), args.map(a => recurse(not(a))))
      // !(a && b) -> !a || !b
      case OperatorApplication(NegationOp(), List(OperatorApplication(ConjunctionOp(), args))) =>
        OperatorApplication(DisjunctionOp(), args.map(a => recurse(not(a))))
      // !(a || b) -> !a && !b
      case OperatorApplication(NegationOp(), List(OperatorApplication(DisjunctionOp(), args))) =>
        OperatorApplication(ConjunctionOp(), args.map(a => recurse(not(a))))
      // !(!a) -> a
      case OperatorApplication(NegationOp(), List(OperatorApplication(NegationOp(), args))) =>
        args(0)
      // !(a == b) -> a != b
      case OperatorApplication(NegationOp(), List(OperatorApplication(EqualityOp(), args))) =>
        OperatorApplication(InequalityOp(), args)
      // !(a != b) -> a == b
      case OperatorApplication(NegationOp(), List(OperatorApplication(InequalityOp(), args))) =>
        OperatorApplication(EqualityOp(), args)
      // !(a ==> b) -> a && !b
      case OperatorApplication(NegationOp(), List(OperatorApplication(ImplicationOp(), args))) =>
        OperatorApplication(ConjunctionOp(), List(args(0), recurse(not(args(1)))))
      // !(a <==> b) -> (a != b)
      case OperatorApplication(NegationOp(), List(OperatorApplication(IffOp(), args))) =>
        OperatorApplication(InequalityOp(), args)
      // !(if e then texp else fexp) -> if e then !texp else !fexp
      case OperatorApplication(NegationOp(), List(OperatorApplication(ITEOp(), args))) =>
        OperatorApplication(ITEOp(), List(recurse(args(0)), recurse(not(args(1))), recurse(not(args(2)))))
      // any other operator, just recurse.
      case OperatorApplication(op, args) =>
        OperatorApplication(op, args.map(a => recurse(a)))
      case arrSel : ArraySelectOperation =>
        ArraySelectOperation(recurse(arrSel.e), arrSel.index.map(recurse(_)))
      case arrUpd : ArrayStoreOperation =>
        ArrayStoreOperation(recurse(arrUpd.e), arrUpd.index.map(recurse(_)), recurse(arrUpd.value))
      case funcApp : FuncApplication =>
        FuncApplication(recurse(funcApp.e), funcApp.args.map(recurse(_)))
      case lambda : Lambda =>
        Lambda(lambda.ids, recurse(lambda.e))
    }
  }

  def replace(expr: Expr, spec: SpecDecl, context: Scope) : Expr = {
    if (exprTypeChecker.typeOf(expr, context).isBool) {
      expr match {
        case OperatorApplication(op, operands) =>
          for (opr <- operands) {
            replace(opr, spec, context)
          }
          val ret = Identifier("z" concat conjCounter.toString)
          conjCounter += 1
          circuits = (ret, expr) :: circuits
          ret
        case _ =>
          expr
      }
    } else {
      expr
    }
  }

  /** This class is the return value of createMonitorExpressions.
   *
   *  z is the name of the "Tseitin" variable corresponding to the top of the expression's AST.
   *  biImplications are the list of equivalences between Tseitin variables and corresponding expressions.
   *  assignments is a list of assignments to monitor variables.
   *  failed, accept and pending are the corresponding monitor variables.
   */
  case class MonitorInfo(
    z : Identifier,
    biImplications : List[(Identifier, Option[Expr])],
    assignments : List[(Identifier, Expr)],
    failedVars : List[Identifier],
    acceptVars : List[Identifier],
    pendingVars : List[Identifier]
  )

  /** This function creates the monitor expressions for each temporal and non-temporal operator.
   *
   *  The conversion to the negated normal form must have been done before calling this method.
   */
  def createMonitorExpressions(specName : Identifier, expr : Expr, nameProvider : ContextualNameProvider) : MonitorInfo = {
    val isExprTemporal = expr match {
      case tExpr : PossiblyTemporalExpr => tExpr.isTemporal
      case ntExpr : Expr => false
    }
    if (!isExprTemporal) {
      val newVar = nameProvider(specName, "z")
      val newImpl = (newVar, Some(expr))
      // FIXME: Revisit this for expressions that don't involve any temporal operators.
      MonitorInfo(newVar, List(newImpl), List.empty, List.empty, List.empty, List.empty)
    } else {
      // Recurse on operator applications and create "Tseitin" variables for the inner AST nodes.
      def createMonitorsForOpApp(opapp : OperatorApplication) : MonitorInfo = {
        val argResults = opapp.operands.map(arg => createMonitorExpressions(specName, arg, nameProvider))
        val args = argResults.map(a => a.z)
        val argImpls = argResults.flatMap(a => a.biImplications)
        val argNexts = argResults.flatMap(a => a.assignments)
        val argFaileds = argResults.flatMap(a => a.failedVars)
        val argAccepts = argResults.flatMap(a => a.acceptVars)
        val argPendings = argResults.flatMap(a => a.pendingVars)

        val z = nameProvider(specName, "z")
        val innerExpr = OperatorApplication(opapp.op, args)
        if (opapp.op.isInstanceOf[TemporalOperator]) {
          val tOp = opapp.op.asInstanceOf[TemporalOperator]

          tOp match {
            case NextTemporalOp() =>
              val zImpl = (z, None)
              // pending = z
              val pendingVar = nameProvider(specName, "pending")
              val pendingNext = (pendingVar, z)
              // failed = Ypending /\ !args(0)
              val failedVar = nameProvider(specName, "failed")
              val failedNext = (failedVar, and(Y(pendingVar), not(args(0))))
              MonitorInfo(z, zImpl :: argImpls, pendingNext :: failedNext :: argNexts, failedVar :: argFaileds, argAccepts, pendingVar :: argPendings)
            case GloballyTemporalOp() =>
              val zImpl = (z, None)
              // pending = Ypending) \/ z
              val pendingVar = nameProvider(specName, "pending")
              val pendingNext = (pendingVar, or(Y(pendingVar), z))
              // failed = pending /\ !args(0)
              val failedVar = nameProvider(specName, "failed")
              val failedNext = (failedVar, and(pendingVar, not(args(0))))
              MonitorInfo(z, zImpl :: argImpls, pendingNext :: failedNext :: argNexts, failedVar :: argFaileds, argAccepts, pendingVar :: argPendings)
            case FinallyTemporalOp() =>
              val zImpl = (z, None)
              // pending = (z \/ Ypending) /\ !args(0)
              val pendingVar = nameProvider(specName, "pending")
              val pendingExpr = and(or(z, Y(pendingVar)), not(args(0)))
              val pendingNext = (pendingVar, pendingExpr)
              // accept = !pending
              val acceptVar = nameProvider(specName, "accept")
              val acceptNext = (acceptVar, not(pendingVar))
              MonitorInfo(z, zImpl :: argImpls, pendingNext :: acceptNext :: argNexts, argFaileds, acceptVar :: argAccepts, pendingVar :: argPendings)
            case WUntilTemporalOp() =>
              val zImpl = (z, None)
              // pending = (z \/ Y pending) /\ !args(1)
              val pendingVar = nameProvider(specName, "pending")
              val pendingExpr = and(or(z, Y(pendingVar)), not(args(1)))
              val pendingNext = (pendingVar, pendingExpr)
              // failed = pending /\ !args(0)
              val failedVar = nameProvider(specName, "failed")
              val failedExpr = and(pendingExpr, not(args(0)))
              val failedNext = (failedVar, failedExpr)
              // accept = true
              val acceptVar = nameProvider(specName, "accept")
              val acceptNext = (acceptVar, BoolLit(false))
              MonitorInfo(z, zImpl :: argImpls, pendingNext :: failedNext :: acceptNext  :: argNexts, failedVar :: argFaileds, acceptVar :: argAccepts, pendingVar :: argPendings)
            case _ =>
              throw new Utils.AssertionError("Unexpected temporal operator here: " + tOp.toString)
          }
        } else {
          val zImpl = (z, Some(innerExpr))
          MonitorInfo(z, zImpl :: argImpls, argNexts, argFaileds, argAccepts, argPendings)
        }
      }
      // Recurse on a temporal operator.
      val tExpr = expr.asInstanceOf[PossiblyTemporalExpr]
      tExpr match {
        case opapp : OperatorApplication =>
          val op = opapp.op
          op match {
            case op : BooleanOperator =>
              Utils.assert(!op.isQuantified, "Temporal expression within quantifier: " + expr.toString)
              createMonitorsForOpApp(opapp)
            case cOp : ComparisonOperator =>
              createMonitorsForOpApp(opapp)
            case tOp : TemporalOperator =>
              createMonitorsForOpApp(opapp)
            case _ =>
              throw new Utils.AssertionError("Invalid temporal expression: " + expr.toString)
          }
      }
    }
  }

  override def rewriteModule(module: Module, ctx: Scope): Option[Module] = {
    val moduleSpecs = module.decls.collect{ case spec : SpecDecl => spec }
    val ltlSpecs = moduleSpecs.filter(s => s.params.exists(d => d == LTLExprDecorator))
    if (ltlSpecs.size == 0) {
      Some(module)
    } else {
      val otherSpecs = moduleSpecs.filter(s => !s.params.exists(d => d == LTLExprDecorator))
      Some(rewriteSpecs(module, ctx, ltlSpecs, otherSpecs))
    }
  }

  def newVars(vars : List[(Identifier, Type)], nameProvider : ContextualNameProvider) : List[(Identifier, Identifier, Type)] = {
    vars.map((p) => (p._1, nameProvider(p._1, "copy2"), p._2))
  }

  def orExpr(a : Expr, b : Expr) : Expr = OperatorApplication(DisjunctionOp(), List(a, b))
  def andExpr(a : Expr, b : Expr) : Expr = OperatorApplication(ConjunctionOp(), List(a, b))
  def notExpr(a : Expr) : Expr = OperatorApplication(NegationOp(), List(a))
  def eqExpr(a : Expr, b : Expr) : Expr = OperatorApplication(EqualityOp(), List(a, b))
  def implExpr(a : Expr, b : Expr) : Expr = OperatorApplication(ImplicationOp(), List(a, b))
  def iffExpr(a : Expr, b : Expr) : Expr = OperatorApplication(IffOp(), List(a, b))

  def assignToVars(varsLeft : List[(Identifier, Type)], varsRight : List[(Identifier, Type)]) : List[AssignStmt] = {
    Utils.assert(varsLeft.size == varsRight.size, "Var arrays must be the same size.")
    (varsLeft zip varsRight).map {
      case (varDecl1, varDecl2) => AssignStmt(List(LhsId(varDecl1._1)), List(varDecl2._1))
    }
  }
  def guardedAssignment(guardVar : Identifier, copyVar : Identifier, origVars : List[(Identifier, Type)], newVars : List[(Identifier, Type)]) : Statement = {
    val thenBlock = BlockStmt(AssignStmt(List(LhsId(copyVar)), List(BoolLit(true))) :: assignToVars(newVars, origVars))
    val ifStmt = IfElseStmt(andExpr(guardVar, notExpr(copyVar)), thenBlock, BlockStmt(List.empty))
    ifStmt
  }

  def eqVarsExpr(varsLeft : List[(Identifier, Type)], varsRight : List[(Identifier, Type)]) : Expr = {
    Utils.assert(varsLeft.size == varsRight.size, "Var arrays must be the same size.")
    val eqExprs = (varsLeft zip varsRight) map {
      case (v1, v2) => eqExpr(v1._1, v2._1)
    }
    val initExpr : Expr = BoolLit(true)
    eqExprs.foldLeft(initExpr)((acc, e) => andExpr(acc, e))
  }

  def createRepeatedAssignment(vars : List[Identifier], value : Expr) : Option[AssignStmt] = {
    if (vars.size > 0) {
      Some(AssignStmt(vars.map(LhsId(_)), List.fill(vars.size)(value)))
    } else {
      None
    }
  }
  def createAssign(v : Identifier, e : Expr) : AssignStmt = {
    AssignStmt(List(LhsId(v)), List(e))
  }
  def createAssign(vs : List[Identifier], es : List[Expr]) : Option[AssignStmt] = {
    if (vs.size > 0) {
      Some(AssignStmt(vs.map(LhsId(_)), es))
    }  else {
      None
    }
  }

  def rewriteSpecs(module : Module, ctx : Scope, ltlSpecs : List[SpecDecl], otherSpecs : List[SpecDecl]) : Module = {
    val nameProvider = new ContextualNameProvider(ctx, "ltl")

    val monitors = ltlSpecs.map {
      (s) => {
        val nnf = convertToNNF(not(s.expr))
        logger.debug("EXP: {}", s.expr.toString())
        logger.debug("NNF: {}", nnf.toString()) 
        createMonitorExpressions(s.id, nnf, nameProvider)
      }
    }

    // create a copy of the state variables and non-deterministically assign the current state to it.
    val allPendingVars = monitors.flatMap(s => s.pendingVars.map(s => (s, BooleanType())))
    val varsToCopy = module.vars ++ allPendingVars
    val varCopyPairs = newVars(varsToCopy, nameProvider)
    val varsToCopyP = varCopyPairs.map(p => (p._2, p._3))
    val varsToCopyPDecl = varsToCopyP.map(v => StateVarsDecl(List(v._1), v._2))
    val copyStateInput = nameProvider(module.id, "copy_state_in")
    val stateCopiedVar = nameProvider(module.id, "state_copied")
    val copyStateInputDecl = InputVarsDecl(List(copyStateInput), BooleanType())
    val stateCopiedVarDecl = StateVarsDecl(List(stateCopiedVar), BooleanType())
    val stateCopyStmt = guardedAssignment(copyStateInput, stateCopiedVar, varsToCopy, varsToCopyP)
    val stateVarsEqExpr = eqVarsExpr(varsToCopy, varsToCopyP)

    // create the "FAILED" variables.
    val hasFaileds = (ltlSpecs zip monitors).map {
      case (spec, monitor) => {
        val hasFailedVar = nameProvider(spec.id, "FAILED")
        val hasFailedExpr : Expr = monitor.failedVars.foldLeft(hasFailedVar.asInstanceOf[Expr])((acc, f) => orExpr(acc, f))
        (hasFailedVar, hasFailedExpr)
      }
    }
    // create the "PENDING" variables.
    val pendings = (ltlSpecs zip monitors).map {
      case (spec, monitor) => {
        val pendingVar = nameProvider(spec.id, "PENDING")
        val pendingExpr : Expr = monitor.pendingVars.foldLeft(BoolLit(false).asInstanceOf[Expr])((acc, f) => orExpr(acc, f))
        (pendingVar, pendingExpr)
      }
    }
    // create the ACCEPT variables.
    val hasAccepteds = (ltlSpecs zip monitors).map {
      case (spec, monitor) => {
        // has accepted is true if this trace has been accepted at least once in the cycle
        val hasAcceptedVars = monitor.acceptVars.map(aVar => nameProvider(aVar, "HAS_ACCEPTED"))
        val hasAcceptedExprs = (monitor.acceptVars zip hasAcceptedVars).map {
          case (aVar, haVar) => orExpr(haVar, andExpr(aVar, stateCopiedVar))
        }
        // has accepted trace is true if all of the accept vars of this trace have been accepted at least
        // once in this cycle.
        val foldInit : Expr = BoolLit(true)
        val hasAcceptedTrace = nameProvider(spec.id, "HAS_ACCEPTED_TRACE")
        val hasAcceptedTraceExpr = if (hasAcceptedVars.size == 0) {
          stateCopiedVar
        } else {
          hasAcceptedVars.foldLeft(foldInit)((acc, v) => andExpr(acc, v))
        }

        ((hasAcceptedVars, hasAcceptedExprs), (hasAcceptedTrace, hasAcceptedTraceExpr))
      }
    }

    val safetyExprs = (hasFaileds zip pendings) map {
      case ((hasFailedVar, _), (pendingVar, _)) =>
        andExpr(notExpr(pendingVar), notExpr(hasFailedVar))
    }
    val livenessExprs = (hasFaileds zip hasAccepteds) map {
      case ((hasFailedVar, _), ((_, _), (hasAcceptedTrace, _))) =>
        andExpr(stateVarsEqExpr, andExpr(notExpr(hasFailedVar), hasAcceptedTrace))
    }
    // This is the assignment to is_init in next.
    val isInitStateVar = nameProvider(module.id, "is_init")
    val isInitStateVarDecl = StateVarsDecl(List(isInitStateVar), BooleanType())
    val isInitAssignNext = AssignStmt(List(LhsId(isInitStateVar)), List(BoolLit(false)))

    // The top-level 'z' variables.
    val zVars = monitors.map(_.z)
    val zAssumes = zVars.map(r => AssumeStmt(iffExpr(r, isInitStateVar), None))

    // These are the monitor inputs. (The 'z' variables.)
    val monitorInputs = monitors.flatMap(m => m.biImplications.map(_._1))
    val monitorInputsDecl = StateVarsDecl(monitorInputs, BooleanType())
    // These are the monitor variables. ('z' variables which are not the top-level.)
    val monitorVars = monitors.flatMap(r => r.assignments).map(_._1)
    val monitorVarsDecl = StateVarsDecl(monitorVars, BooleanType())
    // These are the has failed variables.
    val hasFailedVars = hasFaileds.map(_._1)
    val hasFailedVarsDecl = StateVarsDecl(hasFailedVars, BooleanType())
    // Now for the pending variables.
    val pendingVars = pendings.map(_._1)
    val pendingVarsDecl = StateVarsDecl(pendingVars, BooleanType())
    // Now for the accept var variables.
    val hasAcceptedVars = hasAccepteds.flatMap(e => e._1._1)
    val hasAcceptedVarsDecl = StateVarsDecl(hasAcceptedVars, BooleanType())
    // And then then accept trace variables.
    val hasAcceptedTraceVars = hasAccepteds.map(e => e._2._1)
    val hasAcceptedTraceVarsDecl = StateVarsDecl(hasAcceptedTraceVars, BooleanType())

    // new variable declarations.
    val varDecls = List(copyStateInputDecl, stateCopiedVarDecl,
                      isInitStateVarDecl, hasFailedVarsDecl,
                      pendingVarsDecl, hasAcceptedVarsDecl, hasAcceptedTraceVarsDecl,
                      monitorInputsDecl, monitorVarsDecl) ++ varsToCopyPDecl

    // now construct the next block.
    val stateCopiedInitStmt = AssignStmt(List(LhsId(stateCopiedVar)), List(BoolLit(false)))
    val postInitStmts = List(
                    createRepeatedAssignment(hasFailedVars, BoolLit(false)),
                    createRepeatedAssignment(monitorVars, BoolLit(false)),
                    createRepeatedAssignment(hasAcceptedVars, BoolLit(false)),
                    createRepeatedAssignment(hasAcceptedTraceVars, BoolLit(false)),
                    createRepeatedAssignment(isInitStateVar :: pendingVars, BoolLit(true)),
                    Some(stateCopiedInitStmt)).flatten

    // monitor iff "assignments"
    val monitorBiImpls = monitors.flatMap(r => r.biImplications)
    val biImplHavocs = monitorBiImpls.map(r => HavocStmt(HavocableId(r._1)))
    val biImplAssumes = monitorBiImpls.collect{ case (id, Some(expr)) => AssumeStmt(implExpr(id, expr), None) }

    // monitor internal assignments.
    val assignmentPairs = monitors.flatMap(r => r.assignments)
    val monitorAssignments = assignmentPairs.map(p => createAssign(p._1, p._2))
    val hasFailedAssignments = hasFaileds.map(p => createAssign(p._1, p._2))
    val pendingAssignments = pendings.map(p => createAssign(p._1, p._2))
    val hasAcceptedAssignments = hasAccepteds.map(p => createAssign(p._1._1, p._1._2)).flatten
    val hasAcceptedTraceAssignments = hasAccepteds.map(p => createAssign(p._2._1, p._2._2))
    val preNextStmts = List(stateCopyStmt, isInitAssignNext)
    val postNextStmts = biImplHavocs ++ zAssumes ++ biImplAssumes ++ monitorAssignments ++
                        hasFailedAssignments ++ pendingAssignments ++
                        hasAcceptedAssignments ++ hasAcceptedTraceAssignments
    // new init/next.
    val newInitDecl = InitDecl(BlockStmt(List(module.init.get.body) ++ postInitStmts ++ postNextStmts))
    val newNextDecl = NextDecl(BlockStmt(preNextStmts ++ List(module.next.get.body) ++ postNextStmts))
    // new safety properties.
    val newSafetyProperties = (ltlSpecs zip safetyExprs).map {
      p => {
        val pName = Identifier(p._1.id.name + ":safety")
        val pNameWithPos = ASTNode.introducePos(true, true, pName, p._1.id.position)
        val exprWithPos = ASTNode.introducePos(true, true, p._2, p._1.expr.position)
        val pPrime = SpecDecl(pNameWithPos, exprWithPos, List(LTLSafetyFragmentDecorator, CoverDecorator))
        ASTNode.introducePos(true, true, pPrime, p._1.position)
      }
    }
    val newLivenessProperties = (ltlSpecs zip livenessExprs).map {
      p => {
        val pName = Identifier(p._1.id.name + ":liveness")
        val pNameWithPos = ASTNode.introducePos(true, true, pName, p._1.id.position)
        val exprWithPos = ASTNode.introducePos(true, true, p._2, p._1.expr.position)
        val pPrime = SpecDecl(pNameWithPos, exprWithPos, List(LTLLivenessFragmentDecorator, CoverDecorator))
        ASTNode.introducePos(true, true, pPrime, p._1.position)
      }
    }
    // extract the rest of the module as-is.
    val otherDecls = module.decls.filter(
        p => !p.isInstanceOf[SpecDecl] &&
             !p.isInstanceOf[InitDecl] &&
             !p.isInstanceOf[NextDecl]) ++ otherSpecs
    // assemble the new module.
    val moduleDecls = otherDecls ++ varDecls ++ List(newInitDecl, newNextDecl) ++ newSafetyProperties ++ newLivenessProperties
    Module(module.id, moduleDecls, module.cmds, module.notes)
  }
}

class LTLPropertyRewriter extends ASTRewriter(
    "LTLPropertyRewriter", new LTLPropertyRewriterPass())
