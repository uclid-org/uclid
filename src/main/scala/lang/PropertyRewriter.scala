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
 * Author: Pramod Subramanyan
 * 
 * Compute the types of each module that is referenced in an instance declaration.
 *
 */
package uclid
package lang

class LTLOperatorArgumentCheckerPass extends ReadOnlyPass[Set[ModuleError]] {
  type T = Set[ModuleError]
  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass
  def checkBooleans(operands: List[Expr], context : Scope, in : T) : T = {
    var ret = in
    for (op <- operands) {
      var oType = exprTypeChecker.typeOf(op, context)
      if (!oType.isBool) {
        ret = ret + ModuleError("LTL operator expected argument of type boolean but received argument of type %s.".format(oType.toString), op.position)
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
      // any other operator, just recurse.
      case OperatorApplication(op, args) =>
        OperatorApplication(op, args.map(a => recurse(a)))
      case arrSel : ArraySelectOperation =>
        ArraySelectOperation(recurse(arrSel.e), arrSel.index.map(recurse(_)))
      case arrUpd : ArrayStoreOperation =>
        ArrayStoreOperation(recurse(arrUpd.e), arrUpd.index.map(recurse(_)), recurse(arrUpd.value))
      case funcApp : FuncApplication =>
        FuncApplication(recurse(funcApp.e), funcApp.args.map(recurse(_)))
      case ite : ITE =>
        ITE(recurse(ite.e), recurse(ite.t), recurse(ite.f))
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

  def createTseitinExpr(specName : Identifier, expr : Expr, nameProvider : ContextualNameProvider) : 
    (Identifier, List[(Identifier, Option[Expr])], List[(Identifier, Expr)], List[Identifier], List[Identifier], List[Identifier]) = {
    val isExprTemporal = expr match {
      case tExpr : PossiblyTemporalExpr => tExpr.isTemporal
      case ntExpr : Expr => false
    }
    if (!isExprTemporal) {
      val newVar = nameProvider(specName, "z")
      val newImpl = (newVar, Some(expr))
      // FIXME: Revisit this for expressions that don't involve any temporal operators.
      (newVar, List(newImpl), List.empty, List.empty, List.empty, List.empty)
    } else {
      // Recurse on operator applications and create "Tseitin" variables for the inner AST nodes.
      def createTseitinExprOpapp(opapp : OperatorApplication) : (Identifier, List[(Identifier, Option[Expr])], List[(Identifier, Expr)], List[Identifier], List[Identifier], List[Identifier]) = {
        val argResults = opapp.operands.map(arg => createTseitinExpr(specName, arg, nameProvider))
        val args = argResults.map(_._1)
        val argImpls = argResults.flatMap(a => a._2)
        val argNexts = argResults.flatMap(a => a._3)
        val argFaileds = argResults.flatMap(a => a._4)
        val argAccepts = argResults.flatMap(a => a._5)
        val argPendings = argResults.flatMap(a => a._6)
        
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
              (z, zImpl :: argImpls, pendingNext :: failedNext :: argNexts, failedVar :: argFaileds, argAccepts, pendingVar :: argPendings)
            case GloballyTemporalOp() =>
              val zImpl = (z, None)
              // pending = Ypending) \/ z
              val pendingVar = nameProvider(specName, "pending")
              val pendingNext = (pendingVar, or(Y(pendingVar), z))
              // failed = pending /\ !args(0)
              val failedVar = nameProvider(specName, "failed")
              val failedNext = (failedVar, and(pendingVar, not(args(0))))
              (z, zImpl :: argImpls, pendingNext :: failedNext :: argNexts, failedVar :: argFaileds, argAccepts, pendingVar :: argPendings)
            case FinallyTemporalOp() =>
              val zImpl = (z, None)
              // pending = (z \/ Ypending) /\ !args(0)
              val pendingVar = nameProvider(specName, "pending")
              val pendingExpr = and(or(z, Y(pendingVar)), not(args(0)))
              val pendingNext = (pendingVar, pendingExpr)
              // accept = !pending
              val acceptVar = nameProvider(specName, "accept")
              val acceptNext = (acceptVar, not(pendingVar))
              (z, zImpl :: argImpls, pendingNext :: acceptNext :: argNexts, argFaileds, acceptVar :: argAccepts, pendingVar :: argPendings)
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
              (z, zImpl :: argImpls, pendingNext :: failedNext :: argNexts, failedVar :: argFaileds, argAccepts, pendingVar :: argPendings)
            case _ =>
              throw new Utils.AssertionError("Unexpected temporal operator here: " + tOp.toString)
          }
        } else {
          val zImpl = (z, Some(innerExpr))
          (z, zImpl :: argImpls, argNexts, argFaileds, argAccepts, argPendings)
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
              createTseitinExprOpapp(opapp)
            case cOp : ComparisonOperator =>
              createTseitinExprOpapp(opapp)
            case tOp : TemporalOperator =>
              createTseitinExprOpapp(opapp)
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

  def rewriteSpecs(module : Module, ctx : Scope, ltlSpecs : List[SpecDecl], otherSpecs : List[SpecDecl]) : Module = {
    val nameProvider = new ContextualNameProvider(ctx, "ltl")
    val isInit = nameProvider(module.id, "is_init")
    val rewrites = ltlSpecs.map { 
      (s) => {
        val nnf = convertToNNF(not(s.expr))
        // println("exp: " + s.expr.toString)
        // println("nnf: " + nnf.toString)
        createTseitinExpr(s.id, nnf, nameProvider)
      }
    }
    val specNames = ltlSpecs.map(s => s.id)
    val monitorVars = rewrites.map(r => (r._4, r._5, r._6))

    def orExpr(a : Expr, b : Expr) : Expr = OperatorApplication(DisjunctionOp(), List(a, b))
    def andExpr(a : Expr, b : Expr) : Expr = OperatorApplication(ConjunctionOp(), List(a, b))
    def notExpr(a : Expr) : Expr = OperatorApplication(NegationOp(), List(a))
    // create the hasFailed and pending variables.
    val monitorExprs = (specNames zip monitorVars).map { 
      p => {
        val failedVars = p._2._1
        val hasFailedVar = nameProvider(p._1, "has_failed")
        val hasFailedExpr : Expr = failedVars.foldLeft(hasFailedVar.asInstanceOf[Expr])((acc, f) => orExpr(acc, f))

        val pendingVars = p._2._3
        val pendingVar = nameProvider(p._1, "PENDING")
        val pendingExpr : Expr = pendingVars.foldLeft(BoolLit(false).asInstanceOf[Expr])((acc, f) => orExpr(acc, f))

        val acceptVars = p._2._2
        val safetyExpr = andExpr(notExpr(pendingVar), notExpr(hasFailedVar))
        
        (p._1, (hasFailedVar, hasFailedExpr), (pendingVar, pendingExpr), acceptVars, safetyExpr)
        
      }
    }
    def implExpr(a : Expr, b : Expr) : Expr = OperatorApplication(ImplicationOp(), List(a, b))
    def iffExpr(a : Expr, b : Expr) : Expr = OperatorApplication(IffOp(), List(a, b))
    def eqExpr(a : Expr, b : Expr) : Expr = OperatorApplication(EqualityOp(), List(a, b))

    val isInitAssign = AssignStmt(List(LhsId(isInit)), List(BoolLit(false)))
    val rootVars = rewrites.map(_._1)
    val rootAssumes = rootVars.map(r => AssumeStmt(iffExpr(r, isInit), None))

    val newInputDecls = StateVarsDecl(rewrites.flatMap(r => r._2).map(_._1), BoolType())
    val monitorVarsInt = rewrites.flatMap(r => r._3).map(_._1)
    val monitorVarsExtFalse = monitorExprs.map(_._2._1) 
    val monitorVarsExtTrue = monitorExprs.map(_._3._1)
    val varsToInitFalse : List[Identifier] = monitorVarsExtFalse ++ monitorVarsInt
    val varsToInitTrue : List[Identifier] = isInit :: monitorVarsExtTrue
    val newVarDecls = StateVarsDecl(varsToInitTrue ++ varsToInitFalse, BoolType())
    val newInitFalse = AssignStmt(varsToInitFalse.map(LhsId(_)), List.fill(varsToInitFalse.size)(BoolLit(false)))
    val newInitTrue = AssignStmt(varsToInitTrue.map(LhsId(_)), List.fill(varsToInitTrue.size)(BoolLit(true)))
    val newInits = List(newInitFalse, newInitTrue) 

    val rewriteImpls = rewrites.flatMap(r => r._2)
    val implicationHavocs = rewriteImpls.map(r => HavocStmt(r._1))
    val implicationAssumes = rewriteImpls.collect{ case (id, Some(expr)) => AssumeStmt(iffExpr(id, expr), None) }

    val assignmentPairs = rewrites.flatMap(r => r._3)
    val newAssigns = assignmentPairs.map(p => AssignStmt(List(LhsId(p._1)), List(p._2)))
    val newHFAssigns = monitorExprs.map(p => AssignStmt(List(LhsId(p._2._1)), List(p._2._2)))
    val newPendingAssigns = monitorExprs.map(p => AssignStmt(List(LhsId(p._3._1)), List(p._3._2)))
    val newNexts = implicationHavocs ++ rootAssumes ++ implicationAssumes ++ newAssigns ++ newHFAssigns ++ newPendingAssigns

    val otherDecls = module.decls.filter(p => !p.isInstanceOf[SpecDecl] && !p.isInstanceOf[InitDecl] && !p.isInstanceOf[NextDecl]) ++ otherSpecs
    val newInitDecl = InitDecl(module.init.get.body ++ newInits ++ newNexts)
    val newNextDecl = NextDecl(isInitAssign :: module.next.get.body ++ newNexts)
    val newSafetyProperties = monitorExprs.map(p => SpecDecl(p._1, p._5, List(LTLSafetyFragmentDecorator, CoverDecorator)))
    val moduleDecls = otherDecls ++ List(newInputDecls, newVarDecls, newInitDecl, newNextDecl) ++ newSafetyProperties

    Module(module.id, moduleDecls, module.cmds)
  }
}

class LTLPropertyRewriter extends ASTRewriter(
    "LTLPropertyRewriter", new LTLPropertyRewriterPass())