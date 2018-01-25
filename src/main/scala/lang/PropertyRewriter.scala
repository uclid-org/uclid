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

class LTLOperatorRewriterPass extends RewritePass {
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

class LTLOperatorRewriter extends ASTRewriter("LTLOperatorRewriter", new LTLOperatorRewriterPass()) {
}


class LTLNegatedNormalFormRewriterPass extends RewritePass {
}

class LTLNegatedNormalFormRewriter extends ASTRewriter(
  "LTLNegatedNormalFormRewriter", new LTLNegatedNormalFormRewriterPass())


class LTLPropertyRewriterPass extends RewritePass {
  var conjCounter = 0
  var circuits : List[(Identifier, Expr)] = List[(Identifier, Expr)]()
  var specMap : Map[SpecDecl, (List[(Identifier, Expr)], Identifier, Identifier)] = Map[SpecDecl, (List[(Identifier, Expr)], Identifier, Identifier)]()

  lazy val manager : PassManager = analysis.manager
  lazy val exprTypeChecker = manager.pass("ExpressionTypeChecker").asInstanceOf[ExpressionTypeChecker].pass

  def negate(expr : Expr) : Expr = OperatorApplication(NegationOp(), List(expr))
  def convertToNNF(expr : Expr) : Expr = {
    def recurse(e :  Expr) = convertToNNF(e)
    expr match {
      case id : Identifier => id
      case eId : ExternalIdentifier => eId
      case lit : Literal => lit
      case tup : Tuple => Tuple(tup.values.map(recurse(_)))
      case opapp : OperatorApplication =>
        val op = opapp.op
        val args = opapp.operands
        lazy val opappP = OperatorApplication(op, args.map(recurse(_)))
        opapp.op match {
          case NegationOp() =>
            Utils.assert(args.size == 1, "Negation operation must have only one operand.")
            val operand = args(0)
            operand match {
              case OperatorApplication(op, operands) =>
                lazy val negOps = operands.map(op => recurse(negate(op)))
                op match {
                  case GloballyTemporalOp() =>
                    OperatorApplication(FinallyTemporalOp(), negOps)
                  case NextTemporalOp() =>
                    OperatorApplication(NextTemporalOp(), negOps)
                  case UntilTemporalOp() =>
                    OperatorApplication(ReleaseTemporalOp(), negOps)
                  case FinallyTemporalOp() =>
                    OperatorApplication(GloballyTemporalOp(), negOps)
                  case ReleaseTemporalOp() =>
                    OperatorApplication(UntilTemporalOp(), negOps)
                  case ConjunctionOp() =>
                    OperatorApplication(DisjunctionOp(), negOps)
                  case DisjunctionOp() =>
                    OperatorApplication(ConjunctionOp(), negOps)
                  case IffOp() =>
                    OperatorApplication(InequalityOp(), operands)
                  case ImplicationOp() =>
                    OperatorApplication(ConjunctionOp(), List(operands(0), negOps(1)))
                  case NegationOp() =>
                    args(0)
                  case EqualityOp() =>
                    OperatorApplication(InequalityOp(), args)
                  case InequalityOp() =>
                    OperatorApplication(EqualityOp(), args)
                  case _ =>
                    opappP
                }
              case _ =>
                opappP
            }
          case _ =>
            opappP
        }
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

  def createTseitinExpr(specName : Identifier, expr : Expr, nameProvider : ContextualNameProvider) : (Identifier, List[(Identifier, Expr)], List[(Identifier, Expr)], List[Identifier], List[Identifier]) = {
    val isExprTemporal = expr match {
      case tExpr : PossiblyTemporalExpr => tExpr.isTemporal
      case ntExpr : Expr => false
    }
    if (!isExprTemporal) {
      val newVar = nameProvider(specName, "z")
      val newImpl = (newVar, expr)
      // FIXME: Revisit this for expressions that don't involve any temporal operators.
      (newVar, List(newImpl), List.empty, List.empty, List.empty)
    } else {
      // Recurse on operator applications and create "Tseitin" variables for the inner AST nodes.
      def createTseitinExprOpapp(opapp : OperatorApplication) : (Identifier, List[(Identifier, Expr)], List[(Identifier, Expr)], List[Identifier], List[Identifier]) = {
        val argResults = opapp.operands.map(arg => createTseitinExpr(specName, arg, nameProvider))
        val args = argResults.map(_._1)
        val argImpls = argResults.flatMap(a => a._2)
        val argNexts = argResults.flatMap(a => a._3)
        val argFaileds = argResults.flatMap(a => a._4)
        val argAccepts = argResults.flatMap(a => a._5)
        
        val z = nameProvider(specName, "z")
        val innerExpr = OperatorApplication(opapp.op, args)
        val zImpl = (z, innerExpr)
        if (opapp.op.isInstanceOf[TemporalOperator]) {
          val tOp = opapp.op.asInstanceOf[TemporalOperator]
          def Y(x : Expr) = OperatorApplication(HistoryOperator(), List(x, IntLit(1)))
          def not(x : Expr) = OperatorApplication(NegationOp(), List(x))
          def and(x : Expr, y : Expr) = OperatorApplication(ConjunctionOp(), List(x, y))
          def or(x : Expr, y : Expr) = OperatorApplication(DisjunctionOp(), List(x, y))
          
          tOp match {
            case NextTemporalOp() =>
              // pending = z
              val pendingVar = nameProvider(specName, "pending")
              val pendingNext = (pendingVar, z)
              // failed = Ypending /\ !args(0)
              val failedVar = nameProvider(specName, "failed")
              val failedNext = (failedVar, and(Y(pendingVar), not(args(0))))
              (z, zImpl :: argImpls, pendingNext :: failedNext :: argNexts, failedVar :: argFaileds, argAccepts)
            case GloballyTemporalOp() =>
              // pending = Ypending) \/ z
              val pendingVar = nameProvider(specName, "pending")
              val pendingNext = (pendingVar, or(Y(pendingVar), z))
              // failed = pending /\ !args(0)
              val failedVar = nameProvider(specName, "failed")
              val failedNext = (failedVar, and(pendingVar, not(args(0))))
              (z, zImpl :: argImpls, pendingNext :: failedNext :: argNexts, failedVar :: argFaileds, argAccepts)
            case FinallyTemporalOp() =>
              // pending = (z \/ Ypending) /\ ~args(0)
              val pendingVar = nameProvider(specName, "pending")
              val pendingExpr = and(or(z, Y(pendingVar)), not(args(0)))
              val pendingNext = (pendingVar, pendingExpr)
              // accept = ~pending
              val acceptVar = nameProvider(specName, "accept")
              val acceptNext = (acceptVar, not(pendingVar))
              (z, zImpl :: argImpls, pendingNext :: acceptNext :: argNexts, argFaileds, acceptVar :: argAccepts)
            case _ =>
              // FIXME
              throw new Utils.UnimplementedException("Need more cases here.")
          }
        } else {
          (z, zImpl :: argImpls, argNexts, argFaileds, argAccepts)
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

  def rewriteLTLSpec(spec: SpecDecl, context: Scope, nameProvider : ContextualNameProvider): SpecDecl = {
    println("original: " + spec.expr.toString)
    val negExpr = convertToNNF(negate(spec.expr))
    println("NNF: " + negExpr.toString)
    val transformedExpr = createTseitinExpr(spec.id, negExpr, nameProvider)
    println ("root: " + transformedExpr._1.toString)
    println ("implications:")
    transformedExpr._2.foreach {
      (r) => println("%s ==> %s".format(r._1.toString, r._2.toString)) 
    }
    println("next assignments:")
    transformedExpr._3.foreach {
      (r) => println("%s = %s".format(r._1.toString, r._2.toString))
    }
    println("pendings: " + Utils.join(transformedExpr._4.map(_.toString), ", "))
    println("accepts: " + Utils.join(transformedExpr._5.map(_.toString), ", "))
    spec
  }

  override def rewriteSpec(spec: SpecDecl, context: Scope): Option[SpecDecl] = {
    if (spec.params.exists(p => p == LTLExprDecorator)) {
      rewriteLTLSpec(spec, context, new ContextualNameProvider(context, "ltl"))
      Some(spec)
      //val ret = replace(spec.expr, spec, context).asInstanceOf[Identifier]
      //conjCounter = 0
      //val fail = Identifier(spec.id.name concat "_failed")
      //specMap +=  (spec -> (circuits, ret, fail))
      //Some(SpecDecl(spec.id, OperatorApplication(new NegationOp, List(fail)), spec.params))
    } else {
      Some(spec)
    }
  }

  override def rewriteModule(module: Module, ctx: Scope): Option[Module] = {
    Some(module)
    /*
    var allDecls = module.decls
    var newNext = module.next.get.body
    for ((spec: SpecDecl, (circuits: List[(Identifier, Expr)], start: Identifier, failed: Identifier)) <- specMap) {
      allDecls = StateVarsDecl(List(failed), new BoolType) :: allDecls
      var failExpr = OperatorApplication(new NegationOp, List(BoolLit(false)))
      for ((z: Identifier, expr: Expr) <- circuits) {
        // how do we initialize the values of these vars?
        allDecls = StateVarsDecl(List(z), new BoolType) :: allDecls
        expr match {
          case OperatorApplication(op: GloballyTemporalOp, operands) =>
            var pending = Identifier(spec.id.name concat z.name concat "_pending")
            allDecls = StateVarsDecl(List(pending), new BoolType) :: allDecls
            // Update pending: pending = (Y pending) ∨ z
            var newPending = OperatorApplication(new DisjunctionOp, List(pending, z))
            newNext = AssignStmt(List(LhsId(pending)), List(newPending)) :: newNext
            // Update failed: failed = pending ∧ ¬a
            var newFailed = OperatorApplication(new ConjunctionOp, List(pending, OperatorApplication(new NegationOp, operands)))
            failExpr = OperatorApplication(new ConjunctionOp, List(OperatorApplication(new NegationOp, List(newFailed)), failExpr))
            newNext = AssignStmt(List(LhsId(failed)), List(newFailed)) :: newNext
          case OperatorApplication(op: NextTemporalOp, operands) =>
            var y_z = Identifier("y_" concat z.name)
            allDecls = StateVarsDecl(List(y_z), new BoolType) :: allDecls
            var pending = Identifier(spec.id.name concat z.name concat "_pending")
            allDecls = StateVarsDecl(List(pending), new BoolType) :: allDecls
            // Update pending: pending = z
            newNext = AssignStmt(List(LhsId(pending)), List(z)) :: newNext
            // Update failed: failed = Yz ∧ ¬a
            var newFailed = OperatorApplication(new ConjunctionOp, List(y_z, OperatorApplication(new NegationOp, operands)))
            failExpr = OperatorApplication(new ConjunctionOp, List(OperatorApplication(new NegationOp, List(newFailed)), failExpr))
            newNext = AssignStmt(List(LhsId(failed)), List(newFailed)) :: newNext
            // Update y_z
            newNext = AssignStmt(List(LhsId(y_z)), List(z)) :: newNext
          case OperatorApplication(op: UntilTemporalOp, operands) =>
            // this is a liveness property
          case OperatorApplication(op: FinallyTemporalOp, operands) =>
            // this is a liveness property
          case OperatorApplication(op: ReleaseTemporalOp, operands) =>
            // we use the following identity from wikipedia: a R b <==> b W (a && b)
            var pending = Identifier(spec.id.name concat z.name concat "_pending")
            allDecls = StateVarsDecl(List(pending), new BoolType) :: allDecls
            // Update pending: pending = (z ∨ (Y pending )) ∧ ¬(b ∧ a)
            var inner1 = OperatorApplication(new DisjunctionOp, List(z, pending))
            var inner2 = OperatorApplication(new NegationOp, List(OperatorApplication(new ConjunctionOp, List(operands.head, operands.last))))
            var newPending = OperatorApplication(new ConjunctionOp, List(inner1, inner2))
            newNext = AssignStmt(List(LhsId(pending)), List(z)) :: newNext
            // Update failed: failed = failed ∧ ¬b
            var newFailed = OperatorApplication(new ConjunctionOp, List(pending, OperatorApplication(new NegationOp, List(operands.last))))
            failExpr = OperatorApplication(new ConjunctionOp, List(OperatorApplication(new NegationOp, List(newFailed)), failExpr))
            newNext = AssignStmt(List(LhsId(failed)), List(newFailed)) :: newNext
          case OperatorApplication(op: WUntilTemporalOp, operands) =>
            var pending = Identifier(spec.id.name concat z.name concat "_pending")
            allDecls = StateVarsDecl(List(pending), new BoolType) :: allDecls
            // Update pending: pending = (z ∨ (Y pending )) ∧ ¬b
            var inner = OperatorApplication(new DisjunctionOp, List(z, pending))
            var newPending = OperatorApplication(new ConjunctionOp, List(inner, OperatorApplication(new NegationOp, List(operands.last))))
            newNext = AssignStmt(List(LhsId(pending)), List(z)) :: newNext
            // Update failed: failed = failed ∧ ¬a
            var newFailed = OperatorApplication(new ConjunctionOp, List(pending, OperatorApplication(new NegationOp, List(operands.head))))
            failExpr = OperatorApplication(new ConjunctionOp, List(OperatorApplication(new NegationOp, List(newFailed)), failExpr))
            newNext = AssignStmt(List(LhsId(failed)), List(newFailed)) :: newNext
          case _ =>
            // do we want to append instead of prepend?
            newNext = AssumeStmt(OperatorApplication(new ImplicationOp, List(z, expr)), None) :: newNext
        }
      }
    }
    // replace with new Next declaration
    allDecls = allDecls.filter(d => !d.isInstanceOf[NextDecl])
    allDecls = NextDecl(newNext) :: allDecls
    Some(Module(module.id, allDecls, module.cmds))
    * 
    */
  }
}

class LTLPropertyRewriter extends ASTRewriter(
    "LTLPropertyRewriter", new LTLPropertyRewriterPass())