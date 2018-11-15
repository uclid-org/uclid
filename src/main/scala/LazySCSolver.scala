package uclid
package lang

import com.typesafe.scalalogging.Logger

case class LazySCResult(e: smt.Expr, result: smt.SolverResult)
class LazySCSolver(simulator: SymbolicSimulator) {
  val log = Logger(classOf[LazySCSolver])
  
  def checkExpr(solver: smt.Context, e: smt.Expr) = {
    solver.push()
    solver.assert(e)
    val sat = solver.check()
    val result = sat.result match {
      case Some(true) => smt.SolverResult(Some(false), sat.model)
      case Some(false) => smt.SolverResult(Some(true), sat.model)
      case None => smt.SolverResult(None, None)
    }
    solver.pop()
    LazySCResult(e, result)
  }

  def getTaintInitLambda(init_lambda: smt.Lambda, scope: Scope, solver: smt.Context) = {
    //FIXME: Handle Arrays
    val taint_vars = init_lambda.ids.map(sym => simulator.newTaintSymbol(sym.id, smt.BoolType))
    val initSymTab1 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 1, scope)
    val initSymTab2 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 1, scope)
    val prevVars1 = simulator.getVarsInOrder(initSymTab1.map(_.swap), scope)
    val prevVars2 = simulator.getVarsInOrder(initSymTab2.map(_.swap), scope)
    val init_havocs = simulator.getHavocs(init_lambda.e)
    // Relies on the fact that getVarsInOrder returns variables in a particular order
    val taint_set = taint_vars.zip(prevVars1.flatten.zip(prevVars2.flatten))

    val havoc_subs1 = init_havocs.map {
      havoc =>
        val s = havoc.id.split("_")
        val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
        (havoc, simulator.newHavocSymbol(name, havoc.typ))
    }

    val havoc_subs2 = init_havocs.map {
      havoc =>
        val s = havoc.id.split("_")
        val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
        (havoc, simulator.newHavocSymbol(name, havoc.typ))
    }

    val init_conjunct1 = simulator.substitute(simulator.betaSubstitution(init_lambda, prevVars1), havoc_subs1)
    val init_conjunct2 = simulator.substitute(simulator.betaSubstitution(init_lambda, prevVars2), havoc_subs2)

    val setTaints = taint_set.map {
      taint_var =>
        log.debug("taint_var = " + taint_var._1.toString)
        log.debug("The tuple = " + taint_var._2.toString)
        val equality = smt.OperatorApplication(smt.EqualityOp, List(taint_var._2._1, taint_var._2._2))
        val not_expr = smt.OperatorApplication(smt.NegationOp, List(equality))
        val query_expr = smt.OperatorApplication(smt.ConjunctionOp, List(init_conjunct1, init_conjunct2, not_expr))
        log.debug("The query expr " + query_expr.toString)
        checkExpr(solver, query_expr).result.result match {
          case Some(true) =>
            log.debug("equal")
            taint_var._1
          case _ =>
            log.debug("unequal")
            smt.OperatorApplication(smt.NegationOp, List(taint_var._1))
        }
    }

    val taint_conjunct = if (setTaints.length > 1) smt.OperatorApplication(smt.ConjunctionOp, setTaints)
    else if (setTaints.length == 0) smt.BooleanLit(true)
    else setTaints(0)
    log.debug(" --- Taint Conjunct --- " + taint_conjunct.toString)
    val lambda = smt.Lambda(taint_vars, taint_conjunct)
    log.debug("Taint init lambda: " + lambda.toString())
    lambda
  }

  def getNextTaintLambda(nextLambda: smt.Lambda) = {
    val supports = getSupports(nextLambda)
    log.debug("The lambda " + nextLambda.toString)
    log.debug("The support set " + supports)
    val nextVars = nextLambda.ids.takeRight(nextLambda.ids.length / 2)
    val prevVars = nextLambda.ids.take(nextLambda.ids.length / 2)
    log.debug("The next vars " + nextVars.toString)
    //FIXME: Handle Arrays
    val m : Map[smt.Symbol, smt.Symbol] = Map.empty
    val nextVarMap = nextVars.foldLeft(m) {
      (acc, sym) =>
        acc + (sym -> simulator.newTaintSymbol(sym.id, smt.BoolType))
    }
    val prevVarMap = prevVars.foldLeft(m) {
      (acc, sym) =>
        acc + (sym -> simulator.newTaintSymbol(sym.id, smt.BoolType))
    }

    val lambdaConjuncts = nextVarMap.map {
      p =>
        val support_set = supports(p._1).toList.map(sym => prevVarMap(sym))
        val conjunct = if ( support_set.length > 1) smt.OperatorApplication(smt.ConjunctionOp, support_set)
        else if (support_set.length == 0) smt.BooleanLit(true)
        else support_set(0)
        smt.OperatorApplication(smt.EqualityOp, List(p._2, conjunct))
    }.toList

    val conjunct = if (lambdaConjuncts.length > 1) smt.OperatorApplication(smt.ConjunctionOp, lambdaConjuncts)
    else if (lambdaConjuncts.length == 0) smt.BooleanLit(true)
    else lambdaConjuncts(0)
    val lambda = smt.Lambda(prevVars.map(p => prevVarMap(p)) ++ nextVars.map(p => nextVarMap(p)),
      conjunct)
    log.debug("Taint Next Lambda " + lambda.toString)

    lambda
  }

  def getSupports(lambda: smt.Lambda): Map[smt.Symbol, Set[smt.Symbol]] = {
    assert(lambda.ids.length % 2 == 0)
    if (lambda.e.isInstanceOf[smt.BooleanLit]) {
      val primed_vars = lambda.ids.takeRight(lambda.ids.length / 2) // Assuming prevs are followed by nexts
      val non_primed_vars = lambda.ids.take(lambda.ids.length / 2)
      primed_vars.zip(non_primed_vars).map(p => p._1 -> Set(p._2)).toMap
    }
    else {
      val primedVars = lambda.ids.takeRight(lambda.ids.length / 2) // Assuming prevs are followed by nexts
      val nonPrimedVars = lambda.ids.take(lambda.ids.length / 2)
      log.debug("The primed_vars " + primedVars.toString)
      log.debug("The non-primed vars " + nonPrimedVars.toString)

      val matches = primedVars.zip(nonPrimedVars).map(p => p._1 -> p._2).toMap
      val opapp = lambda.e.asInstanceOf[smt.OperatorApplication]
      val operator_apps = opapp.operands.filter(exp => exp.isInstanceOf[smt.OperatorApplication])
      val equalities = operator_apps.map(p => p.asInstanceOf[smt.OperatorApplication]).
        filter(exp =>
          exp.op match {
            case smt.EqualityOp => true
            case _ => false
          })
      val var_map = equalities.map {
        eq =>
          if (eq.operands(0).isInstanceOf[smt.Symbol])
            eq.operands(0).asInstanceOf[smt.Symbol] -> eq.operands(1)
          else //if (eq.operands(0).isInstanceOf[smt.OperatorApplication])
            eq.operands(0).asInstanceOf[smt.OperatorApplication].operands(0).asInstanceOf[smt.Symbol] -> eq.operands(1)

      }.toMap
      //UclidMain.println("The var map " + var_map.toString)
      // Map from primed variables to their dependencies
      var dependency_map: Map[smt.Symbol, Set[smt.Symbol]] = Map.empty
      primedVars.foreach(p => getDependencies(p))

      def getDependencies(v: smt.Symbol): Set[smt.Symbol] = {
        val eq_exp = var_map.get(v) match {
          case Some(exp) => exp
          case None => {
            dependency_map = dependency_map + (v -> Set())
            return Set()
          }
        }
        val vars = getVars(eq_exp)
        val dps = vars.map {
          sym =>
            if (nonPrimedVars.contains(sym)) {
              Set(sym)
            }
            else {
              val dep = dependency_map.get(sym) match {
                case Some(deps) => deps
                case None => getDependencies(sym)
              }
              dep
            }
        }.flatten.toSet //+ matches(v)
        dependency_map = dependency_map + (v -> dps)
        dps
      }

      dependency_map
    }
  }

  def getVars(e: smt.Expr): List[smt.Symbol] = {
    e match {
      case smt.Symbol(id, symbolTyp) => List(e.asInstanceOf[smt.Symbol])
      case smt.IntLit(n) => List()
      case smt.BooleanLit(b) => List()
      case smt.BitVectorLit(bv, w) => List()
      case smt.EnumLit(id, eTyp) => List()
      case smt.ConstArray(v, arrTyp) => List()
      case smt.MakeTuple(args) => args.flatMap(e => getVars(e))
      case opapp : smt.OperatorApplication =>
        val op = opapp.op
        val args = opapp.operands.flatMap(exp => getVars(exp))
        args
      //UclidMain.println("Crashing Here" + op.toString)
      case smt.ArraySelectOperation(a,index) =>  getVars(a) ++ index.flatMap(e => getVars(e))
      case smt.ArrayStoreOperation(a,index,value) =>
        getVars(a) ++ index.flatMap(e => getVars(e)) ++ getVars(value)
      case smt.FunctionApplication(f, args) =>
        args.flatMap(arg => getVars(arg))
      case _ =>
        throw new Utils.UnimplementedException("'" + e + "' is not yet supported.")
    }
  }
}