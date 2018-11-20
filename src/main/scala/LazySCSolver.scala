package uclid
package lang

import com.typesafe.scalalogging.Logger

import scala.collection.mutable.ArrayBuffer

case class LazySCResult(e: smt.Expr, result: smt.SolverResult)
class LazySCSolver(simulator: SymbolicSimulator, solver: smt.Context) {
  val log = Logger(classOf[LazySCSolver])
  
  def checkExpr(solver: smt.Context, e: smt.Expr, assumes: List[smt.Expr]) = {
    solver.push()
    assumes.foreach(assume => solver.assert(assume))
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

  def getTaintInitLambda(init_lambda: smt.Lambda, scope: Scope, solver: smt.Context, hyperAssumes: List[smt.Expr]) = {
    //FIXME: Handle Arrays
    log.debug("The init hyperAssumes " + hyperAssumes.toString)
    log.debug("The init lambda " + init_lambda.toString)
    val taint_vars = init_lambda.ids.map(sym => simulator.newTaintSymbol(sym.id, smt.BoolType))
    val initSymTab1 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 1, scope)
    val initSymTab2 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 1, scope)
    val prevVars1 = simulator.getVarsInOrder(initSymTab1.map(_.swap), scope)
    val prevVars2 = simulator.getVarsInOrder(initSymTab2.map(_.swap), scope)
    val init_havocs = simulator.getHavocs(init_lambda.e)
    // Relies on the fact that getVarsInOrder returns variables in a particular order
    val taint_set = taint_vars.zip(prevVars1.flatten.zip(prevVars2.flatten))
    val hyperSelects = hyperAssumes.map(hypAssume => simulator.getHyperSelects(hypAssume)).flatten

    val subs = hyperSelects.map {
      expr =>
        val op = expr.op
        val exp = expr.operands
        op match {
          case smt.HyperSelectOp(i) =>

              val actual_params = if (i == 1) simulator.getVarsInOrder(initSymTab1.map(_.swap), scope).flatten
              else if (i == 2) simulator.getVarsInOrder(initSymTab2.map(_.swap), scope).flatten
              else throw new Utils.RuntimeError("HyperAssumes for more than 2 copies unsupported")

              val formal_params = init_lambda.ids
              assert(actual_params.length == formal_params.length)
              val matches = formal_params.zip(actual_params)
              val final_expr = simulator.substitute(exp(0), matches)
              (expr, final_expr)

          case _ =>
            throw new Utils.RuntimeError("Should never get here.")
        }
    }

    val substitutedHyperAssumes = hyperAssumes.map(assume => simulator.substitute(assume, subs))
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

    val init_conjunct1 = simulator.substitute(simulator.betaSubstitution(init_lambda, prevVars1.flatten), havoc_subs1)
    val init_conjunct2 = simulator.substitute(simulator.betaSubstitution(init_lambda, prevVars2.flatten), havoc_subs2)

    val setTaints = taint_set.map {
      taint_var =>
        log.debug("taint_var = " + taint_var._1.toString)
        log.debug("The tuple = " + taint_var._2.toString)
        val equality = smt.OperatorApplication(smt.EqualityOp, List(taint_var._2._1, taint_var._2._2))
        val not_expr = smt.OperatorApplication(smt.NegationOp, List(equality))
        val assumes = List(init_conjunct1, init_conjunct2) ++ substitutedHyperAssumes
        log.debug("The assumes " + assumes.toString)
        log.debug("The query expr " + not_expr.toString)
        checkExpr(solver, not_expr, assumes).result.result match {
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

  def getNextTaintLambda(nextLambda: smt.Lambda, hyperAssumes: List[smt.Expr]) = {
    //FIXME: HyperAssumes should be rewritten on every unroll of nextTaintLambda
    val supports = getSupports(nextLambda)
    log.debug("The next hyperAssumes " + hyperAssumes.toString)
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

  def getNewTaintVars(symTab: simulator.SymbolTable, scope: Scope) = {
    val reverse_map = symTab.map(_.swap)
    simulator.getVarsInOrder(reverse_map, scope).flatten.map {
      v =>
        simulator.newTaintSymbol(v.asInstanceOf[smt.Symbol].id, smt.BoolType)
    }

  }

  // Partitions a substituted smt conjunct into equalities having a symbol on the LHS and other assumes
  def partitionConjunct(e: smt.Expr) = {
    log.debug("-- The lambda Conjunct -- " + e.toString)
    val operands = e match {
      case smt.OperatorApplication(op, operands) =>
        if (op == smt.EqualityOp) List(e)
        else operands
      case smt.BooleanLit(true) => List()
      case _ => throw new Utils.RuntimeError("Not a lambda Expr.")
    }
    log.debug("--- The operands --- " + operands.toString)
    val equalities = operands.filter {
      operand =>
        operand match {
          case smt.OperatorApplication(op, opers) =>
            op == smt.EqualityOp
          case _ => false
        }
    }
    log.debug("--- The equalities --- " + equalities.toString)
    val stateUpdates = equalities.filter {
      operand =>
        operand match {
          case smt.OperatorApplication(op, opers) =>
            opers(0).isInstanceOf[smt.Symbol]
          case _ => false
        }
    }

    log.debug("--- The state updates --- " + stateUpdates.toString)
    val stateUpdateMap = stateUpdates.map {
      update =>
        update.asInstanceOf[smt.OperatorApplication].operands(0) -> update
    }.toMap


    val assumes = operands.filter{
      operand =>
        !stateUpdates.contains(operand) && operand.isInstanceOf[smt.OperatorApplication]
    }
    log.debug("--- The assumes ---" + assumes.toString)
    (stateUpdateMap, assumes)

  }
  // Applicable for only two copies
  def simulateLazySC(bound: Int, scope: Scope, label: String, filter : ((Identifier, List[ExprDecorator]) => Boolean)) = {

    val init_lambda = simulator.getInitLambda(false, true, false, scope, label, filter)
    val next_lambda = simulator.getNextLambda(init_lambda._3, true, false, scope, label, filter)
    val taintInitLambda = getTaintInitLambda(init_lambda._1, scope, solver, init_lambda._5)
    val taintNextLambda = getNextTaintLambda(next_lambda._1, List.empty)

    val num_copies = 2
    val numberOfSteps = bound
    val simRecord = new simulator.SimulationTable
    var prevVarTable = new ArrayBuffer[List[List[smt.Expr]]]()
    var havocTable = new ArrayBuffer[List[(smt.Symbol, smt.Symbol)]]()
    var prevTaintVarTable = new ArrayBuffer[List[smt.Expr]]()
    var taintAssumes = new ArrayBuffer[smt.Expr]()


    //FIXME: Remove newInputSymbols
    val taintSymTab = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 1, scope)
    val initTaintVars = getNewTaintVars(taintSymTab, scope)
    prevTaintVarTable += initTaintVars
    val initTaintConjunct = simulator.betaSubstitution(taintInitLambda, initTaintVars)
    taintAssumes += initTaintConjunct

    for (i <- 1 to num_copies) {

        var frames = new simulator.FrameTable
        val initSymTab = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 1, scope)
        frames += initSymTab
        var prevVars = simulator.getVarsInOrder(initSymTab.map(_.swap), scope)
        prevVarTable += prevVars
        val init_havocs = simulator.getHavocs(init_lambda._1.e)
        val havoc_subs = init_havocs.map {
          havoc =>
            val s = havoc.id.split("_")
            val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
            (havoc, simulator.newHavocSymbol(name, havoc.typ))
        }
        havocTable += havoc_subs
        val init_conjunct = simulator.substitute(simulator.betaSubstitution(init_lambda._1, prevVars.flatten), havoc_subs)
        if (i == 1) {
          simulator.addAssumptionToTree(init_conjunct, List.empty)
        }
        else {
          val firstInitVars = prevVarTable(0).flatten
          val secondInitVars = prevVarTable(1).flatten
          val partition = partitionConjunct(init_conjunct)

          assert(secondInitVars.length == prevTaintVarTable(0).length)
          assert(secondInitVars.length == firstInitVars.length)
          val taintMatches = secondInitVars.zip(firstInitVars zip prevTaintVarTable(0))
          log.debug(" ----- Partition Map ----- " + partition._1)
          log.debug(" ----- Init taint Matches ---- " + taintMatches.toString)
          taintMatches.foreach {
            v =>
              checkExpr(solver, smt.OperatorApplication(smt.NegationOp, List(v._2._2)), taintAssumes.toList).result.result match {
                case Some(true) =>  //Unsat and tainted, hence equal
                  val equality = smt.OperatorApplication(smt.EqualityOp, List(v._1, v._2._1))
                  log.debug("++ Added Equality ++ " + equality.toString)
                  simulator.addAssumptionToTree(equality, List.empty)
                case _ => // Sat, possibility of being unequal. Duplicate Expression
                  partition._1.get(v._1) match {
                    case Some(expr) =>
                      log.debug("## Added Duplicate ## " + (v._1, expr).toString)
                      simulator.addAssumptionToTree(expr, List.empty)
                    case None =>
                      log.debug("## Not Duplicated as variable not in lambda ##")
                  }

              }
          }
          partition._2.foreach {
            expr =>
              log.debug("Added INIT assumption to tree " + expr.toString)
              simulator.addAssumptionToTree(expr, List.empty)
          }
        }

        simRecord += frames


    }

    val hyperAssumesInit = simulator.rewriteHyperAssumes(
      init_lambda._1, 0, init_lambda._5, simRecord, 0, scope, prevVarTable.toList)
    hyperAssumesInit.foreach {
      hypAssume =>
        simulator.addAssumptionToTree(hypAssume, List.empty)
    }


    val asserts_init = simulator.rewriteAsserts(
      init_lambda._1, init_lambda._2, 0,
      prevVarTable(0).flatten.map(p => p.asInstanceOf[smt.Symbol]),
      simRecord.clone(), havocTable(0))

    asserts_init.foreach {
      assert =>
        // FIXME: simTable
        simulator.addAssertToTree(assert)
    }

    val asserts_init_hyper = simulator.rewriteHyperAsserts(
      init_lambda._1, 0, init_lambda._4, simRecord, 0, scope, prevVarTable.toList)
    asserts_init_hyper.foreach {
      assert =>
        // FIXME: simTable
        simulator.addAssertToTree(assert)
    }


    var symTabStep = simulator.symbolTable
    for (i <- 1 to numberOfSteps) {
      val nextTaintVars = getNewTaintVars(taintSymTab, scope)
      prevTaintVarTable += nextTaintVars
      val nextTaintConjunct = simulator.betaSubstitution(taintNextLambda, prevTaintVarTable(i - 1) ++ nextTaintVars)
      taintAssumes += nextTaintConjunct

      for (j <- 1 to num_copies) {
        symTabStep = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), i + 1, scope)
        simRecord(j - 1) += symTabStep
        val new_vars = simulator.getVarsInOrder(symTabStep.map(_.swap), scope)
        val next_havocs = simulator.getHavocs(next_lambda._1.e)
        val havoc_subs = next_havocs.map {
          havoc =>
            val s = havoc.id.split("_")
            val name = s.takeRight(s.length - 2).foldLeft("")((acc, p) => acc + "_" + p)
            (havoc, simulator.newHavocSymbol(name, havoc.typ))
        }
        val next_conjunct = simulator.substitute(simulator.betaSubstitution(next_lambda._1, (prevVarTable(j - 1) ++ new_vars).flatten), havoc_subs)
        //simulator.addAssumptionToTree(next_conjunct, List.empty)
        if (j == 1) {
          simulator.addAssumptionToTree(next_conjunct, List.empty)
        }
        else {
          val firstNextVars = prevVarTable(0).flatten
          val secondNextVars = new_vars.flatten
          val partition = partitionConjunct(next_conjunct)

          assert(secondNextVars.length == prevTaintVarTable(0).length)
          assert(secondNextVars.length == firstNextVars.length)
          val taintMatches = secondNextVars.zip(firstNextVars zip prevTaintVarTable(0))
          log.debug(" ----- Next Partition Map ----- " + partition._1)
          log.debug(" ----- Next taint Matches ---- " + taintMatches.toString)
          taintMatches.foreach {
            v =>
              checkExpr(solver, smt.OperatorApplication(smt.NegationOp, List(v._2._2)), taintAssumes.toList).result.result match {
                case Some(true) =>  //Unsat and tainted, hence equal
                  val equality = smt.OperatorApplication(smt.EqualityOp, List(v._1, v._2._1))
                  log.debug("++ Added Equality ++ " + equality.toString)
                  simulator.addAssumptionToTree(equality, List.empty)
                case _ => // Sat, possibility of being unequal. Duplicate Expression
                  partition._1.get(v._1) match {
                    case Some(expr) =>
                      log.debug("## Added Duplicate ## " + (v._1, expr).toString)
                      simulator.addAssumptionToTree(expr, List.empty)
                    case None =>
                  }

              }
          }
          partition._2.foreach {
            expr =>
              log.debug("Added NEXT assumption to tree " + expr.toString)
              simulator.addAssumptionToTree(expr, List.empty)
          }
        }
        havocTable(j - 1) = havoc_subs
        prevVarTable(j - 1) = new_vars
      }

      val hyperAssumesNext = simulator.rewriteHyperAssumes(next_lambda._1, numberOfSteps, next_lambda._5, simRecord, i, scope, prevVarTable.toList)
      hyperAssumesNext.foreach {
        hypAssume =>
          simulator.addAssumptionToTree(hypAssume, List.empty)
      }
      // Asserting on-HyperInvariant assertions
      // FIXME: simTable
      val asserts_next = simulator.rewriteAsserts(
        next_lambda._1, next_lambda._2, i,
        simulator.getVarsInOrder(simRecord(0)(i - 1).map(_.swap), scope).flatten.map(p => p.asInstanceOf[smt.Symbol]) ++
          prevVarTable(0).flatten.map(p => p.asInstanceOf[smt.Symbol]), simRecord.clone(), havocTable(0))
      asserts_next.foreach {
        assert =>
          simulator.addAssertToTree(assert)
      }
      // FIXME: simTable
      simulator.defaultLog.debug("i: {}", i)
      val asserts_next_hyper = simulator.rewriteHyperAsserts(next_lambda._1, numberOfSteps, next_lambda._4, simRecord, i, scope, prevVarTable.toList)
      asserts_next_hyper.foreach {
        assert => {
          simulator.addAssertToTree(assert)
        }
      }
    }
    simulator.symbolTable = symTabStep


  }
}