package uclid
package lang

import com.typesafe.scalalogging.Logger

import scala.collection.mutable.ArrayBuffer

case class LazySCResult(e: smt.Expr, result: smt.SolverResult)
class LazySCSolver(simulator: SymbolicSimulator, solver: smt.Context) {
  val log = Logger(classOf[LazySCSolver])
  type TaintSymbolTable = Map[Identifier, List[smt.Expr]]
  type TaintFrameTable = ArrayBuffer[TaintSymbolTable]
  type TaintSymbolHyperTable = Map[Identifier, Array[smt.Expr]]
  type TaintSimulationTable = ArrayBuffer[TaintFrameTable]
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
    val taint_vars = init_lambda.ids.map(sym => getNewTaintSymbol(sym))
    var additionalConstraints = new ArrayBuffer[smt.Expr]()

    val initSymTab1 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 0, scope)
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

              val actual_params = if (i == 1) prevVars1.flatten
              else if (i == 2) prevVars2.flatten
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

    val setTaints = taint_set.flatMap {
      taint_var =>
        //log.debug("taint_var = " + taint_var.toString)
        log.debug("The tuple = " + taint_var.toString)
        val equality = smt.OperatorApplication(smt.EqualityOp, List(taint_var._2._1, taint_var._2._2))
        val not_expr = smt.OperatorApplication(smt.NegationOp, List(equality))
        val assumes = List(init_conjunct1, init_conjunct2) ++ substitutedHyperAssumes
        val isArray = taint_var._1.length == 2

        log.debug("The assumes " + assumes.toString)
        log.debug("The query expr " + not_expr.toString)
        checkExpr(solver, not_expr, assumes).result.result match {
          case Some(true) =>
            log.debug("equal")
            if (isArray) {
              //val taint1 = simulator.newTaintSymbol(taint_var._1.id, smt.BoolType)
              val arrTyp = taint_var._1(1).typ.asInstanceOf[smt.ArrayType]
              val taint2 = smt.ConstArray(smt.BooleanLit(true), arrTyp)
              val exp = smt.OperatorApplication(smt.EqualityOp, List(taint_var._1(1), taint2))
              additionalConstraints += exp
              List(taint_var._1(0))
            }
            else {
              List(taint_var._1(0))
            }
          case _ =>
            log.debug("unequal")
            if (isArray) {
              //val taint1 = simulator.newTaintSymbol(taint_var._1.id, smt.BoolType)
              val arrTyp = taint_var._1(1).typ.asInstanceOf[smt.ArrayType]
              val taint2 = smt.ConstArray(smt.BooleanLit(false), arrTyp)
              val exp = smt.OperatorApplication(smt.EqualityOp, List(taint_var._1(1), taint2))
              additionalConstraints += exp
              List(taint_var._1(0))
            }
            else {
              List(smt.OperatorApplication(smt.NegationOp, List(taint_var._1(0))))
            }
            //smt.OperatorApplication(smt.NegationOp, List(taint_var._1))
        }
    }

    val taintsWithConstraints = setTaints ++ additionalConstraints
    val taint_conjunct = if (taintsWithConstraints.length > 1) smt.OperatorApplication(smt.ConjunctionOp, taintsWithConstraints)
    else if (taintsWithConstraints.isEmpty) smt.BooleanLit(true)
    else taintsWithConstraints.head


    log.debug(" --- Taint Conjunct --- " + taint_conjunct.toString)
    val lambda = smt.Lambda(taint_vars.flatten, taint_conjunct)
    log.debug("Taint init lambda: " + lambda.toString())
    lambda
  }

  def computeAConjunct(nextLambda: smt.Lambda, hyperAssumes: List[smt.Expr], assumes: List[smt.Expr], scope: Scope, taintMap: Map[smt.Expr, List[smt.Expr]]) = {

    val initSymTab1 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 1, scope)
    val initSymTab2 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 2, scope)
    val nextSymTab1 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 3, scope)
    val nextSymTab2 = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), 4, scope)

    val prevVars1 = simulator.getVarsInOrder(initSymTab1.map(_.swap), scope)
    val prevVars2 = simulator.getVarsInOrder(initSymTab2.map(_.swap), scope)
    val nextVars1 = simulator.getVarsInOrder(nextSymTab1.map(_.swap), scope)
    val nextVars2 = simulator.getVarsInOrder(nextSymTab2.map(_.swap), scope)

    val prevLambdaVars = nextLambda.ids.take(nextLambda.ids.length / 2)
    val nextLambdaVars = nextLambda.ids.takeRight(nextLambda.ids.length / 2)

    val matches1 = nextLambda.ids.zip(prevVars1.flatten ++ nextVars1.flatten)
    val matches2 = nextLambda.ids.zip(prevVars2.flatten ++ nextVars2.flatten)

    val hyperSelects = hyperAssumes.map(hypAssume => simulator.getHyperSelects(hypAssume)).flatten
    val subs = hyperSelects.map {
      expr =>
        val op = expr.op
        val exp = expr.operands
        op match {
          case smt.HyperSelectOp(i) =>

            val actual_params = if (i == 1) prevVars1.flatten ++ nextVars1.flatten
            else if (i == 2) prevVars2.flatten ++ nextVars2.flatten
            else throw new Utils.RuntimeError("HyperAssumes for more than 2 copies unsupported")

            val formal_params = nextLambda.ids
            assert(actual_params.length == formal_params.length)
            val matches = formal_params.zip(actual_params)
            val final_expr = simulator.substitute(exp(0), matches)
            (expr, final_expr)

          case _ =>
            throw new Utils.RuntimeError("Should never get here.")
        }
    }
    val substitutedHyperAssumes = hyperAssumes.map(assume => simulator.substitute(assume, subs))
    val substitutedAssumes1 = assumes.map(assume => simulator.substitute(assume, matches1))
    val substitutedAssumes2 = assumes.map(assume => simulator.substitute(assume, matches2))
    val matchNexts = nextLambdaVars.zip(nextVars1.flatten.zip(nextVars2.flatten))
    val setTaints = matchNexts.flatMap {
      nextVar =>
        val equality = smt.OperatorApplication(smt.EqualityOp, List(nextVar._2._1, nextVar._2._2))
        val not_expr = smt.OperatorApplication(smt.NegationOp, List(equality))
        val assumes = substitutedAssumes1 ++ substitutedAssumes2 ++ substitutedHyperAssumes
        val isArray = nextVar._1.typ.isInstanceOf[smt.ArrayType]
        log.debug("-- The assumes in A Func -- " + assumes.toString)
        log.debug("-- The query_expr in A Func -- " + not_expr.toString)
        checkExpr(solver, not_expr, assumes).result.result match {
          case Some(true) =>
            log.debug("equal in A Function")
            if (isArray) {
              val arrTyp = nextVar._1.typ.asInstanceOf[smt.ArrayType]
              val constArray = smt.ConstArray(smt.BooleanLit(true), arrTyp)
              val exp = smt.OperatorApplication(smt.EqualityOp, List(taintMap(nextVar._1)(1), constArray))
              Some(exp)
            }
            else {
              Some(taintMap(nextVar._1)(0))
            }
          case _ =>
            log.debug("unequal in A Function")
            None
        }
    }
    val conjunct = if (setTaints.length == 1) setTaints(0)
    else if (setTaints.length == 0) smt.BooleanLit(true)
    else smt.OperatorApplication(smt.ConjunctionOp, setTaints)

    log.debug("--- The A Conjunct --- " + conjunct)
    conjunct


  }

  def getSupportsArray(lambda: smt.Lambda): Map[smt.Expr, Set[smt.Expr]] = {
    Map.empty
  }

  def getNewTaintSymbol(sym: smt.Symbol) = {
    sym.typ match {
      case smt.ArrayType(inTypes, _) =>
        val taint1 = simulator.newTaintSymbol(sym.id, smt.BoolType)
        val taint2 = simulator.newTaintSymbol(sym.id, smt.ArrayType(inTypes, smt.BoolType))
        List(taint1, taint2)
      case _ => List(simulator.newTaintSymbol(sym.id, smt.BoolType))
    }
  }

  def getTaintExprs(nextLambda: smt.Lambda, prevTaintVars: Map[smt.Expr, List[smt.Symbol]], nextTaintVars: Map[smt.Expr, List[smt.Symbol]]) = {

    val nextArrayVars = nextLambda.ids.takeRight(nextLambda.ids.length / 2).filter(sym => sym.typ match {
      case smt.ArrayType(_,_) => true
      case _ => false
    })

    val prevArrayVars = nextLambda.ids.take(nextLambda.ids.length / 2).filter(sym => sym.typ match {
      case smt.ArrayType(_,_) => true
      case _ => false
    })

    val opapp = nextLambda.e.asInstanceOf[smt.OperatorApplication]
    val operator_apps = opapp.operands.filter(exp => exp.isInstanceOf[smt.OperatorApplication])
    val equalities = operator_apps.map(p => p.asInstanceOf[smt.OperatorApplication]).
      filter(exp =>
        exp.op match {
          case smt.EqualityOp => true
          case _ => false
        })

    val arrayEqualities = equalities.filter {
      eq =>
        val lhs = eq.operands(0)
        if (lhs.typ.isInstanceOf[smt.ArrayType]) {
          true
        }
        else {
          false
        }
    }

    val nonArrayEqualities = equalities.filter {
      eq =>
        val lhs = eq.operands(0)
        if (lhs.typ.isInstanceOf[smt.ArrayType]) {
          false
        }
        else {
          true
        }
    }

    val taints1 = nonArrayEqualities.map {
      eq =>
        val nextTaintVar = nextTaintVars(eq.operands(0))
        val t1 = getT1Taint(eq.operands(1), prevTaintVars)
        val t1Conjunct = smt.OperatorApplication(smt.EqualityOp, List(nextTaintVar(0), setToConjunct(t1)))
        t1Conjunct
    }


    val taints2 = arrayEqualities.flatMap {
      eq =>
        val nextTaintVar = nextTaintVars(eq.operands(0))
        val t1 = getT1Taint(eq.operands(1), prevTaintVars)
        val t2 = getT2Taint(eq.operands(1), prevTaintVars)
        val t1Conjunct = smt.OperatorApplication(smt.EqualityOp, List(nextTaintVar(0), setToConjunct(t1)))
        val t2Conjunct = smt.OperatorApplication(smt.EqualityOp, List(nextTaintVar(1), setToConjunct(t2)))
        List(t1Conjunct, t2Conjunct)
    } ++ taints1

    if (taints2.length > 1) smt.OperatorApplication(smt.ConjunctionOp, taints2)
    else if (taints2.length == 1) taints2(0)
    else smt.BooleanLit(true)


  }

  def getNextTaintLambdaV2(nextLambda: smt.Lambda, hyperAssumes: List[smt.Expr], assumes: List[smt.Expr], scope: Scope) = {
    val m: Map[smt.Expr, List[smt.Symbol]] = Map.empty
    val nextVars = nextLambda.ids.takeRight(nextLambda.ids.length / 2)
    val prevVars = nextLambda.ids.take(nextLambda.ids.length / 2)

    val prevTaintVars = prevVars.foldLeft(m) {
      (acc, sym) =>
        acc + (sym -> getNewTaintSymbol(sym))
    }

    val nextTaintVars = nextVars.foldLeft(m) {
      (acc, sym) =>
        acc + (sym -> getNewTaintSymbol(sym))
    }

    val taintExprs = getTaintExprs(nextLambda, prevTaintVars, nextTaintVars)
    val inputs = prevVars.flatMap(v => prevTaintVars(v)) ++ nextVars.flatMap(v => nextTaintVars(v))
    val additionalConjunct = computeAConjunct(nextLambda, hyperAssumes, assumes,scope, nextTaintVars)
    val conjuncts = List(taintExprs) ++ List(additionalConjunct)
    val finalConjunct = if (conjuncts.length > 1) smt.OperatorApplication(smt.ConjunctionOp, conjuncts)
                        else if (conjuncts.length == 1) conjuncts(0)
                        else smt.BooleanLit(true)

    val lambda = smt.Lambda(inputs, finalConjunct)
    log.debug("Taint next lambda " + lambda.toString)
    lambda

  }

  def setToConjunct(s: Set[smt.Expr]): smt.Expr = {
    val l = s.toList
    if (l.length > 1) smt.OperatorApplication(smt.ConjunctionOp, l)
    else if (l.length == 1) l(0)
    else smt.BooleanLit(true)

  }

  def getT2Taint(e: smt.Expr, prevVarTaints: Map[smt.Expr, List[smt.Expr]]): Set[smt.Expr] = {
    e match {

      case smt.Symbol(id, symbolTyp) => symbolTyp match {
        case smt.ArrayType(inTypes, outType) => Set(prevVarTaints(e)(1))
        case _ => throw new Utils.UnimplementedException("T2 taint of non-array type.")
      }
      case smt.IntLit(n) => Set()
      case smt.BooleanLit(b) => Set()
      case smt.BitVectorLit(bv, w) => Set()
      case smt.EnumLit(id, eTyp) => Set()
      case smt.ConstArray(v, arrTyp) => Set()
      case smt.MakeTuple(args) => args.flatMap(e => getT2Taint(e, prevVarTaints)).toSet
      case opapp : smt.OperatorApplication =>
        val op = opapp.op
        if (op == smt.ITEOp) {
          val if_taint = setToConjunct(getT2Taint(opapp.operands(1), prevVarTaints))
          val else_taint = setToConjunct(getT2Taint(opapp.operands(2), prevVarTaints))
          Set(smt.OperatorApplication(smt.ITEOp, List(opapp.operands(0), if_taint, else_taint)))
        } else
          throw new Utils.UnimplementedException("T2 taint not defined for opp app.")
        /*val op = opapp.op
        val args = opapp.operands.flatMap(exp => getT2Taint(exp, prevVarTaints)).toSet
        args*/
      //UclidMain.println("Crashing Here" + op.toString)
      case smt.ArraySelectOperation(a,index) =>
        throw new Utils.UnimplementedException("T2 taint not defined for array store.")
      case smt.ArrayStoreOperation(a,index,value) =>
          val t2_a = getT2Taint(a, prevVarTaints)
          val t1_val = setToConjunct(getT1Taint(value, prevVarTaints))
          assert(t2_a.toList.length == 1)
          Set(smt.ArrayStoreOperation(t2_a.toList(0), index, t1_val))
      case smt.FunctionApplication(f, args) =>
        throw new Utils.UnimplementedException("T2 taint not defined for func app.")
      case _ =>
        throw new Utils.UnimplementedException("'" + e + "' is not yet supported.")
    }
  }

  def getT1Taint(e: smt.Expr, prevVarTaints: Map[smt.Expr, List[smt.Expr]]): Set[smt.Expr] = {
    e match {
      //T1 taint of arrays and non arrays
      case smt.Symbol(id, symbolTyp) => Set(prevVarTaints(e)(0))
      case smt.IntLit(n) => Set()
      case smt.BooleanLit(b) => Set()
      case smt.BitVectorLit(bv, w) => Set()
      case smt.EnumLit(id, eTyp) => Set()
      case smt.ConstArray(v, arrTyp) => Set()
      case smt.MakeTuple(args) => args.flatMap(e => getT1Taint(e, prevVarTaints)).toSet
      case opapp : smt.OperatorApplication =>
        if (opapp.op == smt.ITEOp) {
          val t1_if = setToConjunct(getT1Taint(opapp.operands(1), prevVarTaints))
          val t1_else = setToConjunct(getT1Taint(opapp.operands(2), prevVarTaints))
          Set(smt.OperatorApplication(smt.ITEOp, List(opapp.operands(0), t1_if, t1_else)))
        }
        else {
          val op = opapp.op
          val args = opapp.operands.flatMap(exp => getT1Taint(exp, prevVarTaints)).toSet
          args
        }
      //UclidMain.println("Crashing Here" + op.toString)
      case smt.ArraySelectOperation(a,index) =>
        val idx_taints = index.flatMap(idx => getT1Taint(idx, prevVarTaints)).toSet
        val t2_a = setToConjunct(getT2Taint(a, prevVarTaints))
        getT1Taint(a, prevVarTaints) ++ Set(smt.ArraySelectOperation(t2_a, index)) ++ idx_taints

      case smt.ArrayStoreOperation(a,index,value) =>
        index.flatMap(idx => getT1Taint(idx, prevVarTaints)).toSet ++ getT1Taint(a, prevVarTaints)
      case smt.FunctionApplication(f, args) =>
        args.flatMap(arg => getT1Taint(arg, prevVarTaints)).toSet
      case _ =>
        throw new Utils.UnimplementedException("'" + e + "' is not yet supported.")
    }
  }


  def getNextTaintLambda(nextLambda: smt.Lambda, hyperAssumes: List[smt.Expr], assumes: List[smt.Expr], scope: Scope) = {
    //FIXME: HyperAssumes should be rewritten on every unroll of nextTaintLambda
    val supports = getSupports(nextLambda)
    log.debug("The next hyperAssumes " + hyperAssumes.toString)
    log.debug("The lambda " + nextLambda.toString)
    log.debug("The support set " + supports)

    val nextVars = nextLambda.ids.takeRight(nextLambda.ids.length / 2).filter(sym => sym.typ match {
      case smt.ArrayType(_,_) => false
      case _ => true
    })

    val prevVars = nextLambda.ids.take(nextLambda.ids.length / 2).filter(sym => sym.typ match {
      case smt.ArrayType(_,_) => false
      case _ => true
    })


    log.debug("The next vars " + nextVars.toString)
    // TODO: Compute the correct order of taintVars
    // Array taint var corresponds to t1 followed by t2
    //FIXME: Handle Arrays
    val m : Map[smt.Expr, List[smt.Expr]] = Map.empty
    val nextVarMap = nextVars.foldLeft(m) {
      (acc, sym) =>
        acc + (sym -> List(getNewTaintSymbol(sym)(0)))
    }
    val prevVarMap = prevVars.foldLeft(m) {
      (acc, sym) =>
        acc + (sym -> List(getNewTaintSymbol(sym)(0)))
    }


    val lambdaConjuncts = nextVarMap.map {
      p =>
        val support_set = supports(p._1.asInstanceOf[smt.Symbol]).toList.map(sym => prevVarMap(sym)(0))
        val conjunct = if ( support_set.length > 1) smt.OperatorApplication(smt.ConjunctionOp, support_set)
        else if (support_set.length == 0) smt.BooleanLit(false)
        else support_set(0)
        smt.OperatorApplication(smt.ImplicationOp, List(conjunct, p._2(0)))
    }.toList

    val addlConjunct = computeAConjunct(nextLambda, hyperAssumes, assumes, scope, nextVarMap)
    val conjunct = if (lambdaConjuncts.length > 1) smt.OperatorApplication(smt.ConjunctionOp, lambdaConjuncts)
    else if (lambdaConjuncts.length == 0) smt.BooleanLit(true)
    else lambdaConjuncts(0)
    val lambda = smt.Lambda(prevVars.map(p => prevVarMap(p)(0).asInstanceOf[smt.Symbol]) ++ nextVars.map(p => nextVarMap(p)(0).asInstanceOf[smt.Symbol]),
      smt.OperatorApplication(smt.ConjunctionOp, List(addlConjunct, conjunct)))
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
    simulator.getVarsInOrder(reverse_map, scope).flatten.flatMap {
      v =>
        getNewTaintSymbol(v.asInstanceOf[smt.Symbol])
    }

  }

  def getTaintSymbolTable(scope : Scope) : TaintSymbolTable = {
    scope.map.foldLeft(Map.empty[Identifier, List[smt.Expr]]){
      (mapAcc, decl) => {
        decl._2 match {
          case Scope.ConstantVar(id, typ) => mapAcc + (id -> getNewTaintSymbol(simulator.newConstantSymbol(id.name, smt.Converter.typeToSMT(typ))))
          case Scope.Function(id, typ) => mapAcc + (id -> getNewTaintSymbol(simulator.newConstantSymbol(id.name, smt.Converter.typeToSMT(typ))))
          case Scope.EnumIdentifier(id, typ) => mapAcc + (id -> List(smt.EnumLit(id.name, smt.EnumType(typ.ids.map(_.toString)))))
          case Scope.InputVar(id, typ) => mapAcc + (id -> getNewTaintSymbol(simulator.newInitSymbol(id.name, smt.Converter.typeToSMT(typ))))
          case Scope.OutputVar(id, typ) => mapAcc + (id -> getNewTaintSymbol(simulator.newInitSymbol(id.name, smt.Converter.typeToSMT(typ))))
          case Scope.StateVar(id, typ) => mapAcc + (id -> getNewTaintSymbol(simulator.newInitSymbol(id.name, smt.Converter.typeToSMT(typ))))
          case Scope.SharedVar(id, typ) => mapAcc + (id -> getNewTaintSymbol(simulator.newInitSymbol(id.name, smt.Converter.typeToSMT(typ))))
          case _ => mapAcc
        }
      }
    }
  }

  def newTaintInputSymbols(st : TaintSymbolTable, step : Int, scope : Scope) : TaintSymbolTable = {
    scope.map.foldLeft(st)((acc, decl) => {
      decl._2 match {
        case Scope.InputVar(id, typ) => acc + (id -> getNewTaintSymbol(simulator.newInputSymbol(id.name, step, smt.Converter.typeToSMT(typ))))
        case _ => acc
      }
    })
  }

  def getTaintVarsInOrder(map: Map[List[smt.Expr], Identifier], scope: Scope) : List[List[smt.Expr]] = {
    val ids = map.map(p => p._2).toList
    val reverse_map = map.map(_.swap)
    val const_vars = ids.filter(id => scope.get(id).get match {
      case Scope.ConstantVar(id, typ) => true
      case _ => false
    }).flatMap(id => reverse_map(id)).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 5).foldLeft(s(4))((acc, p) => acc + "_" + p)
        name
    }
    /*val func_vars = ids.filter(id => scope.get(id).get match {
      case Scope.Function(id, typ) => true
      case _ => false
    }).map(id => reverse_map.get(id).get)
    */
    val input_vars = ids.filter(id => scope.get(id).get match {
      case Scope.InputVar(id, typ) => true
      case _ => false
    }).flatMap(id => reverse_map(id)).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 5).foldLeft(s(4))((acc, p) => acc + "_" + p)
        name
    }
    val output_vars = ids.filter(id => scope.get(id).get match {
      case Scope.OutputVar(id, typ) => true
      case _ => false
    }).flatMap(id => reverse_map(id)).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 5).foldLeft(s(4))((acc, p) => acc + "_" + p)
        name
    }
    val state_vars = ids.filter(id => scope.get(id).get match {
      case Scope.StateVar(id, typ) => true
      case _ => false
    }).flatMap(id => reverse_map(id)).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 5).foldLeft(s(4))((acc, p) => acc + "_" + p)
        name
    }
    val shared_vars = ids.filter(id => scope.get(id).get match {
      case Scope.SharedVar(id, typ) => true
      case _ => false
    }).flatMap(id => reverse_map(id)).sortBy{
      v =>
        val s = v.toString.split("_")
        val name = s.takeRight(s.length - 5).foldLeft(s(4))((acc, p) => acc + "_" + p)
        name
    }
    List(const_vars, input_vars, output_vars, state_vars, shared_vars)

  }
  // Partitions a substituted smt conjunct into equalities having a symbol on the LHS and other assumes
  def partitionConjunct(e: smt.Expr) = {
    //log.debug("-- The lambda Conjunct -- " + e.toString)
    val operands = e match {
      case smt.OperatorApplication(op, operands) =>
        if (op == smt.EqualityOp) List(e)
        else operands
      case smt.BooleanLit(true) => List()
      case _ => throw new Utils.RuntimeError("Not a lambda Expr.")
    }
    //log.debug("--- The operands --- " + operands.toString)
    val equalities = operands.filter {
      operand =>
        operand match {
          case smt.OperatorApplication(op, opers) =>
            op == smt.EqualityOp
          case _ => false
        }
    }
    //log.debug("--- The equalities --- " + equalities.toString)
    val stateUpdates = equalities.filter {
      operand =>
        operand match {
          case smt.OperatorApplication(op, opers) =>
            opers(0).isInstanceOf[smt.Symbol]
          case _ => false
        }
    }

    //log.debug("--- The state updates --- " + stateUpdates.toString)
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
    val taintNextLambda = getNextTaintLambdaV2(next_lambda._1, next_lambda._5, next_lambda._6, scope)

    val num_copies = 2
    val numberOfSteps = bound
    val simRecord = new simulator.SimulationTable
    val taintFrameTable = new TaintFrameTable
    var prevVarTable = new ArrayBuffer[List[List[smt.Expr]]]()
    var havocTable = new ArrayBuffer[List[(smt.Symbol, smt.Symbol)]]()
    var prevTaintVarTable = new ArrayBuffer[List[smt.Expr]]()
    var taintAssumes = new ArrayBuffer[smt.Expr]()

    var stepOffset = 0
    //FIXME: Remove newInputSymbols
    val taintSymTab = newTaintInputSymbols(getTaintSymbolTable(scope), stepOffset, scope)
    stepOffset += 1
    taintFrameTable += taintSymTab
    val initTaintVars = getTaintVarsInOrder(taintSymTab.map(_.swap), scope)
    prevTaintVarTable += initTaintVars.flatten
    val initTaintConjunct = simulator.betaSubstitution(taintInitLambda, initTaintVars.flatten)
    taintAssumes += initTaintConjunct

    for (i <- 1 to num_copies) {

        var frames = new simulator.FrameTable
        val initSymTab = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), stepOffset, scope)
        stepOffset += 1
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
                  log.debug("%% Taint Assumes %% " + taintAssumes.toList.toString)
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
      val taintSymTab = newTaintInputSymbols(getTaintSymbolTable(scope), stepOffset, scope)
      stepOffset += 1
      taintFrameTable += taintSymTab
      val nextTaintVars = getTaintVarsInOrder(taintSymTab.map(_.swap), scope)
      prevTaintVarTable += nextTaintVars.flatten
      val nextTaintConjunct = simulator.betaSubstitution(taintNextLambda, prevTaintVarTable(i - 1) ++ nextTaintVars.flatten)
      taintAssumes += nextTaintConjunct

      for (j <- 1 to num_copies) {
        symTabStep = simulator.newInputSymbols(simulator.getInitSymbolTable(scope), stepOffset, scope)
        stepOffset += 1
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
          val taintMatches = secondNextVars.zip(firstNextVars zip prevTaintVarTable(i - 1))
          log.debug(" ----- Next Partition Map ----- " + partition._1)
          log.debug(" ----- Next taint Matches ---- " + taintMatches.toString)
          taintMatches.foreach {
            v =>
              checkExpr(solver, smt.OperatorApplication(smt.NegationOp, List(v._2._2)), taintAssumes.toList).result.result match {
                case Some(true) =>  //Unsat and tainted, hence equal
                  val equality = smt.OperatorApplication(smt.EqualityOp, List(v._1, v._2._1))
                  //log.debug("%% Taint Assumes %% " + taintAssumes.toList.toString)
                  //log.debug("@@ Query Expr @@ " + smt.OperatorApplication(smt.NegationOp, List(v._2._2)).toString)
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