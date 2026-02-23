/*
 * UCLID5 Verification and Synthesis Engine
 *
 * IC3/PDR (Property Directed Reachability) engine for safety property verification.
 *
 */

package uclid

import lang._
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.collection.mutable.{Map => MutableMap}
import com.typesafe.scalalogging.Logger

class IC3Engine(module: Module, solver: smt.Z3Interface) {

  val log = Logger(classOf[IC3Engine])

  // Create a fresh SymbolicSimulator to extract formulas.
  val symSim = new SymbolicSimulator(module)
  val scope = Scope.empty + module

  val passAllFilter: (Identifier, List[ExprDecorator]) => Boolean = (_, _) => true

  // Extract init formula and current-state symbol table.
  val (initLambda, _, initSymbolTable, _, _) =
    symSim.getInitLambda(false, false, false, scope, "ic3", passAllFilter, passAllFilter)
  val initFormula: smt.Expr = initLambda.e

  // Extract transition formula and next-state symbol table.
  val (transLambda, _, nextSymTab, _, _, _) =
    symSim.getNextLambda(initSymbolTable, false, false, scope, "ic3", passAllFilter, passAllFilter)
  val transFormula: smt.Expr = transLambda.e

  // Build mapping from current-state symbols to next-state symbols.
  val curToNextMap: Map[smt.Symbol, smt.Symbol] = initSymbolTable.flatMap { case (id, curExpr) =>
    scope.get(id) match {
      case Some(Scope.StateVar(_, _)) | Some(Scope.OutputVar(_, _)) |
           Some(Scope.SharedVar(_, _)) | Some(Scope.InputVar(_, _)) =>
        nextSymTab.get(id).map { nextExpr =>
          (curExpr.asInstanceOf[smt.Symbol], nextExpr.asInstanceOf[smt.Symbol])
        }
      case _ => None
    }
  }.toMap

  val nextToCurMap: Map[smt.Symbol, smt.Symbol] = curToNextMap.map(_.swap)

  // State variable symbols for cube extraction (excludes inputs and constants).
  val stateSymbols: List[smt.Symbol] = initSymbolTable.flatMap { case (id, expr) =>
    scope.get(id) match {
      case Some(Scope.StateVar(_, _)) | Some(Scope.OutputVar(_, _)) | Some(Scope.SharedVar(_, _)) =>
        Some(expr.asInstanceOf[smt.Symbol])
      case _ => None
    }
  }.toList

  type Clause = smt.Expr
  val frames: ArrayBuffer[ArrayBuffer[Clause]] = ArrayBuffer()

  case class ProofObligation(frame: Int, cube: smt.Expr)

  def prime(expr: smt.Expr): smt.Expr = {
    smt.Context.rewriteExpr(expr, (e: smt.Expr) => e match {
      case s: smt.Symbol => curToNextMap.getOrElse(s, s)
      case other => other
    }, MutableMap.empty)
  }

  def unprime(expr: smt.Expr): smt.Expr = {
    smt.Context.rewriteExpr(expr, (e: smt.Expr) => e match {
      case s: smt.Symbol => nextToCurMap.getOrElse(s, s)
      case other => other
    }, MutableMap.empty)
  }

  def negate(expr: smt.Expr): smt.Expr = {
    smt.OperatorApplication(smt.NegationOp, List(expr))
  }

  /** Extract a concrete cube (conjunction of equalities) from a model over state variables.
   *  Skips symbols whose types can't be evaluated (e.g., arrays, uninterpreted sorts). */
  def extractConcreteCube(model: smt.Model): smt.Expr = {
    val lits = stateSymbols.flatMap { sym =>
      try {
        val value = model.evaluate(sym)
        Some(smt.OperatorApplication(smt.EqualityOp, List(sym, value)))
      } catch {
        case _: Utils.RuntimeError => None
      }
    }
    if (lits.isEmpty) smt.BooleanLit(true)
    else if (lits.size == 1) lits.head
    else smt.OperatorApplication(smt.ConjunctionOp, lits)
  }

  /** Assert all clauses in a frame. Frame 0 is the init formula. */
  def assertFrame(frameIdx: Int): Unit = {
    if (frameIdx == 0) {
      solver.assert(initFormula)
    } else {
      frames(frameIdx).foreach(clause => solver.assert(clause))
    }
  }

  /**
   * Try to generalize a primed integer equality (v' == c) to a sign-based inequality.
   * E.g., if c < 0, try v' < 0 instead of v' == c.
   * Returns the generalized literal if successful, otherwise the original.
   */
  def tryGeneralizeLiteral(
    primedLit: smt.Expr,
    otherAssumptions: List[smt.Expr],
    frame: Int,
    cube: smt.Expr
  ): smt.Expr = {
    primedLit match {
      case smt.OperatorApplication(smt.EqualityOp, List(sym: smt.Symbol, smt.IntLit(value))) =>
        val zero = smt.IntLit(BigInt(0))
        val candidate = if (value < 0) {
          smt.OperatorApplication(smt.IntLTOp, List(sym, zero))
        } else if (value > 0) {
          smt.OperatorApplication(smt.IntGTOp, List(sym, zero))
        } else {
          return primedLit // value == 0, keep as is
        }
        // Check if replacing this literal still gives UNSAT
        val newAssumptions = candidate :: otherAssumptions
        solver.push()
        if (frame == 0) {
          solver.assert(initFormula)
        } else {
          assertFrame(frame)
        }
        solver.assert(negate(unprime(candidate)))
        solver.assert(transFormula)
        val result = solver.checkAssumptions(newAssumptions)
        solver.pop()
        if (result.isFalse) candidate else primedLit
      case _ => primedLit
    }
  }

  /** Generalize a cube using unsat cores and integer inequality generalization. */
  def generalize(frame: Int, cube: smt.Expr): smt.Expr = {
    val literals = cube match {
      case smt.OperatorApplication(smt.ConjunctionOp, args) => args
      case other => List(other)
    }

    val primedLiterals = literals.map(prime)

    // Get unsat core to find minimal set of needed literals.
    solver.push()
    if (frame == 0) {
      solver.assert(initFormula)
    } else {
      assertFrame(frame)
    }
    solver.assert(negate(cube))
    solver.assert(transFormula)
    val result = solver.checkAssumptions(primedLiterals)
    solver.pop()

    if (result.isFalse) {
      var coreLiterals = solver.getUnsatCore()
      if (coreLiterals.isEmpty) coreLiterals = primedLiterals

      // Try to generalize each core literal (integer equalities to inequalities).
      val generalizedLiterals = coreLiterals.map { lit =>
        val others = coreLiterals.filter(_ != lit)
        tryGeneralizeLiteral(lit, others, frame, cube)
      }

      val unprimedLiterals = generalizedLiterals.map(unprime)
      val coreConj = if (unprimedLiterals.size == 1) unprimedLiterals.head
                     else smt.OperatorApplication(smt.ConjunctionOp, unprimedLiterals)
      negate(coreConj)
    } else {
      negate(cube)
    }
  }

  /** Substitute symbols in an expression using the given map. */
  def substitute(expr: smt.Expr, substMap: Map[smt.Symbol, smt.Symbol]): smt.Expr = {
    smt.Context.rewriteExpr(expr, (e: smt.Expr) => e match {
      case s: smt.Symbol => substMap.getOrElse(s, s)
      case other => other
    }, MutableMap.empty)
  }

  /**
   * Build a concrete counterexample trace by doing a BMC-style unrolling.
   * Returns (stepSymbolTables, model) where stepSymbolTables(i) is the
   * symbol table at step i, and model provides concrete values.
   */
  def buildCexTrace(depth: Int, propExpr: smt.Expr): (ArrayBuffer[SymbolicSimulator.SymbolTable], smt.Model) = {
    val stepSymTables = ArrayBuffer[SymbolicSimulator.SymbolTable]()

    // Step 0: reuse initSymbolTable symbols (init formula is expressed in these).
    stepSymTables += initSymbolTable

    // Steps 1..depth: create fresh symbols for state/input/output/shared vars.
    for (step <- 1 to depth) {
      val newSymTab = initSymbolTable.map { case (id, expr) =>
        scope.get(id) match {
          case Some(Scope.StateVar(_, _)) | Some(Scope.OutputVar(_, _)) |
               Some(Scope.SharedVar(_, _)) | Some(Scope.InputVar(_, _)) =>
            val sym = expr.asInstanceOf[smt.Symbol]
            (id, smt.Symbol(s"ic3_cex_${step}_${sym.id}", sym.symbolTyp).asInstanceOf[smt.Expr])
          case _ =>
            (id, expr) // Constants, enums, functions stay the same.
        }
      }
      stepSymTables += newSymTab
    }

    solver.push()

    // Assert init at step 0.
    solver.assert(initFormula)

    // Assert transition for each step i -> i+1.
    for (step <- 0 until depth) {
      val substMap = scala.collection.mutable.Map[smt.Symbol, smt.Symbol]()

      // Map original current-state symbols to step i symbols.
      initSymbolTable.foreach { case (id, expr) =>
        scope.get(id) match {
          case Some(Scope.StateVar(_, _)) | Some(Scope.OutputVar(_, _)) |
               Some(Scope.SharedVar(_, _)) | Some(Scope.InputVar(_, _)) =>
            substMap(expr.asInstanceOf[smt.Symbol]) = stepSymTables(step)(id).asInstanceOf[smt.Symbol]
          case _ => // skip
        }
      }

      // Map original next-state symbols to step i+1 symbols.
      nextSymTab.foreach { case (id, expr) =>
        scope.get(id) match {
          case Some(Scope.StateVar(_, _)) | Some(Scope.OutputVar(_, _)) |
               Some(Scope.SharedVar(_, _)) | Some(Scope.InputVar(_, _)) =>
            substMap(expr.asInstanceOf[smt.Symbol]) = stepSymTables(step + 1)(id).asInstanceOf[smt.Symbol]
          case _ => // skip
        }
      }

      solver.assert(substitute(transFormula, substMap.toMap))
    }

    // Assert ¬P at the last step.
    val propSubst: Map[smt.Symbol, smt.Symbol] = initSymbolTable.flatMap { case (id, expr) =>
      scope.get(id) match {
        case Some(Scope.StateVar(_, _)) | Some(Scope.OutputVar(_, _)) |
             Some(Scope.SharedVar(_, _)) | Some(Scope.InputVar(_, _)) =>
          Some(expr.asInstanceOf[smt.Symbol] -> stepSymTables(depth)(id).asInstanceOf[smt.Symbol])
        case _ => None
      }
    }.toMap

    solver.assert(negate(substitute(propExpr, propSubst)))

    val result = solver.check()
    solver.pop()

    Utils.assert(result.isTrue, "IC3: BMC unrolling for CEX must be SAT")
    (stepSymTables, result.model.get)
  }

  /** Main IC3 algorithm. Returns None if proved, Some(depth) if CEX found at given depth. */
  def checkProperty(propExpr: smt.Expr): Option[Int] = {
    log.debug("IC3: checking property")

    // Step 1: Check init ∧ ¬P
    solver.push()
    solver.assert(initFormula)
    solver.assert(negate(propExpr))
    val initCheck = solver.check()
    solver.pop()
    if (initCheck.isTrue) {
      log.debug("IC3: property violated in initial state")
      return Some(0)
    }

    frames.clear()
    frames += ArrayBuffer() // F[0]
    frames += ArrayBuffer() // F[1]

    var k = 1
    val MAX_FRAMES = 500

    while (k < MAX_FRAMES) {
      log.debug(s"IC3: working on frame $k")

      if (!strengthen(k, propExpr)) {
        log.debug("IC3: counterexample found")
        return Some(k)
      }

      propagate(k) match {
        case Some(fixpointFrame) =>
          log.debug("IC3: fixpoint reached, property proved")
          printInductiveInvariant(fixpointFrame)
          return None
        case None => // continue
      }

      k += 1
      frames += ArrayBuffer()
    }

    throw new Utils.RuntimeError("IC3: exceeded maximum number of frames")
  }

  /** Strengthen frame k by blocking all bad cubes. Returns false if CEX found. */
  def strengthen(k: Int, propExpr: smt.Expr): Boolean = {
    val obligations = ListBuffer[ProofObligation]()

    while (true) {
      if (obligations.isEmpty) {
        // Check for bad cubes: F[k] ∧ ¬P SAT?
        solver.push()
        assertFrame(k)
        solver.assert(negate(propExpr))
        val badCheck = solver.check()
        solver.pop()

        if (badCheck.isTrue) {
          // Use ¬P as the cube (not concrete model values).
          // This is critical for infinite-state (integer) systems.
          obligations += ProofObligation(k, negate(propExpr))
        } else {
          return true
        }
      }

      // Process the lowest-frame obligation first.
      val sortedIdx = obligations.zipWithIndex.minBy(_._1.frame)._2
      val obligation = obligations.remove(sortedIdx)

      if (obligation.frame == 0) {
        // Check if cube is reachable from init.
        solver.push()
        solver.assert(initFormula)
        solver.assert(obligation.cube)
        val initCheck = solver.check()
        solver.pop()

        if (initCheck.isTrue) {
          return false // Real counterexample
        }
        // Block at frame 1.
        val blockingClause = generalize(0, obligation.cube)
        if (frames.size > 1) {
          frames(1) += blockingClause
        }
      } else {
        // Consecution check: F[i-1] ∧ ¬cube ∧ T ∧ cube' SAT?
        solver.push()
        assertFrame(obligation.frame - 1)
        solver.assert(negate(obligation.cube))
        solver.assert(transFormula)
        solver.assert(prime(obligation.cube))
        val consecCheck = solver.check()
        solver.pop()

        if (consecCheck.isTrue) {
          // Found predecessor — use concrete cube from model.
          val predCube = extractConcreteCube(consecCheck.model.get)
          obligations += ProofObligation(obligation.frame - 1, predCube)
          obligations += obligation
        } else {
          // Cube blocked — generalize and add blocking clause.
          val blockingClause = generalize(obligation.frame - 1, obligation.cube)
          for (i <- 1 to obligation.frame) {
            if (i < frames.size) {
              frames(i) += blockingClause
            }
          }
        }
      }
    }
    true // unreachable
  }

  /** Propagate clauses forward and check for fixpoint.
   *  Returns Some(i) if fixpoint found (frames(i) ⊆ frames(i+1)), None otherwise. */
  def propagate(k: Int): Option[Int] = {
    for (i <- 1 until k) {
      val clausesToPush = ArrayBuffer[Clause]()
      frames(i).foreach { clause =>
        solver.push()
        assertFrame(i)
        solver.assert(clause)
        solver.assert(transFormula)
        solver.assert(prime(negate(clause)))
        val pushCheck = solver.check(false)
        solver.pop()

        if (pushCheck.isFalse) {
          clausesToPush += clause
        }
      }
      clausesToPush.foreach { clause =>
        if (!frames(i + 1).contains(clause)) {
          frames(i + 1) += clause
        }
      }
      if (frames(i).forall(c => frames(i + 1).contains(c))) {
        return Some(i)
      }
    }
    None
  }

  /** Pretty-print the inductive invariant from the fixpoint frame. */
  def printInductiveInvariant(fixpointFrame: Int): Unit = {
    val clauses = frames(fixpointFrame).distinct
    UclidMain.printResult("IC3: Inductive invariant (frame %d):".format(fixpointFrame))
    if (clauses.isEmpty) {
      UclidMain.printResult("  true")
    } else {
      clauses.foreach { clause =>
        UclidMain.printResult("  " + clause.toString)
      }
    }
  }

  /** Run IC3 on all properties matching the filter. */
  def run(propertyFilter: (Identifier, List[ExprDecorator]) => Boolean, label: String = "ic3"): List[CheckResult] = {
    // IC3 requires real solver responses (not SMT file dumps). Disable SMT file
    // generation on the shared solver during IC3 execution.
    val savedFilePrefix = solver.filePrefix
    solver.filePrefix = ""

    try {
      val frameTbl = ArrayBuffer(initSymbolTable)

      module.properties.flatMap { prop =>
        if (propertyFilter(prop.id, prop.params) && !ExprDecorator.isLTLProperty(prop.params)) {
          val propExpr = symSim.evaluate(prop.expr, initSymbolTable, frameTbl, 0, scope)
          val cexDepth = checkProperty(propExpr)

          val (solverResult, assertFrameTable, assertIter) = cexDepth match {
            case None =>
              // Property proved.
              (smt.SolverResult(Some(true), None), ArrayBuffer(frameTbl), 0)
            case Some(depth) =>
              // CEX found — build concrete trace via BMC unrolling.
              val (stepSymTables, model) = buildCexTrace(depth, propExpr)
              val cexFrameTbl: ArrayBuffer[SymbolicSimulator.SymbolTable] = stepSymTables
              (smt.SolverResult(Some(false), Some(model)), ArrayBuffer(cexFrameTbl), depth)
          }

          val assertInfo = AssertInfo(
            prop.name, label,
            assertFrameTable, scope, assertIter,
            smt.BooleanLit(true), propExpr,
            prop.params, prop.expr.position
          )

          Some(CheckResult(assertInfo, solverResult))
        } else {
          None
        }
      }
    } finally {
      solver.filePrefix = savedFilePrefix
    }
  }
}
