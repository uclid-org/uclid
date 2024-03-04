package uclid.smt

import org.scalatest.flatspec.AnyFlatSpec

/**
 * The Btor2 format only features BitVector and Array types.
 * In general it appears that treating BV<1> as Bool when loading
 * a btor2 file makes for faster responses from a SMT solver.
 * This spec verifies our hand coded conversion from functions
 * working on BV<1> to boolean expressions.
 */
class BitVectorToBoolSpec extends AnyFlatSpec {
  def startSolver() = new SMTLIB2Interface(List("z3", "-in"))

  def check_eq(solver: Context, a: Expr, b: Expr): Boolean = {
    val av = if(a.typ.isBool) to_bv(a) else a
    val bv = if(b.typ.isBool) to_bv(b) else b
    solver.push()
    solver.assert(OperatorApplication(InequalityOp, List(av, bv)))
    val res = solver.check()
    solver.pop()
    if(!res.isFalse) { println(s"${res.model}") }
    res.isFalse // unsat -> there does not exist an input for which these expressions are different
  }
  def to_bool(a: Expr): Expr = OperatorApplication(EqualityOp, List(a, BitVectorLit(1,1)))
  def to_bv(a: Expr): Expr = OperatorApplication(ITEOp, List(a, BitVectorLit(1,1), BitVectorLit(0,1)))

  "unary operations" should "be converted to bool correctly" in {
    val s = startSolver()
    val a = Symbol("a", BitVectorType(1))
    val not_a  = OperatorApplication(NegationOp, List(to_bool(a)))

    assert(check_eq(s, OperatorApplication(BVNotOp(1), List(a)), not_a)) // not
    assert(check_eq(s, OperatorApplication(BVAddOp(1), List(a, BitVectorLit(1,1))), not_a)) // inc
    assert(check_eq(s, OperatorApplication(BVSubOp(1), List(a, BitVectorLit(1,1))), not_a)) // dec
    assert(check_eq(s, OperatorApplication(BVSubOp(1), List(BitVectorLit(0,1), a)), a)) // neg

    s.finish()
  }

  "binary operations" should "be converted to bool correctly" in {
    val s = startSolver()
    val a = Symbol("a", BitVectorType(1)) ; val ab = to_bool(a)
    val b = Symbol("b", BitVectorType(1)) ; val bb = to_bool(b)
    val a_iff_b  = OperatorApplication(IffOp, List(ab, bb))
    val not_b = OperatorApplication(NegationOp, List(bb))
    val not_a = OperatorApplication(NegationOp, List(ab))
    val a_and_not_b = OperatorApplication(ConjunctionOp, List(ab, not_b))
    val a_or_not_b = OperatorApplication(DisjunctionOp, List(ab, not_b))
    val not_a_and_b = OperatorApplication(ConjunctionOp, List(not_a, bb))
    val not_a_or_b = OperatorApplication(DisjunctionOp, List(not_a, bb))
    val a_xor_b = OperatorApplication(DisjunctionOp, List(a_and_not_b, not_a_and_b))
    val a_or_b = OperatorApplication(DisjunctionOp, List(ab, bb))
    val a_and_b = OperatorApplication(ConjunctionOp, List(ab, bb))

    assert(check_eq(s, OperatorApplication(EqualityOp, List(a, b)), a_iff_b)) // eq

    def cmp(op: Int => BoolResultOp) = OperatorApplication(op(1), List(a, b))
    // unsigned
    assert(check_eq(s, cmp(BVGTUOp), a_and_not_b)) // ugt
    assert(check_eq(s, cmp(BVGEUOp), a_or_not_b) ) // uge
    assert(check_eq(s, cmp(BVLTUOp), not_a_and_b)) // ult (= not(uge))
    assert(check_eq(s, cmp(BVLEUOp), not_a_or_b) ) // ule (= not(ugt))
    // signed
    assert(check_eq(s, cmp(BVGTOp), not_a_and_b)) // sgt
    assert(check_eq(s, cmp(BVGEOp), not_a_or_b) ) // sge
    assert(check_eq(s, cmp(BVLTOp), a_and_not_b)) // slt (= not(sge))
    assert(check_eq(s, cmp(BVLEOp), a_or_not_b) ) // sle (= not(sgt))

    def ar(op: Int => BVResultOp) = OperatorApplication(op(1), List(a,b))
    assert(check_eq(s, ar(BVAddOp), a_xor_b)) // add
    assert(check_eq(s, ar(BVSubOp), a_xor_b)) // sub
    assert(check_eq(s, ar(BVMulOp), a_and_b)) // mul

    s.finish()
  }
}
