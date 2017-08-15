
/**
 * @author pramod
 */
package uclid {
  import com.microsoft.{z3 => z3}
  import java.util.HashMap;
  
  /**
   * Decide validity of SMTExpr's using Z3.
   */
  class Z3Interface(ctx : z3.Context, solver : z3.Solver) {
    
  }
  
  object SMTTester
  {
    def test() : Unit = {
      var cfg = new HashMap[String, String]()
      cfg.put("model", "true")
      var ctx = new z3.Context(cfg)
      val bv4Type = ctx.mkBitVecSort(4);
      val a = ctx.mkFreshConst("a", bv4Type).asInstanceOf[z3.BitVecExpr]
      val b = ctx.mkFreshConst("b", bv4Type).asInstanceOf[z3.BitVecExpr]
      val zero = ctx.mkNumeral(0, bv4Type).asInstanceOf[z3.BitVecExpr]
      val ones = ctx.mkBVNot(zero)
  
      val s = ctx.mkSolver()
      s.add(ctx.mkDistinct(a, zero))
      s.add(ctx.mkDistinct(b, zero))
      s.add(ctx.mkDistinct(a, ones))
      s.add(ctx.mkDistinct(b, ones))
      s.add(ctx.mkDistinct(a, b))
      s.add(ctx.mkEq(ctx.mkBVOR(a, b), ones))
      val result = s.check()
      println ("result = " + result)
      if (result == z3.Status.SATISFIABLE) {
          println("model = " + s.getModel.toString)
      }
    }
  }
}