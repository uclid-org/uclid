
/**
 * @author pramod
 */
package uclid {
  package smt {
    import com.microsoft.{z3 => z3}
    import java.util.HashMap;
    import scala.collection.mutable.Map
    import scala.collection.JavaConversions._
    
    /**
     * Decide validity of SMTExpr's using a Z3 sovler.
     */
    class Z3Interface(z3Ctx : z3.Context, z3Solver : z3.Solver) extends SolverInterface {
      // Member variables.
      /** The Z3 context. */
      val ctx = z3Ctx
      /** The Z3 solver. */
      val solver = z3Solver
      /** The symbol map. */
      var symbolMap : Map[Symbol, z3.Expr] = Map()
      /* Prefix for all  tuple names. */
      val tupleNamePrefix = "__ucl_tuple_"
      /* Counter for unique tuple names. */
      var tupleNameSuffix = 0
      // Get a unique tuple name. 
      def getTupleName() : z3.Symbol = { 
        tupleNameSuffix = tupleNameSuffix + 1
        return ctx.mkSymbol(tupleNamePrefix + tupleNameSuffix)
      }
      // Get tuple field names.
      val getTupleFieldNames = new Memo[Int, Array[z3.Symbol]]((n : Int) => {
        (1 to n).map((i => ctx.mkSymbol("__ucl_field" + i.toString))).toArray
      })
      // Methods to convert uclid.smt.Type values into Z3 sorts.
      // Begin memoization functions for Z3 sorts.  //
      val getBoolSort = new Memo[Unit, z3.BoolSort](Unit => ctx.mkBoolSort())
      val getIntSort = new Memo[Unit, z3.IntSort](Unit => ctx.mkIntSort())
      val getBitVectorSort = new Memo[Int, z3.BitVecSort]((w : Int) => ctx.mkBitVecSort(w))
      val getTupleSort = new Memo[List[Type], z3.TupleSort]((types : List[Type]) => {
        ctx.mkTupleSort(
            getTupleName(), getTupleFieldNames(types.size),
            types.map((t) => getZ3Sort(t)).toArray
        )
      })
      val getArraySort = new Memo[(List[Type], Type), z3.ArraySort]((arrayType : (List[Type], Type)) => {
        ctx.mkArraySort(getTupleSort(arrayType._1), getZ3Sort(arrayType._2))
      })
      // End of memoization functions. //
      // function to convert uclid.smt types to Z3 sorts.
      def getZ3Sort (typ : smt.Type) : z3.Sort = {
        typ  match {
          case BoolType()       => getBoolSort()
          case IntType()        => getIntSort()
          case BitVectorType(w) => getBitVectorSort(w)
          case TupleType(ts)    => getTupleSort(ts)
          case ArrayType(rs, d) => getArraySort(rs, d)
        }
      }
      
      val getBoolLit = new Memo[Boolean, z3.BoolExpr](b => ctx.mkBool(b))
      val getIntLit = new Memo[BigInt, z3.IntExpr](i => ctx.mkInt(i.toString))
      val getBitVectorLit = new Memo[(BigInt, Int), z3.BitVecExpr]((arg) => ctx.mkBV(arg._1.toString, arg._2))
      
      def createZ3Symbol (sym : Symbol) : z3.Expr = {
        val sort : z3.Sort = (sym.typ) match {
          case BoolType() => getBoolSort()
          case IntType() => getIntSort()
          case BitVectorType(w) => getBitVectorSort(w)
          // FIXME: other sorts=
        }
        return ctx.mkFreshConst(sym.id, sort)
      }
      
      def castArgs[T <: z3.AST](args : List[z3.AST]) = { args.map((arg => arg.asInstanceOf[T])) }
      def z3BinaryArithOpFunction(op : Operator, args : List[z3.AST]) : Option[z3.Expr] = {
        val func = op match {
          case IntLTOp  => Some(ctx.mkLt _)
          case IntLEOp  => Some(ctx.mkLe _)
          case IntGTOp  => Some(ctx.mkGt _)
          case IntGEOp  => Some(ctx.mkGe _)
          case _        => None
        }
        func match {
          case Some(func) => {
            val arithArgs = castArgs[z3.ArithExpr](args)
            Some(func(arithArgs(0), arithArgs(1)))
          }
          case None => None
        }
      }
      def z3NaryArithOpFunction(op : Operator, args : List[z3.AST]) : Option[z3.Expr] = {
        val func = op match {
          case IntAddOp  => Some(ctx.mkAdd _)
          case IntSubOp  => Some(ctx.mkSub _)
          case IntMulOp  => Some(ctx.mkMul _)
          case _         => None
        }
        func match {
          case Some(func) => Some(func(castArgs[z3.ArithExpr](args).toSeq : _*))
          case None       => None
        }
      }
      def z3BinaryBoolOpFunction(op : Operator, args : List[z3.AST]) : Option[z3.Expr]  = {
        val func = op match {
          case IffOp         => Some(ctx.mkIff _)
          case ImplicationOp => Some(ctx.mkImplies _)
          case EqualityOp    => Some(ctx.mkEq _)
          case _             => None
        }
        func match {
          case Some(func)  => {
            val boolArgs = castArgs[z3.BoolExpr](args)
            Some(func(boolArgs(0), boolArgs(1)))
          }
          case None        => None
        }
      }
      
      def z3NaryBoolOpFunction(op : Operator, args : List[z3.AST]) : Option[z3.Expr]  = {
        val func = op match {
          case ConjunctionOp => Some(ctx.mkAnd _)
          case DisjunctionOp => Some(ctx.mkOr _)
          case _             => None
        }
        func match {
          case Some(func) => Some(func(castArgs[z3.BoolExpr](args).toSeq : _*))
          case None       => None
        }
      }

      def z3UnaryBoolOpFunction(op : Operator, args : List[z3.AST]) : Option[z3.Expr]  = {
        val func = op match {
          case NegationOp => Some(ctx.mkNot _)
          case _          => None
        }
        func match {
          case Some(func) => Some(func(castArgs[z3.BoolExpr](args)(0)))
          case None       => None
        }
      }
      
      def opToZ3(op : Operator, args : List[z3.AST]) : Option[z3.Expr]  = {
       lazy val binaryArith = z3BinaryArithOpFunction (op, args)
       lazy val naryArith = z3NaryArithOpFunction (op, args)
       lazy val unaryBool = z3UnaryBoolOpFunction (op, args)
       lazy val binaryBool = z3BinaryBoolOpFunction (op, args)
       lazy val naryBool = z3NaryBoolOpFunction (op, args)
       
       val expressions : Stream[Option[z3.Expr]] = binaryArith #:: naryArith #:: unaryBool #:: binaryBool #:: naryBool #:: Stream.empty
       val someExpressions = expressions.filter((expr) => expr.isEmpty)
       someExpressions.take(1) match {
         case head #:: tail => head
         case Stream.Empty => None
       }
      }
      
      
      def toZ3(e : Expr) : z3.AST = {
        e match {
          case Symbol(_,_) => 
            symbolMap.get(e.asInstanceOf[Symbol]).get
          case OperatorApplication(op,operands) =>
            opToZ3(op, operands.map((arg) => toZ3(arg))).get
          case ArraySelectOperation(e, index) =>
            throw new UnsupportedOperationException("not implemented.")
          case ArrayStoreOperation(e, index, value) =>
            throw new UnsupportedOperationException("not implemented.")
          case FunctionApplication(e, args) =>
            throw new UnsupportedOperationException("not implemented.")
          case ITE(e,t,f) =>
            throw new UnsupportedOperationException("not implemented.")
          case Lambda(_,_) =>
            throw new RuntimeException("lambdas in assertions should have been beta-reduced")
          case IntLit(i) => getIntLit(i)
          case BitVectorLit(bv,w) => getBitVectorLit(bv, w)
          case BooleanLit(b) => getBoolLit(b)
        }
      }
      
      def check (e : Expr) : Option[Boolean] = {
        val smtSymbols = findSymbols(e)
        val z3Symbols = smtSymbols.map((sym => (sym, createZ3Symbol(sym)))).toMap
        
        return None
      }
      
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
}