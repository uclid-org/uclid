
/**
 * @author pramod
 */
package uclid
package smt

import com.microsoft.{z3 => z3}
import java.util.HashMap;
import scala.collection.mutable.Map
import scala.collection.JavaConverters._

/**
 * Decide validity of SMTExpr's using a Z3 sovler.
 */
class Z3Interface(z3Ctx : z3.Context, z3Solver : z3.Solver) extends SolverInterface {
  // Member variables.
  /** The Z3 context. */
  val ctx = z3Ctx
  /** The Z3 solver. */
  val solver = z3Solver
  /* Prefix for all  tuple names. */
  val tupleNamePrefix = "__ucl_tuple_"
  /* Counter for unique tuple names. */
  var tupleNameSuffix = 0
  /** Returns a unique tuple name. */ 
  def getTupleName() : z3.Symbol = { 
    tupleNameSuffix = tupleNameSuffix + 1
    return ctx.mkSymbol(tupleNamePrefix + tupleNameSuffix)
  }
  /** Returns tuple field names. */
  val getTupleFieldNames = new Memo[Int, Array[z3.Symbol]]((n : Int) => {
    (1 to n).map((i => ctx.mkSymbol(i.toString + "__ucl_tuple_field" ))).toArray
  })
  
  /** Utility function to cast to subtypes of z3.AST */
  def typecastAST[T <: z3.AST](args : List[z3.AST]) : List[T] = { 
    args.map((arg => arg.asInstanceOf[T]))
  }

  // Methods to convert uclid.smt.Type values into Z3 sorts.
  val getBoolSort = new Memo[Unit, z3.BoolSort](Unit => ctx.mkBoolSort())
  val getIntSort = new Memo[Unit, z3.IntSort](Unit => ctx.mkIntSort())
  val getBitVectorSort = new Memo[Int, z3.BitVecSort]((w : Int) => ctx.mkBitVecSort(w))
  val getTupleSort = new Memo[List[Type], z3.TupleSort]((types : List[Type]) => {
    ctx.mkTupleSort(
        getTupleName(), getTupleFieldNames(types.size),
        types.map((t) => getZ3Sort(t)).toArray
    )
  })
  val getRecordSort = new Memo[List[(String, Type)], z3.TupleSort]((fields : List[(String, Type)]) => {
    ctx.mkTupleSort(
      getTupleName(), 
      fields.map((f) => ctx.mkSymbol(f._1)).toArray,
      fields.map((f) => getZ3Sort(f._2)).toArray
    )
  })
  def getProductSort(typ : ProductType) : z3.TupleSort = {
    typ match {
      case tupType : TupleType => getTupleSort(tupType.types)
      case recType : RecordType => getRecordSort(recType.fields_)
    }
  }
  val getArraySort = new Memo[(List[Type], Type), z3.ArraySort]((arrayType : (List[Type], Type)) => {
    ctx.mkArraySort(getTupleSort(arrayType._1), getZ3Sort(arrayType._2))
  })
  /** Convert uclid.smt types to Z3 sorts. */
  def getZ3Sort (typ : smt.Type) : z3.Sort = {
    typ  match {
      case BoolType()       => getBoolSort()
      case IntType()        => getIntSort()
      case BitVectorType(w) => getBitVectorSort(w)
      case TupleType(ts)    => getTupleSort(ts)
      case RecordType(rs)   => getRecordSort(rs)
      case ArrayType(rs, d) => getArraySort(rs, d)
    }
  }

  /** Create a Z3 tuple AST. */
  def getTuple(values : List[z3.AST], tupleMemberTypes : List[Type]) : z3.Expr = {
    val tupleType = TupleType(tupleMemberTypes)
    val tupleSort = getZ3Sort(tupleType).asInstanceOf[z3.TupleSort]
    val tupleCons = tupleSort.mkDecl()
    tupleCons.apply(typecastAST[z3.Expr](values).toSeq : _*) 
  }
  
  /** Create a boolean literal. */
  val getBoolLit = new Memo[Boolean, z3.BoolExpr](b => ctx.mkBool(b))
  
  /** Create an integer literal. */
  val getIntLit = new Memo[BigInt, z3.IntExpr](i => ctx.mkInt(i.toString))
  
  /** Create a bitvector literal. */
  val getBitVectorLit = new Memo[(BigInt, Int), z3.BitVecExpr]((arg) => ctx.mkBV(arg._1.toString, arg._2))
  
  /** Convert a smt.Symbol object into a Z3 AST. */
  def symbolToZ3 (sym : Symbol) : z3.AST = {
    abstract class ExprSort
    case class VarSort(sort : z3.Sort) extends ExprSort
    case class MapSort(ins : List[Type], out : Type) extends ExprSort
    
    val exprSort = (sym.typ) match {
      case BoolType() => VarSort(getBoolSort())
      case IntType() => VarSort(getIntSort())
      case BitVectorType(w) => VarSort(getBitVectorSort(w))
      case TupleType(ts) => VarSort(getTupleSort(ts))
      case RecordType(rs) => VarSort(getRecordSort(rs))
      case MapType(ins, out) => MapSort(ins, out)
      case ArrayType(ins, out) => VarSort(getArraySort(ins, out))
    } 
    
    exprSort match {
      case VarSort(s) => 
        ctx.mkFreshConst(sym.id, s)
      case MapSort(ins, out) => 
        ctx.mkFuncDecl(sym.id, ins.map(getZ3Sort _).toArray, getZ3Sort(out))
    }
  }
  
  /** Convert an OperatorApplication into a Z3 AST.  */
  def opToZ3(op : Operator, operands : List[Expr]) : z3.Expr  = {
    lazy val args = operands.map((arg) => exprToZ3(arg))
    // These values need to be lazy so that they are only evaluated when the appropriate ctx.mk* functions
    // are called. If they were eager, the casts would fail at runtime.
    lazy val exprArgs = typecastAST[z3.Expr](args)
    lazy val arithArgs = typecastAST[z3.ArithExpr](args)
    lazy val boolArgs = typecastAST[z3.BoolExpr](args)
    lazy val bvArgs = typecastAST[z3.BitVecExpr](args)
    
    def mkReplace(w : Int, hi : Int, lo : Int, arg0 : z3.BitVecExpr, arg1 : z3.BitVecExpr) : z3.BitVecExpr = {
      val slice0 = (w-1, hi+1)
      val slice2 = (lo-1, 0)
      
      // Convert a valid slice into Some(bvexpr) and an invalid slice into none.
      def getSlice(slice : (Int, Int), arg : z3.BitVecExpr) : Option[z3.BitVecExpr] = {
        if (slice._1 >= slice._2) {
          Utils.assert(slice._1 < w && slice._1 >= 0, "Invalid slice: " + slice.toString)
          Utils.assert(slice._2 < w && slice._2 >= 0, "Invalid slice: " + slice.toString)
          Some(ctx.mkExtract(slice._1, slice._2, arg))
        } else {
          None
        }
      }
      // Now merge the slices.
      val slices : List[z3.BitVecExpr] = List(getSlice(slice0, arg0), Some(arg1), getSlice(slice2, arg0)).flatten
      val repl = slices.tail.foldLeft(slices.head)((r0, r1) => ctx.mkConcat(r0, r1))
      Utils.assert(w == repl.getSortSize(), "Invalid result size.")
      return repl
    }
    op match {
      case IntLTOp                => ctx.mkLt (arithArgs(0), arithArgs(1))
      case IntLEOp                => ctx.mkLe (arithArgs(0), arithArgs(1))
      case IntGTOp                => ctx.mkGt (arithArgs(0), arithArgs(1))
      case IntGEOp                => ctx.mkGe (arithArgs(0), arithArgs(1))
      case IntAddOp               => ctx.mkAdd (arithArgs : _*)
      case IntSubOp               => ctx.mkSub (arithArgs: _*)
      case IntMulOp               => ctx.mkMul (arithArgs : _*)
      case BVLTOp(_)              => ctx.mkBVSLT(bvArgs(0), bvArgs(1))
      case BVLEOp(_)              => ctx.mkBVSLE(bvArgs(0), bvArgs(1))
      case BVGTOp(_)              => ctx.mkBVSGT(bvArgs(0), bvArgs(1))
      case BVGEOp(_)              => ctx.mkBVSGE(bvArgs(0), bvArgs(1))
      case BVAddOp(_)             => ctx.mkBVAdd(bvArgs(0), bvArgs(1))
      case BVSubOp(_)             => ctx.mkBVSub(bvArgs(0), bvArgs(1))
      case BVMulOp(_)             => ctx.mkBVMul(bvArgs(0), bvArgs(1))
      case BVAndOp(_)             => ctx.mkBVAND(bvArgs(0), bvArgs(1))
      case BVOrOp(_)              => ctx.mkBVOR(bvArgs(0), bvArgs(1))
      case BVXorOp(_)             => ctx.mkBVXOR(bvArgs(0), bvArgs(1))
      case BVNotOp(_)             => ctx.mkBVNot(bvArgs(0))
      case BVExtractOp(hi, lo)    => ctx.mkExtract(hi, lo, bvArgs(0))
      case BVConcatOp(w)          => ctx.mkConcat(bvArgs(0), bvArgs(1))
      case BVReplaceOp(w, hi, lo) => mkReplace(w, hi, lo, bvArgs(0), bvArgs(1))
      case NegationOp             => ctx.mkNot (boolArgs(0))
      case IffOp                  => ctx.mkIff (boolArgs(0), boolArgs(1))
      case ImplicationOp          => ctx.mkImplies (boolArgs(0), boolArgs(1))
      case EqualityOp             => ctx.mkEq(exprArgs(0), exprArgs(1)) 
      case ConjunctionOp          => ctx.mkAnd (boolArgs : _*)
      case DisjunctionOp          => ctx.mkOr (boolArgs : _*)
      case RecordSelectOp(fld)    =>
        val prodType = operands(0).typ.asInstanceOf[ProductType]
        val fieldIndex = prodType.fieldIndex(fld)
        val prodSort = getProductSort(prodType)
        prodSort.getFieldDecls()(fieldIndex).apply(exprArgs(0))            
      case RecordUpdateOp(fld) =>
        val prodType = operands(0).typ.asInstanceOf[ProductType]
        val fieldIndex = prodType.fieldIndex(fld)
        val indices = prodType.fieldIndices
        val prodSort = getProductSort(prodType)
        val newFields = indices.map{ (i) =>
          if (i == fieldIndex) exprArgs(1)
          else prodSort.getFieldDecls()(i).apply(exprArgs(0))
        }
        prodSort.mkDecl().apply(newFields.toSeq : _*)
      case _             => throw new Utils.UnimplementedException("Operator not yet implemented: " + op.toString())
    }
  }
  
  /** Convert an smt.Expr object into a Z3 AST.  */
  val exprToZ3 : Memo[Expr, z3.AST] = new Memo[Expr, z3.AST]((e) => {
    val z3AST : z3.AST = e match {
      case Symbol(id, typ) => 
        symbolToZ3(Symbol(id, typ))
      case OperatorApplication(op,operands) =>
        opToZ3(op, operands)
      case ArraySelectOperation(e, index) =>
        val arrayType = e.typ.asInstanceOf[ArrayType]
        val arrayIndexType = arrayType.inTypes
        val indexTuple = getTuple(index.map((arg) => exprToZ3(arg)), arrayIndexType)
        ctx.mkSelect(exprToZ3(e).asInstanceOf[z3.ArrayExpr], indexTuple)
      case ArrayStoreOperation(e, index, value) =>
        val arrayType = e.typ.asInstanceOf[ArrayType]
        val arrayIndexType = arrayType.inTypes
        val indexTuple = getTuple(index.map((arg) => exprToZ3(arg)), arrayIndexType)
        val data = exprToZ3(value).asInstanceOf[z3.Expr]
        ctx.mkStore(exprToZ3(e).asInstanceOf[z3.ArrayExpr], indexTuple, data)
      case FunctionApplication(e, args) =>
        val func = exprToZ3(e).asInstanceOf[z3.FuncDecl]
        func.apply(typecastAST[z3.Expr](args.map(exprToZ3(_))).toSeq : _*)
      case ITE(e,t,f) =>
        ctx.mkITE(exprToZ3(e).asInstanceOf[z3.BoolExpr], exprToZ3(t).asInstanceOf[z3.Expr], exprToZ3(f).asInstanceOf[z3.Expr])
      case Lambda(_,_) =>
        throw new Utils.RuntimeError("Lambdas in assertions should have been beta-reduced.")
      case IntLit(i) => getIntLit(i)
      case BitVectorLit(bv,w) => getBitVectorLit(bv, w)
      case BooleanLit(b) => getBoolLit(b)
      case MakeTuple(args) => 
        val tupleSort = getTupleSort(args.map(_.typ))
        tupleSort.mkDecl().apply(typecastAST[z3.Expr](args.map(exprToZ3(_))).toSeq : _*)
      case _ =>
        throw new Utils.UnimplementedException("No translation for expression yet: " + e.toString)
    }
    // z3AST
    if (z3AST.isInstanceOf[z3.Expr]) z3AST.asInstanceOf[z3.Expr].simplify()
    else z3AST
  })
  
  override def addConstraint(e : Expr) : Unit = {
    solver.add(exprToZ3(e).asInstanceOf[z3.BoolExpr])
  }
  
  /** Check whether a particular expression is satisfiable.  */      
  override def check (e : Expr) : Option[Boolean] = {
    val z3Expr = exprToZ3(e)
    // println("Z3 Expression: " + z3Expr.toString)
    
    solver.push()
    solver.add(z3Expr.asInstanceOf[z3.BoolExpr])
    val result = solver.check()
    solver.pop()
    
    if (result == z3.Status.SATISFIABLE) {
      Some(true)
    } else if (result == z3.Status.UNSATISFIABLE) {
      Some(false)
    } else {
      None
    }
  }
  
  override def addAssumptions(es : List[Expr]) {
    solver.push()
    es.foreach((e) => {
      println("adding assumption: " + e.toString())
      solver.add(exprToZ3(e).asInstanceOf[z3.BoolExpr])
    })
  }
  override def popAssumptions() {
    solver.pop()
  }
  
}

object Z3Interface {
  def newInterface() : Z3Interface = {
    var cfg = new HashMap[String, String]()
    cfg.put("model", "true")
    var ctx = new z3.Context(cfg)
    var solver = ctx.mkSolver()
    return new Z3Interface(ctx, solver)
  }
}
