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
 * Z3 Java API interface.
 *
 */

package uclid
package smt

import com.microsoft.{z3 => z3}
import java.util.HashMap;
import scala.collection.mutable.Map
import scala.collection.JavaConverters._
import com.microsoft.z3.enumerations.Z3_lbool

/**
 * Result of solving a Z3 instance.
 */
class Z3Model(interface: Z3Interface, val model : z3.Model) extends Model {
  override def evalAsString(e : Expr) : String = {
    interface.exprToZ3(e) match {
      case z3Expr : z3.Expr => model.eval(z3Expr, true).toString
      case _ => throw new Utils.EvaluationError("Unable to evaluate expression: " + e.toString)
    }
  }
  override def evaluate(e : Expr) : Expr = {
    interface.exprToZ3(e) match {
      case z3Expr : z3.Expr => 
        val value = model.eval(z3Expr, true)
        if (value.isIntNum()) {
          val bigInt = value.asInstanceOf[z3.IntNum].getBigInteger()
          smt.IntLit(bigInt)
        } else if (value.isBool()) {
          val boolValue = value.asInstanceOf[z3.BoolExpr].getBoolValue()
          if (boolValue == Z3_lbool.Z3_L_TRUE) {
            smt.BooleanLit(true)
          } else if(boolValue == Z3_lbool.Z3_L_FALSE) {
            smt.BooleanLit(false)
          } else {
            throw new Utils.RuntimeError("Unable to get model value for: " + e.toString)
          }
        } else {
          throw new Utils.RuntimeError("Unable to get model value for: " + e.toString)
        }
    }
  }
}

/**
 * Decide validity of SMTExpr's using a Z3 sovler.
 */
class Z3Interface(z3Ctx : z3.Context, z3Solver : z3.Solver) extends SolverInterface {
  // Member variables.
  /** The Z3 context. */
  val ctx = z3Ctx
  /** The Z3 solver. */
  val solver = z3Solver
  
  /* Unique names for Tuples. */
  val tupleNamer = new UniqueNamer("$tuple")
  def getTupleName() : z3.Symbol = { 
    return ctx.mkSymbol(tupleNamer.newName())
  }
  /* Unique names for Enums. */
  val enumNamer = new UniqueNamer("$enum")
  def getEnumName() : String = {
    enumNamer.newName()
  }
  /* Unique names for quantifiers. */
  val forallNamer = new UniqueNamer("$forall")
  def getForallName() = ctx.mkSymbol(forallNamer.newName())
  val existsNamer = new UniqueNamer("$exists")
  def getExistsName() = ctx.mkSymbol(existsNamer.newName())
  val skolemNamer = new UniqueNamer("$skolem")
  def getSkolemName() = ctx.mkSymbol(skolemNamer.newName())

  /** Returns tuple field names. */
  val getTupleFieldNames = new Memo[Int, Array[z3.Symbol]]((n : Int) => {
    (1 to n).map((i => ctx.mkSymbol(i.toString + "__ucl_tuple_field" ))).toArray
  })
  
  
  /** Utility function to cast to subtypes of z3.AST */
  def typecastAST[T <: z3.AST](args : List[z3.AST]) : List[T] = { 
    args.map((arg => arg.asInstanceOf[T]))
  }

  // Methods to convert uclid.smt.Type values into Z3 sorts.
  val getUninterpretedSort = new Memo[String, z3.UninterpretedSort]((name) => ctx.mkUninterpretedSort(name))
  lazy val boolSort = ctx.mkBoolSort()
  lazy val intSort = ctx.mkIntSort()
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
  val getEnumSort = new Memo[List[String], z3.EnumSort]((enumConstants : List[String]) => {
    ctx.mkEnumSort(getEnumName(), enumConstants :_ *)
  })
  
  /** Convert uclid.smt types to Z3 sorts. */
  def getZ3Sort (typ : smt.Type) : z3.Sort = {
    typ  match {
      case UninterpretedType(n) => getUninterpretedSort(n)
      case BoolType()           => boolSort
      case IntType()            => intSort
      case BitVectorType(w)     => getBitVectorSort(w)
      case TupleType(ts)        => getTupleSort(ts)
      case RecordType(rs)       => getRecordSort(rs)
      case ArrayType(rs, d)     => getArraySort(rs, d)
      case EnumType(ids)        => getEnumSort(ids)
      case MapType(rs, d)       =>
        throw new Utils.RuntimeError("Must not use getZ3Sort to convert MapSorts.")
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
  
  /** Create an enum literal. */
  val getEnumLit = new Memo[(String, EnumType), z3.Expr]((p) => getEnumSort(p._2.members).getConst(p._2.fieldIndex(p._1)))
  
  /** Convert a smt.Symbol object into a Z3 AST. */
  def symbolToZ3 (sym : Symbol) : z3.AST = {
    abstract class ExprSort
    case class VarSort(sort : z3.Sort) extends ExprSort
    case class MapSort(ins : List[Type], out : Type) extends ExprSort
    
    val exprSort = (sym.typ) match {
      case UninterpretedType(name) => VarSort(getUninterpretedSort(name))
      case BoolType() => VarSort(boolSort)
      case IntType() => VarSort(intSort)
      case BitVectorType(w) => VarSort(getBitVectorSort(w))
      case TupleType(ts) => VarSort(getTupleSort(ts))
      case RecordType(rs) => VarSort(getRecordSort(rs))
      case MapType(ins, out) => MapSort(ins, out)
      case ArrayType(ins, out) => VarSort(getArraySort(ins, out))
      case EnumType(ids) => VarSort(getEnumSort(ids))
    } 
    
    exprSort match {
      case VarSort(s) => 
        ctx.mkConst(sym.id, s)
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
      case InequalityOp           => ctx.mkDistinct(exprArgs(0), exprArgs(1))
      case ConjunctionOp          => ctx.mkAnd (boolArgs : _*)
      case DisjunctionOp          => ctx.mkOr (boolArgs : _*)
      case ForallOp(vs)           =>
        // val qTyps = vs.map((v) => getZ3Sort(v.typ)).toArray
        val qVars = vs.map((v) => symbolToZ3(v).asInstanceOf[z3.Expr]).toArray
        ctx.mkForall(qVars, boolArgs(0), 1, null, null, getForallName(), getSkolemName())
      case ExistsOp(vs)           =>
        val qVars = vs.map((v) => symbolToZ3(v).asInstanceOf[z3.Expr]).toArray
        ctx.mkExists(qVars, boolArgs(0), 1, null, null, getExistsName(), getSkolemName())
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
      case EnumLit(e, typ) => getEnumLit(e, typ)
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
  override def check (e : Expr) : SolverResult = {
    val z3Expr = exprToZ3(e)
    // println("SMT expression: " + e.toString)
    // println("Z3 Expression: " + z3Expr.toString)
    
    solver.push()
    solver.add(z3Expr.asInstanceOf[z3.BoolExpr])
    // println(solver.toString())
    val z3Result = solver.check()
    // println(z3Result.toString)
    
    val checkResult : SolverResult = z3Result match {
      case z3.Status.SATISFIABLE =>
        val z3Model = solver.getModel()
        // println("model: " + z3Model.toString)
        SolverResult(Some(true), Some(new Z3Model(this, z3Model))) 
      case z3.Status.UNSATISFIABLE =>
        SolverResult(Some(false), None)
      case _ =>
        SolverResult(None, None)
    }
    solver.pop()
    return checkResult
  }
  
  override def addAssumptions(es : List[Expr]) {
    solver.push()
    es.foreach((e) => {
      val eZ3 = exprToZ3(e).asInstanceOf[z3.BoolExpr]
      // println("assumption: " + eZ3.toString)
      solver.add(eZ3)
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
