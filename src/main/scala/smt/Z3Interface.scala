/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Pramod Subramanyan
 *
 * Z3 Java API interface.
 *
 */

package uclid
package smt

import com.microsoft.z3
import java.util.HashMap

import scala.collection.mutable.Map
import scala.collection.JavaConverters._
import com.microsoft.z3.enumerations.Z3_lbool
import com.typesafe.scalalogging.Logger
import java.io.File
import java.io.PrintWriter


/**
 * Result of solving a Z3 instance.
 */
class Z3Model(interface: Z3Interface, val model : z3.Model) extends Model {
  override def evalAsString(e : Expr) : String = {
    interface.exprToZ3(e) match {
      case z3ArrayExpr : z3.ArrayExpr => convertZ3ArrayString(model.eval(z3ArrayExpr, true).toString)
      case z3Expr : z3.Expr => model.eval(z3Expr, true).toString
      case _ => throw new Utils.EvaluationError("Unable to evaluate expression: " + e.toString)
    }
  }

  def convertZ3ArrayString(initString : String) : String = {

    val let_count       = "\\(let \\(\\(a!\\d+ ".r().findAllIn(initString).length
    val tempString      = initString.replaceAll("(\\(let \\(\\(a!\\d+ )?(\\(store )+(a!\\d+)?", "").replaceAll("(\\n.*)\\)\\)\\)(?=\\n)", "$1\\) ").replaceAll("\\n?\\s+", " ")
    val cleanString     = tempString.substring(0, tempString.length() - let_count)

    val prefixArray     = "((as const (Array " //)))
    val prefixArrayLen  = prefixArray.length()

    val totalLen        = cleanString.length()

    var index           = 0;
    var startIndex      = 0;

    if (!cleanString.startsWith(prefixArray, index)) {
      return "ERROR"
    }
    index += prefixArrayLen

    // Skip the array type information
    index = findNextIndexRightParen(cleanString, index, 2)

    // Capture bottom value
    startIndex = index

    index = findNextIndexRightParen(cleanString, index, 1)

    var bottom = cleanString.substring(startIndex, index - 2)


    // Parse all stores operations
    var Array : Map[String, String] = Map.empty[String, String]
    while (index < totalLen) {
      val arrayIndexStartIndex = index
      index = findNextIndexSpace(cleanString, index)
      val arrayIndex = cleanString.substring(arrayIndexStartIndex, index)

      index += 1
      val arrayValueStartIndex = index
      index = findNextIndexRightParen(cleanString, index, 1)
      val arrayValue = cleanString.substring(arrayValueStartIndex, index - 2)

      Array += (arrayIndex -> arrayValue)
    }


    var output : String = ""
    Array.foreach{ case (k,v) => {
      if (!v.contentEquals(bottom)) {
        output = output.concat(s"\n\t$k : $v")
      }
    }}

    return output.concat(s"\n\tbottom : $bottom")

  }

  def findNextIndexRightParen(str : String, idx : Int, target : Int) : Int = {
    var paren = 0;
    var index = idx;

    while (paren < target) {
      val c = str.charAt(index)
      val inc = c match {
        case '(' => -1
        case ')' => 1
        case _   => 0
      }
      paren += inc
      index += 1
    }
    return index + 1
  }

  // Find the index of the next space without open parentheses in str starting at idx
  def findNextIndexSpace(str : String, idx : Int) : Int = {
    var paren = 0;
    var index = idx;

    var c = str.charAt(index)

    val len = str.length()

    while (c != ' ' || paren != 0) {
      val inc = c match {
        case '(' => -1
        case ')' => 1
        case _   => 0
      }
      paren += inc
      index += 1
      c = str.charAt(index)
    }
    return index
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
class Z3Interface() extends Context {

  val cfg = new HashMap[String, String]()
  cfg.put("model", "true")

  /** The Z3 context. */
  val ctx = new z3.Context(cfg)
  ctx.setPrintMode(z3.enumerations.Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT)
  /** The Z3 solver. */
  val solver = ctx.mkSolver()

  /* Unique names for Tuples. */
  val tupleNamer = new UniqueNamer("_tuple")
  def getTupleName() : z3.Symbol = {
    return ctx.mkSymbol(tupleNamer.newName())
  }
  /* Unique names for Enums. */
  val enumNamer = new UniqueNamer("_enum")
  def getEnumName() : String = {
    enumNamer.newName()
  }
  /* Unique names for quantifiers. */
  val forallNamer = new UniqueNamer("_forall")
  def getForallName() = ctx.mkSymbol(forallNamer.newName())
  val existsNamer = new UniqueNamer("_exists")
  def getExistsName() = ctx.mkSymbol(existsNamer.newName())
  val skolemNamer = new UniqueNamer("_skolem")
  def getSkolemName() = ctx.mkSymbol(skolemNamer.newName())

  /** Returns tuple field names. */
  val getTupleFieldNames = new Memo[Int, Array[z3.Symbol]]((n : Int) => {
    (1 to n).map((i => ctx.mkSymbol("__f" + i.toString))).toArray
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
  val getArrayIndexSort = new Memo[List[Type], z3.Sort]({
    p => {
      if (p.size == 1) {
        getZ3Sort(p(0))
      } else {
        getTupleSort(p)
      }
    }
  })
  val getArraySort = new Memo[(List[Type], Type), z3.ArraySort]((arrayType : (List[Type], Type)) => {
    val indexTypeIn = arrayType._1
    val z3IndexType = getArrayIndexSort(indexTypeIn)
    ctx.mkArraySort(z3IndexType, getZ3Sort(arrayType._2))
  })
  val getEnumSort = new Memo[List[String], z3.EnumSort]((enumConstants : List[String]) => {
    ctx.mkEnumSort(getEnumName(), enumConstants :_ *)
  })

  /** Convert uclid.smt types to Z3 sorts. */
  def getZ3Sort (typ : smt.Type) : z3.Sort = {
    typ  match {
      case UninterpretedType(n) => getUninterpretedSort(n)
      case BoolType             => boolSort
      case IntType              => intSort
      case BitVectorType(w)     => getBitVectorSort(w)
      case TupleType(ts)        => getTupleSort(ts)
      case RecordType(rs)       => getRecordSort(rs)
      case ArrayType(rs, d)     => getArraySort(rs, d)
      case EnumType(ids)        => getEnumSort(ids)
      case SynonymType(_, _) | MapType(_, _) | UndefinedType =>
        throw new Utils.RuntimeError("Must not use getZ3Sort to convert type: " + typ.toString() + ".")
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

  /** Create a constant array literal. */
  val getConstArrayLit = new Memo[(Literal, ArrayType), z3.Expr]({
    (p) => {
      val value = exprToZ3(p._1).asInstanceOf[z3.Expr]
      val sort = getArrayIndexSort(p._2.inTypes)
      val arr = ctx.mkConstArray(sort, value)
      arr
    }
  })
  /** Convert a smt.Symbol object into a Z3 AST. */
  def symbolToZ3 (sym : Symbol) : z3.AST = {
    abstract class ExprSort
    case class VarSort(sort : z3.Sort) extends ExprSort
    case class MapSort(ins : List[Type], out : Type) extends ExprSort

    val exprSort = (sym.typ) match {
      case UninterpretedType(name) => VarSort(getUninterpretedSort(name))
      case BoolType => VarSort(boolSort)
      case IntType => VarSort(intSort)
      case BitVectorType(w) => VarSort(getBitVectorSort(w))
      case TupleType(ts) => VarSort(getTupleSort(ts))
      case RecordType(rs) => VarSort(getRecordSort(rs))
      case MapType(ins, out) => MapSort(ins, out)
      case ArrayType(ins, out) => VarSort(getArraySort(ins, out))
      case EnumType(ids) => VarSort(getEnumSort(ids))
      case SynonymType(_, _) | UndefinedType =>
        throw new Utils.RuntimeError("Must not use symbolToZ3 on: " + sym.typ.toString() + ".")
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
      case IntSubOp               =>
        if (args.size == 1) {
          ctx.mkUnaryMinus(arithArgs(0))
        } else {
          ctx.mkSub (arithArgs: _*)
        }
      case IntMulOp               => ctx.mkMul (arithArgs : _*)
      case BVLTOp(_)              => ctx.mkBVSLT(bvArgs(0), bvArgs(1))
      case BVLEOp(_)              => ctx.mkBVSLE(bvArgs(0), bvArgs(1))
      case BVGTOp(_)              => ctx.mkBVSGT(bvArgs(0), bvArgs(1))
      case BVGEOp(_)              => ctx.mkBVSGE(bvArgs(0), bvArgs(1))
      case BVAddOp(_)             => ctx.mkBVAdd(bvArgs(0), bvArgs(1))
      case BVSubOp(_)             => ctx.mkBVSub(bvArgs(0), bvArgs(1))
      case BVMulOp(_)             => ctx.mkBVMul(bvArgs(0), bvArgs(1))
      case BVMinusOp(_)           => ctx.mkBVNeg(bvArgs(0))
      case BVAndOp(_)             => ctx.mkBVAND(bvArgs(0), bvArgs(1))
      case BVOrOp(_)              => ctx.mkBVOR(bvArgs(0), bvArgs(1))
      case BVXorOp(_)             => ctx.mkBVXOR(bvArgs(0), bvArgs(1))
      case BVNotOp(_)             => ctx.mkBVNot(bvArgs(0))
      case BVExtractOp(hi, lo)    => ctx.mkExtract(hi, lo, bvArgs(0))
      case BVConcatOp(w)          => ctx.mkConcat(bvArgs(0), bvArgs(1))
      case BVReplaceOp(w, hi, lo) => mkReplace(w, hi, lo, bvArgs(0), bvArgs(1))
      case BVSignExtOp(w, e)      => ctx.mkSignExt(e, bvArgs(0))
      case BVZeroExtOp(w, e)      => ctx.mkZeroExt(e, bvArgs(0))
      case BVLeftShiftOp(w, e)    => ctx.mkBVSHL(bvArgs(0), ctx.mkBV(e, w))
      case BVLRightShiftOp(w, e)  => ctx.mkBVLSHR(bvArgs(0), ctx.mkBV(e, w))
      case BVARightShiftOp(w, e)  => ctx.mkBVASHR(bvArgs(0), ctx.mkBV(e, w))
      case NegationOp             => ctx.mkNot (boolArgs(0))
      case IffOp                  => ctx.mkIff (boolArgs(0), boolArgs(1))
      case ImplicationOp          => ctx.mkImplies (boolArgs(0), boolArgs(1))
      case EqualityOp             => ctx.mkEq(exprArgs(0), exprArgs(1))
      case InequalityOp           => ctx.mkDistinct(exprArgs(0), exprArgs(1))
      case ConjunctionOp          => ctx.mkAnd (boolArgs : _*)
      case DisjunctionOp          => ctx.mkOr (boolArgs : _*)
      case ITEOp                  => ctx.mkITE(exprArgs(0).asInstanceOf[z3.BoolExpr], exprArgs(1), exprArgs(2))
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
    def toArrayIndex(index : List[Expr], indexType : List[Type]) : z3.Expr = {
      if (index.size == 1) {
        exprToZ3(index(0)).asInstanceOf[z3.Expr]
      } else {
        getTuple(index.map((arg) => exprToZ3(arg)), indexType)
      }
    }
    val z3AST : z3.AST = e match {
      case Symbol(id, typ) =>
        symbolToZ3(Symbol(id, typ))
      case OperatorApplication(op,operands) =>
        opToZ3(op, operands)
      case ArraySelectOperation(e, index) =>
        val arrayType = e.typ.asInstanceOf[ArrayType]
        val arrayIndexType = arrayType.inTypes
        val arrayIndex = toArrayIndex(index, arrayIndexType)
        ctx.mkSelect(exprToZ3(e).asInstanceOf[z3.ArrayExpr], arrayIndex)
      case ArrayStoreOperation(e, index, value) =>
        val arrayType = e.typ.asInstanceOf[ArrayType]
        val arrayIndexType = arrayType.inTypes
        val arrayIndex = toArrayIndex(index, arrayIndexType)
        val data = exprToZ3(value).asInstanceOf[z3.Expr]
        ctx.mkStore(exprToZ3(e).asInstanceOf[z3.ArrayExpr], arrayIndex, data)
      case FunctionApplication(e, args) =>
        val func = exprToZ3(e).asInstanceOf[z3.FuncDecl]
        func.apply(typecastAST[z3.Expr](args.map(exprToZ3(_))).toSeq : _*)
      case Lambda(_,_) =>
        throw new Utils.RuntimeError("Lambdas in assertions should have been beta-reduced.")
      case IntLit(i) => getIntLit(i)
      case BitVectorLit(bv,w) => getBitVectorLit(bv, w)
      case BooleanLit(b) => getBoolLit(b)
      case EnumLit(e, typ) => getEnumLit(e, typ)
      case ConstArrayLit(value, typ) => getConstArrayLit(value, typ)
      case MakeTuple(args) =>
        val tupleSort = getTupleSort(args.map(_.typ))
        tupleSort.mkDecl().apply(typecastAST[z3.Expr](args.map(exprToZ3(_))).toSeq : _*)
    }
    // z3AST
    if (z3AST.isInstanceOf[z3.Expr]) z3AST.asInstanceOf[z3.Expr].simplify()
    else z3AST
  })

  override def push() {
    solver.push()
  }
  override def pop() {
    solver.pop()
  }

  lazy val assertLogger = Logger("uclid.smt.Z3Interface.assert")
  override def assert(e : Expr) {
    val z3Expr = exprToZ3(e).asInstanceOf[z3.BoolExpr]
    assertLogger.debug(e.toString)
    assertLogger.debug(z3Expr.toString())
    solver.add(z3Expr)
  }
  override def preassert(e: Expr) {}

  def writeToFile(p: String, s: String): Unit = {
    val pw = new PrintWriter(new File(p))
    try pw.write(s) finally pw.close()
  } 

  lazy val checkLogger = Logger("uclid.smt.Z3Interface.check")
  /** Check whether a particular expression is satisfiable.  */
  override def check() : SolverResult = {
    val smtOutput = solver.toString()
    checkLogger.debug(smtOutput)

    if (filePrefix == "") {
      val z3Result = solver.check()

      val checkResult : SolverResult = z3Result match {
        case z3.Status.SATISFIABLE =>
          val z3Model = solver.getModel()
          checkLogger.debug("SAT")
          checkLogger.debug("Model: {}", z3Model.toString())
          SolverResult(Some(true), Some(new Z3Model(this, z3Model)))
        case z3.Status.UNSATISFIABLE =>
          checkLogger.debug("UNSAT")
          SolverResult(Some(false), None)
        case _ =>
          checkLogger.debug("UNDET")
          SolverResult(None, None)
      }
      return checkResult
    } else {
      writeToFile(f"$filePrefix%s-$curAssertName%s-$curAssertLabel%s-$counten%04d.smt", smtOutput + "\n\n(check-sat)\n(get-info :all-statistics)\n")
      counten += 1
      return SolverResult(None, None)
    }
  }

  override def finish() {
    ctx.close()
  }
}


object InterpolationTest
{
  def test() : Unit = {
    val cfg = new HashMap[String, String]()
    cfg.put("model", "true")
    cfg.put("proof", "true")
    val ctx = z3.InterpolationContext.mkContext(cfg)
    val solver = ctx.mkSolver()

    val x = ctx.mkIntConst("x")
    val y = ctx.mkIntConst("y")
    val z = ctx.mkIntConst("z")

    val x_eq_y = ctx.mkEq(x, y)
    val x_eq_5 = ctx.mkEq(x, ctx.mkInt(5))
    val A = ctx.mkAnd(x_eq_y, x_eq_5)
    val iA = ctx.MkInterpolant(A)
    val B = ctx.mkDistinct(y, ctx.mkInt(5))
    val pat = ctx.mkAnd(iA, B)
    val params = ctx.mkParams()
    solver.add(A)
    solver.add(B)
    val r = solver.check()
    println("result: " + r.toString())
    val proof = solver.getProof()
    val interp = ctx.ComputeInterpolant(pat, params)
    println("Interpolant: " + interp.interp(0).toString())
  }
}
