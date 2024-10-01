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
import scala.collection.immutable.ListMap

import scala.collection.mutable.Map
import com.microsoft.z3.enumerations.Z3_lbool
import com.microsoft.z3.enumerations.Z3_decl_kind
import com.typesafe.scalalogging.Logger

import org.json4s._
import org.json4s.jackson.JsonMethods._


/**
 * Result of solving a Z3 instance.
 */
class Z3Model(interface: Z3Interface, val model : z3.Model) extends Model {
  override def evalAsString(e : Expr) : String = {
    interface.exprToZ3(e) match {
      case z3ArrayExpr : z3.ArrayExpr[_, _] => convertZ3ArrayString(z3ArrayExpr)
      case z3Expr : z3.Expr[_] => model.eval(z3Expr, true).toString
      case _ => throw new Utils.EvaluationError("Unable to evaluate expression: " + e.toString)
    }
  }

  override def evalAsJSON(e : Expr) : JValue = {
    interface.exprToZ3(e) match {
      case z3ArrayExpr : z3.ArrayExpr[_, _] => convertZ3ArrayJSON(z3ArrayExpr)
      case z3Expr : z3.Expr[_] => JString(model.eval(z3Expr, true).toString)
      case _ => throw new Utils.EvaluationError("Unable to evaluate expression: " + e.toString)
    }
  }

  def convertZ3ArrayString(initExpr : z3.Expr[_]) : String = {

    val array : Map[String, String] = Map.empty[String, String]
    var e    : z3.Expr[_] = model.eval(initExpr, true)
    var bottom : String = ""
    var longest : Integer = 1
    var isNumeral : Boolean = false


    while (e.isStore()) {
      val args : Array[z3.Expr[_]] = e.getArgs()
      if (!array.contains(args(1).toString)) {
        array += (args(1).toString -> args(2).toString)
      }
      isNumeral = args(1).isNumeral()
      e = model.eval(args(0), true)
    }

    if (e.isConstantArray()) {
      bottom = e.getArgs()(0).toString
    } else if (e.isAsArray) {
      var fd : z3.FuncDecl[_] = e.getFuncDecl().getParameters()(0).getFuncDecl()
      var fint : z3.FuncInterp[_] = null
    
      do {
        fint = model.getFuncInterp(fd)

        for (entry <- fint.getEntries()) {
          val args : Array[z3.Expr[_]] = entry.getArgs()
          if (!array.contains(args(0).toString)) {
            array += (args(0).toString -> entry.getValue().toString)
          }
        }

        fd = fint.getElse().getFuncDecl()
      } while (fint.getElse().getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UNINTERPRETED)

      bottom = fint.getElse().toString
    } else {
      return "UCLID is unable to convert this z3 array to string: " + e.toString + "\n"
    }

    array.foreach{ case (k, v) => {
        if (!v.contentEquals(bottom) && k.length > longest) {
            longest = k.length
        }
    }}
 
    var output : String = ""
    val sortedArray : ListMap[String,String] = if (isNumeral) 
        ListMap(array.toSeq.sortWith((x, y) => BigInt(x._1) < BigInt(y._1)):_*) 
        else ListMap(array.toSeq.sortBy(_._1):_*) 
    sortedArray.foreach{ case (k,v) => {
      if (!v.contentEquals(bottom)) {
        output += k.formatted(s"\n\t%${longest}s : $v")
      }
    }}

    return output + "-".formatted(s"\n\t%${longest}s : $bottom")
  }

  def convertZ3ArrayJSON(initExpr : z3.Expr[_]) : JValue = {

    val array : Map[String, String] = Map.empty[String, String]
    var e    : z3.Expr[_] = model.eval(initExpr, true)
    var bottom : String = ""
    var longest : Integer = 1
    var isNumeral : Boolean = false


    while (e.isStore()) {
      val args : Array[z3.Expr[_]] = e.getArgs()
      if (!array.contains(args(1).toString)) {
        array += (args(1).toString -> args(2).toString)
      }
      isNumeral = args(1).isNumeral()
      e = model.eval(args(0), true)
    }

    if (e.isConstantArray()) {
      bottom = e.getArgs()(0).toString
    } else if (e.isAsArray) {
      var fd : z3.FuncDecl[_] = e.getFuncDecl().getParameters()(0).getFuncDecl()
      var fint : z3.FuncInterp[_] = null
    
      do {
        fint = model.getFuncInterp(fd)

        for (entry <- fint.getEntries()) {
          val args : Array[z3.Expr[_]] = entry.getArgs()
          if (!array.contains(args(0).toString)) {
            array += (args(0).toString -> entry.getValue().toString)
          }
        }

        fd = fint.getElse().getFuncDecl()
      } while (fint.getElse().getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UNINTERPRETED)

      bottom = fint.getElse().toString
    } else {
      return JString("UCLID is unable to convert this z3 array to string: " + e.toString + "\n").asInstanceOf[JValue]
    }

    array.foreach{ case (k, v) => {
        if (!v.contentEquals(bottom) && k.length > longest) {
            longest = k.length
        }
    }}
 
    val sortedArray : ListMap[String,String] = if (isNumeral) 
        ListMap(array.toSeq.sortWith((x, y) => BigInt(x._1) < BigInt(y._1)):_*) 
        else ListMap(array.toSeq.sortBy(_._1):_*) 
    JObject(sortedArray.filter({case (k, v) => !v.contentEquals(bottom)}).map{
      case (k, v) => (k.toString() -> JString(v.toString()))
    }.+("-" -> JString(bottom)).toList)
  }

  override def evaluate(e : Expr) : Expr = {
    interface.exprToZ3(e) match {
      case z3Expr : z3.Expr[_] =>
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
  /** The parameters we will use. */
  val params = ctx.mkParams()
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
  lazy val realSort = ctx.mkRealSort()
  val getBitVectorSort = new Memo[Int, z3.BitVecSort]((w : Int) => ctx.mkBitVecSort(w))
  val getFltSort = new Memo[(Int, Int), z3.FPSort]( (e: (Int, Int)) => ctx.mkFPSort(e._1,e._2))
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
  val getArraySort = new Memo[(List[Type], Type), z3.ArraySort[_, _]]((arrayType : (List[Type], Type)) => {
    val indexTypeIn = arrayType._1
    val z3IndexType = getArrayIndexSort(indexTypeIn)
    ctx.mkArraySort(z3IndexType, getZ3Sort(arrayType._2))
  })
  val getEnumSort = new Memo[List[String], z3.EnumSort[_]]((enumConstants : List[String]) => {
    ctx.mkEnumSort(getEnumName(), enumConstants :_ *)
  })

  val getDataSort = new Memo[(String, List[ConstructorType]), z3.DatatypeSort[_]]((dt: (String, List[ConstructorType])) => {
    val constructors = dt._2.map(c => {
      val name = c.id
      val recognizer = "is-" + c.id
      val fieldNames = c.inTypes.map(pair => pair._1).toArray
      val sorts = c.inTypes.map(pair => 
        pair._2 match {
          case SelfReferenceType(name) => null
          case t => getZ3Sort(t)
        }).toArray
      val sortRefs = c.inTypes.map(pair => 
        pair._2 match {
          case SelfReferenceType(name) => 0
          case t => 1
        }).toArray
      ctx.mkConstructor(name, recognizer, fieldNames, sorts, sortRefs)
    }).toArray
    ctx.mkDatatypeSort(dt._1, constructors.asInstanceOf[Array[com.microsoft.z3.Constructor[com.microsoft.z3.DatatypeSort[_]]]])
  })

  /** Convert uclid.smt types to Z3 sorts. */
  def getZ3Sort (typ : smt.Type) : z3.Sort = {
    typ  match {
      case UninterpretedType(n) => getUninterpretedSort(n)
      case BoolType             => boolSort
      case IntType              => intSort
      case RealType             => realSort
      case BitVectorType(w)     => getBitVectorSort(w)
      case FltType(e,s)         => getFltSort((e,s))
      case TupleType(ts)        => getTupleSort(ts)
      case RecordType(rs)       => getRecordSort(rs)
      case ArrayType(rs, d)     => getArraySort(rs, d)
      case EnumType(ids)        => getEnumSort(ids)
      case DataType(id, cstors) => getDataSort((id, cstors))
      case SynonymType(_, _) | MapType(_, _) | UndefinedType  | SelfReferenceType(_) | ConstructorType(_, _, _) | TesterType(_, _) =>
        throw new Utils.RuntimeError("Must not use getZ3Sort to convert type: " + typ.toString() + ".")
    }
  }

  /** Create a Z3 tuple AST. */
  def getTuple(values : List[z3.AST], tupleMemberTypes : List[Type]) : z3.Expr[z3.TupleSort] = {
    val tupleType = TupleType(tupleMemberTypes)
    val tupleSort = getZ3Sort(tupleType).asInstanceOf[z3.TupleSort]
    val tupleCons = tupleSort.mkDecl()
    tupleCons.apply(typecastAST[z3.Expr[_]](values).toSeq : _*)
  }

  /** Create a boolean literal. */
  val getBoolLit = new Memo[Boolean, z3.BoolExpr](b => ctx.mkBool(b))

  /** Create an integer literal. */
  val getIntLit = new Memo[BigInt, z3.IntExpr](i => ctx.mkInt(i.toString))

  /** Create a real literal. */
  val getRealLit = new Memo[(BigInt, String), z3.RealExpr]((rl) => ctx.mkReal(rl._1.toString + "." + rl._2))

  /** Create a bitvector literal. */
  val getBitVectorLit = new Memo[(BigInt, Int), z3.BitVecExpr]((arg) => ctx.mkBV(arg._1.toString, arg._2))

  /** Create an enum literal. */
  val getEnumLit = new Memo[(String, EnumType), z3.Expr[_]]((p) => getEnumSort(p._2.members).getConst(p._2.fieldIndex(p._1)))

  /** Create a constant array literal. */
  val getConstArray = new Memo[(Expr, ArrayType), z3.Expr[_]]({
    (p) => {
      val value = exprToZ3(p._1).asInstanceOf[z3.Expr[_]]
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
    case class ConstructorSort(name: String, out : Type) extends ExprSort
    case class TesterSort(name: String, inType : Type) extends ExprSort


    val exprSort = (sym.typ) match {
      case UninterpretedType(name) => VarSort(getUninterpretedSort(name))
      case BoolType => VarSort(boolSort)
      case IntType => VarSort(intSort)
      case RealType => VarSort(realSort)
      case BitVectorType(w) => VarSort(getBitVectorSort(w))
      case FltType(e,s) => VarSort(getFltSort((e,s)))
      case TupleType(ts) => VarSort(getTupleSort(ts))
      case RecordType(rs) => VarSort(getRecordSort(rs))
      case MapType(ins, out) => MapSort(ins, out)
      case ArrayType(ins, out) => VarSort(getArraySort(ins, out))
      case EnumType(ids) => VarSort(getEnumSort(ids))
      case DataType(id, cstors) => VarSort(getDataSort(id, cstors))
      case ConstructorType(id, _, outTyp) => ConstructorSort(id, outTyp)
      case TesterType(id, inType) => TesterSort(id, inType)
      case SynonymType(_, _) | UndefinedType | SelfReferenceType(_) =>
        throw new Utils.RuntimeError("Must not use symbolToZ3 on: " + sym.typ.toString() + ".")
    }

    exprSort match {
      case VarSort(s) =>
        ctx.mkConst(sym.id, s)
      case MapSort(ins, out) =>
        ctx.mkFuncDecl(sym.id, ins.map(getZ3Sort _).toArray, getZ3Sort(out))
      case ConstructorSort(name, out) =>
        val adt = getZ3Sort(out).asInstanceOf[z3.DatatypeSort[_]]
        adt.getConstructors().find(c => c.getName().toString() == name).get
      case TesterSort(name, inType) =>
        val adt = getZ3Sort(inType).asInstanceOf[z3.DatatypeSort[_]]
        val recognizers = adt.getRecognizers()
        val constructors = adt.getConstructors().map(c => c.getName().toString())
        val index = constructors.indexWhere(c => "is_" + c == name)
        recognizers(index)
    }
  }

  /** Convert an OperatorApplication into a Z3 AST.  */
  def opToZ3(op : Operator, operands : List[Expr]) : z3.Expr[_]  = {
    lazy val args = operands.map((arg) => exprToZ3(arg))
    // These values need to be lazy so that they are only evaluated when the appropriate ctx.mk* functions
    // are called. If they were eager, the casts would fail at runtime.
    lazy val exprArgs = typecastAST[z3.Expr[_]](args)
    lazy val arithArgs = typecastAST[z3.ArithExpr[_]](args)
    lazy val boolArgs = typecastAST[z3.BoolExpr](args)
    lazy val bvArgs = typecastAST[z3.BitVecExpr](args)
    lazy val intArgs = typecastAST[z3.IntExpr](args)

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
      case IntDivOp               => ctx.mkDiv (arithArgs(0), arithArgs(1))
      case RealLTOp               => ctx.mkLt (arithArgs(0), arithArgs(1))
      case RealLEOp               => ctx.mkLe (arithArgs(0), arithArgs(1))
      case RealGTOp               => ctx.mkGt (arithArgs(0), arithArgs(1))
      case RealGEOp               => ctx.mkGe (arithArgs(0), arithArgs(1))
      case RealAddOp              => ctx.mkAdd (arithArgs : _*)
      case RealSubOp              =>
        if (args.size == 1) {
          ctx.mkUnaryMinus(arithArgs(0))
        } else {
          ctx.mkSub (arithArgs: _*)
        }
      case RealMulOp              => ctx.mkMul (arithArgs : _*)
      case RealDivOp              => ctx.mkDiv (arithArgs(0), arithArgs(1))
      case BVLTOp(_)              => ctx.mkBVSLT(bvArgs(0), bvArgs(1))
      case BVLEOp(_)              => ctx.mkBVSLE(bvArgs(0), bvArgs(1))
      case BVGTOp(_)              => ctx.mkBVSGT(bvArgs(0), bvArgs(1))
      case BVGEOp(_)              => ctx.mkBVSGE(bvArgs(0), bvArgs(1))
      case BVLTUOp(_)             => ctx.mkBVULT(bvArgs(0), bvArgs(1))
      case BVLEUOp(_)             => ctx.mkBVULE(bvArgs(0), bvArgs(1))
      case BVGTUOp(_)             => ctx.mkBVUGT(bvArgs(0), bvArgs(1))
      case BVGEUOp(_)             => ctx.mkBVUGE(bvArgs(0), bvArgs(1))
      case BVAddOp(_)             => ctx.mkBVAdd(bvArgs(0), bvArgs(1))
      case BVSubOp(_)             => ctx.mkBVSub(bvArgs(0), bvArgs(1))
      case BVMulOp(_)             => ctx.mkBVMul(bvArgs(0), bvArgs(1))
      case BVDivOp(_)             => ctx.mkBVSDiv(bvArgs(0), bvArgs(1))
      case BVUDivOp(_)            => ctx.mkBVUDiv(bvArgs(0), bvArgs(1))
      case BVMinusOp(_)           => ctx.mkBVNeg(bvArgs(0))
      case BVAndOp(_)             => ctx.mkBVAND(bvArgs(0), bvArgs(1))
      case BVUremOp(_)            => ctx.mkBVURem(bvArgs(0), bvArgs(1))
      case BVSremOp(_)            => ctx.mkBVSRem(bvArgs(0), bvArgs(1))  
      case BVOrOp(_)              => ctx.mkBVOR(bvArgs(0), bvArgs(1))
      case BVXorOp(_)             => ctx.mkBVXOR(bvArgs(0), bvArgs(1))
      case BVNotOp(_)             => ctx.mkBVNot(bvArgs(0))
      case BVExtractOp(hi, lo)    => ctx.mkExtract(hi, lo, bvArgs(0))
      case BVConcatOp(_)          => ctx.mkConcat(bvArgs(0), bvArgs(1))
      case BVReplaceOp(w, hi, lo) => mkReplace(w, hi, lo, bvArgs(0), bvArgs(1))
      case BVSignExtOp(_, e)      => ctx.mkSignExt(e, bvArgs(0))
      case BVZeroExtOp(_, e)      => ctx.mkZeroExt(e, bvArgs(0))
      case BVLeftShiftBVOp(_)     => ctx.mkBVSHL(bvArgs(0), bvArgs(1))
      case BVLRightShiftBVOp(_)   => ctx.mkBVLSHR(bvArgs(0), bvArgs(1))
      case BVARightShiftBVOp(_)   => ctx.mkBVASHR(bvArgs(0), bvArgs(1))
      case NegationOp             => ctx.mkNot (boolArgs(0))
      case IffOp                  => ctx.mkIff (boolArgs(0), boolArgs(1))
      case ImplicationOp          => ctx.mkImplies (boolArgs(0), boolArgs(1))
      case EqualityOp             => ctx.mkEq(exprArgs(0), exprArgs(1))
      case InequalityOp           => ctx.mkDistinct(exprArgs: _*)
      case ConjunctionOp          => ctx.mkAnd (boolArgs : _*)
      case DisjunctionOp          => ctx.mkOr (boolArgs : _*)
      case ITEOp                  => ctx.mkITE(exprArgs(0).asInstanceOf[z3.BoolExpr], exprArgs(1), exprArgs(2))
      case ForallOp(vs, patterns)           =>
        // val qTyps = vs.map((v) => getZ3Sort(v.typ)).toArray
        val qVars = vs.map((v) => symbolToZ3(v).asInstanceOf[z3.Expr[_]]).toArray
        val qPatterns = patterns.map { ps => {
            val qs = ps.map(p => exprToZ3(p).asInstanceOf[z3.Expr[_]])
            ctx.mkPattern(qs : _*)
          }
        }.toArray
        ctx.mkForall(qVars, boolArgs(0), 1, qPatterns, null, getForallName(), getSkolemName())
      case ExistsOp(vs, patterns)           =>
        val qVars = vs.map((v) => symbolToZ3(v).asInstanceOf[z3.Expr[_]]).toArray
        val qPatterns = patterns.map { ps => {
            val qs = ps.map(p => exprToZ3(p).asInstanceOf[z3.Expr[_]])
            ctx.mkPattern(qs : _*)
          }
        }.toArray
        ctx.mkExists(qVars, boolArgs(0), 1, qPatterns, null, getExistsName(), getSkolemName())
      case RecordSelectOp(fld) if operands(0).typ.isInstanceOf[ProductType] =>
        val prodType = operands(0).typ.asInstanceOf[ProductType]
        val fieldIndex = prodType.fieldIndex(fld)
        val prodSort = getProductSort(prodType)
        prodSort.getFieldDecls()(fieldIndex).apply(exprArgs(0))
      case RecordSelectOp(fld) if operands(0).typ.isInstanceOf[DataType] =>
        // find the right selector to apply based on fld and dataType
        val dataType = operands(0).typ.asInstanceOf[DataType]
        val z3adt = getDataSort(dataType.id, dataType.cstors)
        val sel = z3adt.getAccessors().flatMap(a => a).find(a => a.getName().toString() == fld).get
        // apply it and return the result
        sel.apply(exprArgs(0))
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
      case BV2SignedIntOp() =>
        ctx.mkBV2Int(bvArgs(0), true)
      case BV2UnsignedIntOp() =>
        ctx.mkBV2Int(bvArgs(0), false)
      case Int2BVOp(w) =>
        ctx.mkInt2BV(w, intArgs(0))
      case _             => throw new Utils.UnimplementedException("Operator not yet implemented: " + op.toString())
    }
  }

  /** Convert an smt.Expr object into a Z3 AST.  */
  val exprToZ3 : Memo[Expr, z3.AST] = new Memo[Expr, z3.AST]((e) => {
    def toArrayIndex(index : List[Expr], indexType : List[Type]) : z3.Expr[z3.TupleSort] = {
      if (index.size == 1) {
        exprToZ3(index(0)).asInstanceOf[z3.Expr[z3.TupleSort]]
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
        ctx.mkSelect(exprToZ3(e).asInstanceOf[z3.ArrayExpr[z3.TupleSort, z3.TupleSort]], arrayIndex)
      case ArrayStoreOperation(e, index, value) =>
        val arrayType = e.typ.asInstanceOf[ArrayType]
        val arrayIndexType = arrayType.inTypes
        val arrayIndex = toArrayIndex(index, arrayIndexType)
        val data = exprToZ3(value).asInstanceOf[z3.Expr[z3.TupleSort]]
        ctx.mkStore(exprToZ3(e).asInstanceOf[z3.ArrayExpr[z3.TupleSort, z3.TupleSort]], arrayIndex, data)
      case FunctionApplication(e, args) =>
        val func = exprToZ3(e).asInstanceOf[z3.FuncDecl[_]]
        func.apply(typecastAST[z3.Expr[_]](args.map(exprToZ3(_))).toSeq : _*)
      case Lambda(_,_) =>
        throw new Utils.RuntimeError("Lambdas in assertions should have been beta-reduced.")
      case IntLit(i) => getIntLit(i)
      case RealLit(i,f) => getRealLit(i,f)
      case BitVectorLit(bv,w) => getBitVectorLit(bv, w)
      case BooleanLit(b) => getBoolLit(b)
      case EnumLit(e, typ) => getEnumLit(e, typ)
      case ConstArray(expr, typ) => getConstArray(expr, typ)
      case r : ConstRecord => 
        val prodSort = getProductSort(r.typ.asInstanceOf[ProductType])
        prodSort.mkDecl().apply(typecastAST[z3.Expr[_]](r.fieldvalues.map(f => exprToZ3(f._2))).toSeq : _*)
      case MakeTuple(args) =>
        val tupleSort = getTupleSort(args.map(_.typ))
        tupleSort.mkDecl().apply(typecastAST[z3.Expr[_]](args.map(exprToZ3(_))).toSeq : _*)
    }
    assertLogger.debug("expr: " + e.toString())
    assertLogger.debug("z3  : " + z3AST.toString())
    // z3AST
    if (z3AST.isInstanceOf[z3.Expr[_]]) z3AST.asInstanceOf[z3.Expr[_]].simplify()
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

  lazy val checkLogger = Logger("uclid.smt.Z3Interface.check")
  /** Check whether a particular expression is satisfiable.  */
  override def check(produceModel: Boolean = true) : SolverResult = {
    lazy val smtOutput = solver.toString()
    checkLogger.debug(smtOutput)

    if (filePrefix == "") {
      val z3Result = solver.check()

      val checkResult : SolverResult = z3Result match {
        case z3.Status.SATISFIABLE =>
          checkLogger.debug("SAT")
          val model = if(produceModel) {
            val z3Model = solver.getModel()
            checkLogger.debug("Model: {}", z3Model.toString())
            Some(new Z3Model(this, z3Model))
          } else { None }
          SolverResult(Some(true), model)
        case z3.Status.UNSATISFIABLE =>
          checkLogger.debug("UNSAT")
          SolverResult(Some(false), None)
        case _ =>
          checkLogger.debug("UNDET")
          SolverResult(None, None)
      }
      return checkResult
    } else {
      Utils.writeToFile(f"$filePrefix%s-$curAssertName%s-$curAssertPos%s-$curAssertLabel%s-$counten%04d.smt", smtOutput + "\n\n(check-sat)\n(get-info :all-statistics)\n")
      counten += 1
      return SolverResult(None, None)
    }
  }

  override def checkSynth() : SolverResult = {
    throw new Utils.UnimplementedException("Can't use an SMT solver for synthesis!")
  }

  override def finish() {
    ctx.close()
  }

  override def addOption(opt: String, value: Context.SolverOption): Unit = {
    value match {
      case Context.BoolOption(b) => params.add(opt, b)
      case Context.IntOption(i) => params.add(opt, i)
      case Context.DoubleOption(d) => params.add(opt, d)
      case Context.StringOption(s) => params.add(opt, s)
    }
    solver.setParameters(params)
  }
}


object FixedpointTest
{
  def test() : Unit = {
    // Transition system
    //
    // Init(x, y) = x == 0 && y > 1
    // Transition(x, y, x', y') = (x' = x + 1) && (y' = y + x)
    // Bad(x, y) = x >= y
    //
    // Init(x, y) => Inv(x, y)
    // Inv(x, y) & (x' = x + 1) & (y' = y + 1) => Inv(x', y')
    // Inv(x, y) & (x >= y) => error() 
    z3.Global.setParameter("fixedpoint.engine", "pdr")

    val ctx = new z3.Context()
    val intSort = ctx.mkIntSort()
    val boolSort = ctx.mkBoolSort()
    val fp = ctx.mkFixedpoint()

    val sorts2 = Array[z3.Sort](intSort, intSort)
    val invDecl = ctx.mkFuncDecl("inv", sorts2, boolSort)
    val errorDecl = ctx.mkFuncDecl("error", Array[z3.Sort](), boolSort)

    val symbolx = ctx.mkSymbol(0)
    val symboly = ctx.mkSymbol(1)
    val symbols2 = Array[z3.Symbol](symbolx, symboly)
    val x = ctx.mkBound(0, sorts2(0)).asInstanceOf[z3.ArithExpr[_]]
    val y = ctx.mkBound(1, sorts2(1)).asInstanceOf[z3.ArithExpr[_]]
    
    def applyDecl(f : z3.FuncDecl[_], x : z3.ArithExpr[_], y : z3.ArithExpr[_]) : z3.BoolExpr = {
      f.apply(x, y).asInstanceOf[z3.BoolExpr]
    }
    var qId = 0
    var skId = 0
    def createForall(sorts : Array[z3.Sort], symbols : Array[z3.Symbol], e : z3.Expr[z3.BoolSort]) = {
      qId += 1
      skId += 1
      ctx.mkForall(sorts, symbols, e,
        0, Array[z3.Pattern](), Array[z3.Expr[_]](), ctx.mkSymbol(qId), ctx.mkSymbol(skId))
    }
    
    fp.registerRelation(invDecl)
    fp.registerRelation(errorDecl)

    // x >= 0 && y >= 0 ==> inv(x, y)
    val xEq0 = ctx.mkEq(x, ctx.mkInt(0))
    val yGt1 = ctx.mkGt(y, ctx.mkInt(1))
    val initCond = ctx.mkAnd(xEq0, yGt1)
    val initRule = createForall(sorts2, symbols2, ctx.mkImplies(initCond, applyDecl(invDecl, x, y)))

    // inv(x, y) ==> inv(x+1, y+x)
    val xPlus1 = ctx.mkAdd(x, ctx.mkInt(1))
    val yPlusx = ctx.mkAdd(y, x)
    val guard = applyDecl(invDecl, x, y)
    val trRule = createForall(sorts2, symbols2, ctx.mkImplies(guard, applyDecl(invDecl, xPlus1, yPlusx)))

    val yProp1 = ctx.mkGe(x, y)
    val propGuard = ctx.mkAnd(applyDecl(invDecl, x, y), yProp1)
    val propRule = createForall(sorts2, symbols2, ctx.mkImplies(propGuard, errorDecl.apply().asInstanceOf[z3.BoolExpr]))
    
    fp.addRule(initRule, ctx.mkSymbol("initRule"))
    fp.addRule(trRule, ctx.mkSymbol("trRule"))
    fp.addRule(propRule, ctx.mkSymbol("propRule"))

    println(fp.toString())

    // property.
    println (fp.query(Array(errorDecl)))
  }
}
