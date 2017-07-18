/**
 * @author rohitsinha
 * @author pramod
 * 
 * This class defines an AST for SMT formulas. Uclid assertions are converted to ASTs using this class. 
 * These ASTs can then be readily converted into something Z3 (or potentially other solvers) can understand.
 * 
 */

package uclid {
  package smt {
    import scala.collection.mutable.Map
    
    trait Type {
      def isBool = false
      def isInt = false
      def isBitVector = false
      def isTuple = false
      def isMap = false
      def isArray = false
    }
    
    // The Boolean type.
    case class BoolType() extends Type { 
      override def toString = "bool" 
      override def isBool = true
    }
    object BoolType {
      val t = new BoolType
    }
    // The integer type.
    case class IntType() extends Type { 
      override def toString = "int" 
      override def isInt = true
    }
    object IntType {
      val t = new IntType
    }
    // The bit-vector type.
    case class BitVectorType(width: Int) extends Type
    {
      override def toString = "bv" + (width.toString)
      override def isBitVector = true
    }
    object BitVectorType {
      val t = new Memo[Int, BitVectorType]((w : Int) => new BitVectorType(w))
    }
    
    case class TupleType(types: List[Type]) extends Type {
      val fieldNames = (1 to types.length).map("_" + _.toString)
      val fields = fieldNames zip types
      val fieldIndices = (0 to (types.length - 1))
      def fieldType(name: String) : Option[Type] = fields.find((p) => p._1 == name).flatMap((f) => Some(f._2))
      def hasField(name: String) : Boolean = fields.find((p) => p._1 == name).isDefined
      def fieldIndex(name: String) : Int = fields.indexWhere((p) => p._1 == name)
      override def toString = "tuple [" + types.tail.fold(types.head.toString)
                              { (acc, i) => acc + ", " + i.toString } + "]"
      override def isTuple = true
    }
    object TupleType {
      val t = new Memo[List[Type], TupleType]((l : List[Type]) => new TupleType(l))
    }
    
    case class MapType(inTypes: List[Type], outType: Type) extends Type {
      override def toString = "map [" + inTypes.tail.fold(inTypes.head.toString)
                              { (acc,i) => acc + "," + i.toString } + "] " + outType
      override def isMap = { true }
    }
    object MapType {
      val t = new Memo[(List[Type], Type), MapType]((t: (List[Type],Type)) => new MapType(t._1, t._2))
    }
    
    case class ArrayType(inTypes: List[Type], outType: Type) extends Type {
      override def toString = "array [" + inTypes.tail.fold(inTypes.head.toString)
      { (acc,i) => acc + "," + i.toString } + "] " + outType
      override def isArray = { true }
    }
    object ArrayType {
      val t = new Memo[(List[Type], Type), ArrayType]((t: (List[Type],Type)) => new ArrayType(t._1, t._2))
    }
    
    object OperatorFixity extends scala.Enumeration {
      type OperatorFixity = Value
      val INFIX, PREFIX = Value
    }
    import OperatorFixity._
    
    trait Operator {
      def resultType(args: List[Expr]) : Type
      def typeCheck (args: List[Expr]) : Unit = { }
      def fixity : OperatorFixity
      
      def checkNumArgs(args: List[Expr], expectedNumOperands : Int) : Unit = {
        Utils.assert(args.size == expectedNumOperands, "Operator '" + toString + "' requires " + expectedNumOperands + " operand(s).")
      }
      def checkAllArgTypes(args: List[Expr], expectedType : Type) : Unit = {
        Utils.assert(args.forall(op => op.typ == expectedType), "Operator '" + toString + "' requires operand(s) of type: " + expectedType)
      }
      def checkAllArgsSameType(args: List[Expr]) : Unit = {
        args match {
          case Nil => Utils.assert(false, "Expected at least one operand for '" + toString + "' operator.")
          case head :: tail => Utils.assert(args.forall(op => op.typ == head.typ), "Operands to '" + toString + "' must of the same type.")
        }
      }
    }
    
    // Operators that return integers.
    abstract class IntResultOp extends Operator {
      override def resultType(args: List[Expr]) : Type = { IntType.t }
      override def fixity = { PREFIX }
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    object IntAddOp extends IntResultOp { 
      override def toString = "+" 
    }
    object IntSubOp extends IntResultOp { 
      override def toString = "-" 
    }
    object IntMulOp extends IntResultOp { 
      override def toString = "*" 
    }
    
    // Operators that return bitvectors.
    abstract class BVResultOp(width : Int) extends Operator {
      override def resultType(args: List[Expr]) : Type = { BitVectorType.t(width) }
      override def fixity = PREFIX
      override def typeCheck(args: List[Expr]) : Unit  = { checkNumArgs(args, 2); checkAllArgTypes(args, BitVectorType.t(width)) }
    }
    case class BVAddOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvadd"
    }
    case class BVSubOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvsub"
    }
    case class BVMulOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvmul"
    }
    case class BVAndOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvand"
    }
    case class BVOrOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvor"
    }
    case class BVXorOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvxor"
    }
    case class BVNotOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvneg"
      override def typeCheck(args: List[Expr]) : Unit  = { checkNumArgs(args, 1); checkAllArgTypes(args, BitVectorType.t(w)) }
    }
    case class BVExtractOp(hi : Int, lo : Int) extends BVResultOp(hi - lo + 1) {
      override def toString = "bvextract " + hi + " " + lo
      override def typeCheck(args: List[Expr]) : Unit = { 
        checkNumArgs(args, 1);
        Utils.assert(args(0).typ.isBitVector, "Argument to bitvector extract must be a bitvector.")
        val argBvType = args(0).typ.asInstanceOf[BitVectorType]
        Utils.assert(hi < argBvType.width && lo < argBvType.width && hi >= 0 && lo >= 0, "Invalid indices to bitvector extract.")
      }
    }
    case class BVConcatOp(w : Int) extends BVResultOp(w) {
      override def toString = "bvconcat"
      override def typeCheck(args: List[Expr]) : Unit = { 
        checkNumArgs(args, 2);
        Utils.assert(args.forall(_.typ.isBitVector), "Argument to bitvector concat must be a bitvector.")
        val width = args.foldLeft(0)((acc, ai) => ai.typ.asInstanceOf[BitVectorType].width + acc)
        Utils.assert(width == w, "Incorrect width argument to BVConcatOp.")
      }
    }    
    case class BVReplaceOp(w : Int, hi : Int, lo : Int) extends BVResultOp(w) {
      override def toString = "bvreplace " + hi + " " + lo
      override def typeCheck(args: List[Expr]) : Unit = {
        checkNumArgs(args, 2);
        Utils.assert(args.forall(_.typ.isBitVector), "Argument to bitvector concat must be a bitvector.")
        Utils.assert(args(0).typ.asInstanceOf[BitVectorType].width == w, "Incorrect width of first operand to BVReplaceOp.")
        Utils.assert(args(1).typ.asInstanceOf[BitVectorType].width == (hi-lo+1), "Incorrect width of second operand to BVReplaceOp.")
      }
    }
    // Operators that return Booleans.
    abstract class BoolResultOp extends Operator {
      override def resultType(args: List[Expr]) : Type = { BoolType.t }
      override def fixity = { INFIX }
    }
    
    case object IffOp extends BoolResultOp { 
      override def toString = "<==>"
      override def typeCheck (args: List[Expr]) = {
        Utils.assert(args.size == 2, "Iff must have two operands.")
        Utils.assert(args.forall(op => op.typ.isBool), "Iff operands must be boolean.")
      }
    }
    case object ImplicationOp extends BoolResultOp { 
      override def toString  = "==>" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BoolType.t) }
    }
    case object ConjunctionOp extends BoolResultOp { 
      override def toString = "/\\" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BoolType.t) }
    }
    case object DisjunctionOp extends BoolResultOp { 
      override def toString = "\\/" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BoolType.t) }
    }
    case object NegationOp extends BoolResultOp { 
      override def toString = "not" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 1); checkAllArgTypes(args, BoolType.t) }
      override def fixity = PREFIX
    }
    case object EqualityOp extends BoolResultOp { 
      override def toString = "=" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgsSameType(args) }
    }
    case object InequalityOp extends BoolResultOp {
      override def toString = "distinct"
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgsSameType(args) }
    }
    // Integer comparison.
    case object IntLTOp extends BoolResultOp { 
      override def toString = "<"
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
      override def fixity = PREFIX
    }
    case object IntLEOp extends BoolResultOp { 
      override def toString = "<=" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
      override def fixity = PREFIX
    }
    case object IntGTOp extends BoolResultOp { 
      override def toString = ">" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
      override def fixity = PREFIX
    }
    case object IntGEOp extends BoolResultOp { 
      override def toString = ">=" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
      override def fixity = PREFIX
    }
    // Bitvector comparison.
    case class BVLTOp(w : Int) extends BoolResultOp { 
      override def toString = "bvslt"
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BitVectorType.t(w)) }
      override def fixity = PREFIX
    }
    case class BVLEOp(w : Int) extends BoolResultOp { 
      override def toString = "bvsle" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BitVectorType.t(w)) }
      override def fixity = PREFIX
    }
    case class BVGTOp(w : Int) extends BoolResultOp { 
      override def toString = "bvugt" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BitVectorType.t(w)) }
      override def fixity = PREFIX
    }
    case class BVGEOp(w : Int) extends BoolResultOp { 
      override def toString = "bvuge" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BitVectorType.t(w)) }
      override def fixity = PREFIX
    }
    case class RecordSelectOp(name : String) extends Operator {
      override def toString = "get-field " + name
      override def typeCheck(args: List[Expr]) : Unit = { 
        checkNumArgs(args, 1);
        Utils.assert(args(0).typ.isInstanceOf[TupleType], "Argument to record select must be a tuple.")
        Utils.assert(args(0).typ.asInstanceOf[TupleType].hasField(name), "Field '" + name + "' does not exist in tuple.")
      }
      def resultType(args: List[Expr]) : Type = {
        args(0).typ.asInstanceOf[TupleType].fieldType(name).get
      }
      override def fixity = PREFIX
    }
    case class RecordUpdateOp(name: String) extends Operator {
      override def toString = "update-field " + name
      override def typeCheck(args: List[Expr]) : Unit = {
        checkNumArgs(args, 2)
        Utils.assert(args(0).typ.isInstanceOf[TupleType], "Argument to record update must be a tuple.")
        val tupleType = args(0).typ.asInstanceOf[TupleType]
        Utils.assert(tupleType.hasField(name), "Field '" + name + "' does not exist in tuple.")
      }
      def resultType(args: List[Expr]) : Type = args(0).typ
      override def fixity = PREFIX
    }
    // Expressions
    abstract class Expr(exprType: Type) {
      val typ = exprType
    }
    // Literals.
    abstract class Literal(exprType : Type) extends Expr (exprType)
    
    case class IntLit(value: BigInt) extends Literal (IntType.t) {
      override def toString = value.toString
    }
    
    case class BitVectorLit(value: BigInt, width: Int) extends Literal (BitVectorType.t(width)) {
      Utils.assert(value.bitCount + 1 <= width, "Value (" + value.toString + ") too big for BitVector of width " + width + " bits.")
      override def toString = "(_ bv" + value.toString + " " + width.toString +")"
    }
    
    case class BooleanLit(value: Boolean) extends Literal (BoolType.t) {
      override def toString = value.toString
    }
    
    case class Symbol(id: String, symbolTyp: Type) extends Expr (symbolTyp) {
      override def toString = id.toString
    }

    // Tuple creation.
    case class MakeTuple(args: List[Expr]) extends Expr (TupleType.t(args.map(_.typ))) {
      override def toString = "(mk-tuple " + Utils.join(args.map(_.toString), " ") + ")" 
    }
    
    
    case class OperatorApplication(op: Operator, operands: List[Expr]) extends Expr (op.resultType(operands)) {
      val fix = op.fixity
      Utils.assert(fix == INFIX || fix == PREFIX, "Unknown fixity.")
      Utils.assert(fix != INFIX || operands.size == 2, "Infix operators must have two operands.")
      op.typeCheck(operands)
      override def toString = {
        fix match {
          case INFIX => "(" + operands(0) + " " + op.toString + " " + operands(1) +  ")"
          case PREFIX => "(" + operands.foldLeft(op.toString){(acc, i) => acc + " " + i} + ")"
        }
      }
    }
    
    case class ArraySelectOperation(e: Expr, index: List[Expr]) 
      extends Expr (e.typ.asInstanceOf[ArrayType].outType) 
    {
      override def toString = "(" + e.toString + ")" + "[" + index.tail.fold(index.head.toString)
        { (acc,i) => acc + "," + i.toString } + "]"
    }
    case class ArrayStoreOperation(e: Expr, index: List[Expr], value: Expr) extends Expr(e.typ) 
    {
      override def toString = e.toString + "[" + index.tail.fold(index.head.toString)
        { (acc,i) => acc + "," + i.toString } + " := " + value.toString + "]"
    }
    
    //For uninterpreted function symbols or anonymous functions defined by Lambda expressions
    case class FunctionApplication(e: Expr, args: List[Expr]) 
      extends Expr (e.typ.asInstanceOf[MapType].outType) 
    {
      override def toString = e.toString + "(" + args.tail.fold(args.head.toString)
        { (acc,i) => acc + "," + i.toString } + ")"
    }
    case class ITE(e: Expr, t: Expr, f: Expr) extends Expr (t.typ) {
      override def toString = "ITE(" + e.toString + "," + t.toString + "," + f.toString + ")"
    }
    case class Lambda(ids: List[Symbol], e: Expr) extends Expr(MapType.t(ids.map(id => id.typ), e.typ)) {
      override def toString = "Lambda(" + ids + "). " + e.toString
    }
    
    abstract class SolverInterface {
      /** 
       *  Helper function that finds the list of all symbols (constants in SMT parlance) in an expression. 
       */
      def findSymbols(e : Expr, syms : Set[Symbol]) : Set[Symbol] = {
        e match {
          case Symbol(_,_) =>
            return syms + e.asInstanceOf[Symbol]
          case OperatorApplication(op,operands) =>
            return operands.foldLeft(syms)((acc,i) => findSymbols(i, acc))
          case ArraySelectOperation(e, index) =>
            return index.foldLeft(findSymbols(e, syms))((acc, i) => findSymbols(i, acc))
          case ArrayStoreOperation(e, index, value) =>
            return index.foldLeft(findSymbols(value, findSymbols(e, syms)))((acc,i) => findSymbols(i, acc))
          case FunctionApplication(e, args) =>
            return args.foldLeft(findSymbols(e, syms))((acc,i) => findSymbols(i, acc))
          case ITE(e,t,f) =>
            return findSymbols(e, syms) ++
              findSymbols(t, Set()) ++
              findSymbols(f, Set())
          case Lambda(_,_) =>
            throw new Exception("lambdas in assertions should have been beta-reduced")
          case IntLit(_) => return Set.empty[Symbol]
          case BitVectorLit(_,_) => return Set.empty[Symbol]
          case BooleanLit(_) => return Set.empty[Symbol]
        }
      }
      
      def findSymbols(e : Expr) : Set[Symbol] = { findSymbols(e, Set()) }
      
      // Assert 'e' in the solver. (Modifies solver context to contain 'e'.)
      def addConstraint(e : Expr)
      // Check whether 'e' is satisfiable in the current solver context.
      def check(e : Expr) : Option[Boolean]
    }
  }
}
