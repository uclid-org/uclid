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
     def isBool = { false }
     def isInt = { false }
     def isBitVector = { false }
     def isMap = { false }
     def isArray = { false }
    }
    
    // The Boolean type.
    case class BoolType() extends Type { 
      override def toString = "bool" 
      override def equals(other: Any) = other.isInstanceOf[BoolType]
      override def isBool = { true }
    }
    object BoolType {
      val t = new BoolType
    }
    // The integer type.
    case class IntType() extends Type { 
      override def toString = "int" 
      override def equals(other: Any) = other.isInstanceOf[IntType]
      override def isInt = { true }
    }
    object IntType {
      val t = new IntType
    }
    
    // The bitvector type.
    case class BitVectorType(width: Int) extends Type
    {
      override def toString = "bv" + (width.toString)
      override def equals(other: Any) = other match {
        case bvType : BitVectorType => (bvType.width == width)
        case _                         => false
      }
      override def isBitVector = { true }
    }
    object BitVectorType {
      var cache = scala.collection.mutable.Map[Int, BitVectorType]()
      def t(width : Int) : BitVectorType = {
        new BitVectorType(width)
      }
    }
    
    case class MapType(inTypes: List[Type], outType: Type) extends Type {
      override def toString = "map [" + inTypes.tail.fold(inTypes.head.toString)
      { (acc,i) => acc + "," + i.toString } + "] " + outType
      override def equals(other: Any) = other match {
          case that: MapType =>
            if (that.inTypes.size == this.inTypes.size) {
              (that.outType == this.outType) && (that.inTypes zip this.inTypes).forall(i => i._1 == i._2)
            } else { false }
          case _ => false
        }
      override def isMap = { true }
    }
    object MapType {
      def t(inTypes: List[Type], outType: Type) = {
        new MapType(inTypes, outType)
      }
    }
    case class ArrayType(inTypes: List[Type], outType: Type) extends Type {
      override def toString = "array [" + inTypes.tail.fold(inTypes.head.toString)
      { (acc,i) => acc + "," + i.toString } + "] " + outType
      override def equals(other: Any) = other match {
          case that: ArrayType =>
            if (that.inTypes.size == this.inTypes.size) {
              (that.outType == this.outType) && (that.inTypes zip this.inTypes).forall(i => i._1 == i._2)
            } else { false }
          case _ => false
        }
      override def isArray = { true }
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
        Utils.assert(args.size == expectedNumOperands, "Operator '" + toString + "' requires " + expectedNumOperands + " operands.")
      }
      def checkAllArgTypes(args: List[Expr], expectedType : Type) : Unit = {
        Utils.assert(args.forall(op => op.typ == expectedType), "Operator '" + toString + "' requires operands of type: " + expectedType)
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
    }
    object IntLTOp extends IntResultOp { 
      override def toString = "<"
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    object IntLEOp extends IntResultOp { 
      override def toString = "<=" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    object IntGTOp extends IntResultOp { 
      override def toString = ">" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    object IntGEOp extends IntResultOp { 
      override def toString = ">=" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    object IntAddOp extends IntResultOp { 
      override def toString = "+" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    object IntSubOp extends IntResultOp { 
      override def toString = "-" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    object IntMulOp extends IntResultOp { 
      override def toString = "*" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, IntType.t) }
    }
    
    // Operators that return Booleans.
    abstract class BoolResultOp extends Operator {
      override def resultType(args: List[Expr]) : Type = { BoolType.t }
      override def fixity = { INFIX }
    }
    
    object IffOp extends BoolResultOp { 
      override def toString = "<==>"
      override def typeCheck (args: List[Expr]) = {
        Utils.assert(args.size == 2, "Iff must have two operands.")
        Utils.assert(args.forall(op => op.typ.isBool), "Iff operands must be boolean.")
      }
    }
    object ImplicationOp extends BoolResultOp { 
      override def toString  = "==>" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BoolType.t) }
    }
    object ConjunctionOp extends BoolResultOp { 
      override def toString = "/\\" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BoolType.t) }
    }
    object DisjunctionOp extends BoolResultOp { 
      override def toString = "\\/" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BoolType.t) }
    }
    object NegationOp extends BoolResultOp { 
      override def toString = "!" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, BoolType.t) }
    }
    object EqualityOp extends BoolResultOp { 
      override def toString = "=" 
      override def typeCheck(args: List[Expr]) : Unit = { checkNumArgs(args, 2); checkAllArgsSameType(args) }
    }
    abstract class Expr(exprType: Type) {
      val typ = exprType
    }
    
    abstract class Literal(exprType : Type) extends Expr (exprType)
    
    case class IntLit(value: BigInt) extends Literal (IntType.t) {
      override def toString = value.toString
    }
    
    case class BitVectorLit(value: BigInt, width: Int) extends Literal (BitVectorType.t(width)) {
      Utils.assert(value.bitCount + 1 <= width, "Value (" + value.toString + ") too big for BitVector of width " + width + " bits.")
      override def toString = value.toString + "bv" + width.toString //TODO: print in hex
    }
    
    case class BooleanLit(value: Boolean) extends Literal (BoolType.t) {
      override def toString = value.toString
    }
    
    case class Symbol(id: String, symbolTyp: Type) extends Expr (symbolTyp) {
      override def toString = id.toString
    }
    
    case class OperatorApplication(op: Operator, operands: List[Expr]) extends Expr (op.resultType(operands)) {
      val fix = op.fixity
      Utils.assert(fix == INFIX || fix == PREFIX, "Unknown fixity.")
      Utils.assert(fix != INFIX || operands.size == 2, "Infix operators musth have two operands.")
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
    
  }
}
