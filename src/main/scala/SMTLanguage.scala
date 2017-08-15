import scala.collection.mutable.Map

trait SMTType {
 def isBool = { false }
 def isInt = { false }
 def isBitVector = { false }
 def isMap = { false }
 def isArray = { false }
}

// The Boolean type.
case class SMTBoolType() extends SMTType { 
  override def toString = "bool" 
  override def equals(other: Any) = other.isInstanceOf[SMTBoolType]
  override def isBool = { true }
}
object SMTBoolType {
  val t = new SMTBoolType
}
// The integer type.
case class SMTIntType() extends SMTType { 
  override def toString = "int" 
  override def equals(other: Any) = other.isInstanceOf[SMTIntType]
  override def isInt = { true }
}
object SMTIntType {
  val t = new SMTIntType
}

// The bitvector type.
case class SMTBitVectorType(width: Int) extends SMTType
{
  override def toString = "bv" + (width.toString)
  override def equals(other: Any) = other match {
    case bvType : SMTBitVectorType => (bvType.width == width)
    case _                         => false
  }
  override def isBitVector = { true }
}
object SMTBitVectorType {
  var cache = scala.collection.mutable.Map[Int, SMTBitVectorType]()
  def t(width : Int) : SMTBitVectorType = {
    new SMTBitVectorType(width)
  }
}

case class SMTMapType(inTypes: List[SMTType], outType: SMTType) extends SMTType {
  override def toString = "map [" + inTypes.tail.fold(inTypes.head.toString)
  { (acc,i) => acc + "," + i.toString } + "] " + outType
  override def equals(other: Any) = other match {
      case that: SMTMapType =>
        if (that.inTypes.size == this.inTypes.size) {
          (that.outType == this.outType) && (that.inTypes zip this.inTypes).forall(i => i._1 == i._2)
        } else { false }
      case _ => false
    }
  override def isMap = { true }
}
object SMTMapType {
  def t(inTypes: List[SMTType], outType: SMTType) = {
    new SMTMapType(inTypes, outType)
  }
}
case class SMTArrayType(inTypes: List[SMTType], outType: SMTType) extends SMTType {
  override def toString = "array [" + inTypes.tail.fold(inTypes.head.toString)
  { (acc,i) => acc + "," + i.toString } + "] " + outType
  override def equals(other: Any) = other match {
      case that: SMTArrayType =>
        if (that.inTypes.size == this.inTypes.size) {
          (that.outType == this.outType) && (that.inTypes zip this.inTypes).forall(i => i._1 == i._2)
        } else { false }
      case _ => false
    }
  override def isArray = { true }
}

object SMTOperatorFixity extends scala.Enumeration {
  type SMTOperatorFixity = Value
  val INFIX, PREFIX = Value
}
import SMTOperatorFixity._

trait SMTOperator {
  def resultType(args: List[SMTExpr]) : SMTType
  def typeCheck (args: List[SMTExpr]) : Unit = { }
  def fixity : SMTOperatorFixity
  
  def checkNumArgs(args: List[SMTExpr], expectedNumOperands : Int) : Unit = {
    UclidUtils.assert(args.size == expectedNumOperands, "Operator '" + toString + "' requires " + expectedNumOperands + " operands.")
  }
  def checkAllArgTypes(args: List[SMTExpr], expectedType : SMTType) : Unit = {
    UclidUtils.assert(args.forall(op => op.typ == expectedType), "Operator '" + toString + "' requires operands of type: " + expectedType)
  }
  def checkAllArgsSameType(args: List[SMTExpr]) : Unit = {
    args match {
      case Nil => UclidUtils.assert(false, "Expected at least one operand for '" + toString + "' operator.")
      case head :: tail => UclidUtils.assert(args.forall(op => op.typ == head.typ), "Operands to '" + toString + "' must of the same type.")
    }
  }
}

// Operators that return integers.
abstract class SMTIntResultOperator extends SMTOperator {
  override def resultType(args: List[SMTExpr]) : SMTType = { SMTIntType.t }
  override def fixity = { PREFIX }
}
object SMTIntLTOperator extends SMTIntResultOperator { 
  override def toString = "<"
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTIntType.t) }
}
object SMTIntLEOperator extends SMTIntResultOperator { 
  override def toString = "<=" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTIntType.t) }
}
object SMTIntGTOperator extends SMTIntResultOperator { 
  override def toString = ">" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTIntType.t) }
}
object SMTIntGEOperator extends SMTIntResultOperator { 
  override def toString = ">=" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTIntType.t) }
}
object SMTIntAddOperator extends SMTIntResultOperator { 
  override def toString = "+" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTIntType.t) }
}
object SMTIntSubOperator extends SMTIntResultOperator { 
  override def toString = "-" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTIntType.t) }
}
object SMTIntMulOperator extends SMTIntResultOperator { 
  override def toString = "*" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTIntType.t) }
}

// Operators that return Booleans.
abstract class SMTBoolResultOperator extends SMTOperator {
  override def resultType(args: List[SMTExpr]) : SMTType = { SMTBoolType.t }
  override def fixity = { INFIX }
}

object SMTBoolIffOperator extends SMTBoolResultOperator { 
  override def toString = "<==>"
  override def typeCheck (args: List[SMTExpr]) = {
    UclidUtils.assert(args.size == 2, "Iff must have two operands.")
    UclidUtils.assert(args.forall(op => op.typ.isBool), "Iff operands must be boolean.")
  }
}
object SMTBoolImplicationOperator extends SMTBoolResultOperator { 
  override def toString  = "==>" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTBoolType.t) }
}
object SMTBoolConjunctionOperator extends SMTBoolResultOperator { 
  override def toString = "/\\" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTBoolType.t) }
}
object SMTBoolDisjunctionOperator extends SMTBoolResultOperator { 
  override def toString = "\\/" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTBoolType.t) }
}
object SMTBoolNegationOperator extends SMTBoolResultOperator { 
  override def toString = "!" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgTypes(args, SMTBoolType.t) }
}
object SMTBoolEqualityOperator extends SMTBoolResultOperator { 
  override def toString = "=" 
  override def typeCheck(args: List[SMTExpr]) : Unit = { checkNumArgs(args, 2); checkAllArgsSameType(args) }
}
abstract class SMTExpr(exprType: SMTType) {
  val typ = exprType
}

abstract class SMTLiteral(exprType : SMTType) extends SMTExpr (exprType)

case class SMTNumber(value: BigInt) extends SMTLiteral (SMTIntType.t) {
  override def toString = value.toString
}

case class SMTBitVector(value: BigInt, width: Int) extends SMTLiteral (SMTBitVectorType.t(width)) {
  UclidUtils.assert(value.bitCount + 1 <= width, "Value (" + value.toString + ") too big for BitVector of width " + width + " bits.")
  override def toString = value.toString + "bv" + width.toString //TODO: print in hex
}

case class SMTBoolean(value: Boolean) extends SMTLiteral (SMTBoolType.t) {
  override def toString = value.toString
}

case class SMTSymbol(id: String, symbolTyp: SMTType) extends SMTExpr (symbolTyp) {
  override def toString = id.toString
}

case class SMTOperatorApplication(op: SMTOperator, operands: List[SMTExpr]) extends SMTExpr (op.resultType(operands)) {
  val fix = op.fixity
  UclidUtils.assert(fix == INFIX || fix == PREFIX, "Unknown fixity.")
  UclidUtils.assert(fix != INFIX || operands.size == 2, "Infix operators musth have two operands.")
  op.typeCheck(operands)
  override def toString = {
    fix match {
      case INFIX => "(" + operands(0) + " " + op.toString + " " + operands(1) +  ")"
      case PREFIX => "(" + operands.foldLeft(op.toString){(acc, i) => acc + " " + i} + ")"
    }
  }
}

case class SMTArraySelectOperation(e: SMTExpr, index: List[SMTExpr]) 
  extends SMTExpr (e.typ.asInstanceOf[SMTArrayType].outType) 
{
  override def toString = "(" + e.toString + ")" + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i.toString } + "]"
}
case class SMTArrayStoreOperation(e: SMTExpr, index: List[SMTExpr], value: SMTExpr) extends SMTExpr(e.typ) 
{
  override def toString = e.toString + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i.toString } + " := " + value.toString + "]"
}

//For uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class SMTFuncApplication(e: SMTExpr, args: List[SMTExpr]) 
  extends SMTExpr (e.typ.asInstanceOf[SMTMapType].outType) 
{
  override def toString = e.toString + "(" + args.tail.fold(args.head.toString)
    { (acc,i) => acc + "," + i.toString } + ")"
}
case class SMTITE(e: SMTExpr, t: SMTExpr, f: SMTExpr) extends SMTExpr (t.typ) {
  override def toString = "ITE(" + e.toString + "," + t.toString + "," + f.toString + ")"
}
case class SMTLambda(ids: List[SMTSymbol], e: SMTExpr) extends SMTExpr(SMTMapType.t(ids.map(id => id.typ), e.typ)) {
  override def toString = "Lambda(" + ids + "). " + e.toString
}


