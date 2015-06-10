abstract class SMTOperator
case class SMTIntLTOperator() extends SMTOperator { override def toString = "<" }
case class SMTIntLEOperator() extends SMTOperator { override def toString = "<=" }
case class SMTIntGTOperator() extends SMTOperator { override def toString = ">" }
case class SMTIntGEOperator() extends SMTOperator { override def toString = ">=" }
case class SMTIntAddOperator() extends SMTOperator { override def toString = "+" }
case class SMTIntSubOperator() extends SMTOperator { override def toString = "-" }
case class SMTIntMulOperator() extends SMTOperator { override def toString = "*" }

abstract class SMTExpr
abstract class SMTLiteral extends SMTExpr
case class SMTNumber(value: BigInt) extends SMTLiteral {
  override def toString = value.toString
}
//TODO: check that value can be expressed using "width" bits
case class SMTBitVector(value: BigInt, width: BigInt) extends SMTLiteral {
  override def toString = value.toString + "bv" + width.toString //TODO: print in hex
}
case class SMTBoolean(value: Boolean) extends SMTLiteral {
  override def toString = value.toString
}
case class SMTSymbol(id: String, typ: SMTType) extends SMTExpr {
  override def toString = "(" + id.toString + "," + typ.toString + ")"
}
case class SMTBiImplication(left: SMTExpr, right: SMTExpr) extends SMTExpr {
  override def toString = "(" + left.toString + " <==> " + right.toString + ")"
}
case class SMTImplication(left: SMTExpr, right: SMTExpr) extends SMTExpr {
  override def toString = "(" + left.toString + " ==> " + right.toString + ")"
}
case class SMTConjunction(left: SMTExpr, right: SMTExpr) extends SMTExpr {
  override def toString = "(" + left.toString + " /\\ " + right.toString + ")"
}
case class SMTDisjunction(left: SMTExpr, right: SMTExpr) extends SMTExpr {
  override def toString = "(" + left.toString + " \\/ " + right.toString + ")"
}
case class SMTNegation(expr: SMTExpr) extends SMTExpr {
  override def toString = "! " + expr.toString
}
case class SMTEquality(left: SMTExpr, right: SMTExpr) extends SMTExpr {
  override def toString = "(" + left.toString + " = " + right.toString + ")"
}
//for symbols interpreted by underlying Theory solvers
case class SMTIFuncApplication(op: SMTOperator, operands: List[SMTExpr]) extends SMTExpr {
  override def toString = op + "(" + operands.foldLeft(""){(acc,i) => acc + "," + i} + ")"
}
case class SMTArraySelectOperation(e: SMTExpr, index: List[SMTExpr]) extends SMTExpr {
  override def toString = e.toString + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i.toString } + "]"
}
case class SMTArrayStoreOperation(e: SMTExpr, index: List[SMTExpr], value: SMTExpr) extends SMTExpr {
  override def toString = e.toString + "[" + index.tail.fold(index.head.toString)
    { (acc,i) => acc + "," + i.toString } + "]" + " := " + value.toString
}
//for uninterpreted function symbols or anonymous functions defined by Lambda expressions
case class SMTFuncApplication(e: SMTExpr, args: List[SMTExpr]) extends SMTExpr {
  override def toString = e.toString + "(" + args.tail.fold(args.head.toString)
    { (acc,i) => acc + "," + i.toString } + ")"
}
case class SMTITE(e: SMTExpr, t: SMTExpr, f: SMTExpr) extends SMTExpr {
  override def toString = "ITE(" + e.toString + "," + t.toString + "," + f.toString + ")"
}
case class SMTLambda(ids: List[SMTSymbol], e: SMTExpr) extends SMTExpr {
  override def toString = "Lambda(" + ids + "). " + e.toString
}

abstract class SMTType
case class SMTBoolType() extends SMTType { 
  override def toString = "bool" 
  override def equals(other: Any) = other.isInstanceOf[SMTBoolType]
}
case class SMTIntType() extends SMTType { 
  override def toString = "int" 
  override def equals(other: Any) = other.isInstanceOf[SMTIntType]  
}

//class SMTBitvectorType extends SMTType
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
}
