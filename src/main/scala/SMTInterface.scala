
/**
 * @author rohitsinha
 */
object SMTInterface {
  def generateDeclaration(x: SMTSymbol) : String = {
    def printType(t: SMTType) : String = {
      t match {
        case SMTBoolType() => "Bool"
        case SMTIntType() => "Int"
        case SMTMapType(ins,out) =>
          "(" + ins.foldLeft(""){(acc,i) => 
            acc + " " + printType(i)} + ") " + printType(out)
        case SMTArrayType(ins,out) =>
          if (ins.size > 1) {
            "(Array " + ins.foldLeft("(MyTuple" + ins.size){(acc,i) => 
              acc + " " + printType(i)} + ") " + printType(out) + ")"
          } else {
            "(Array " + printType(ins(0)) + " " + printType(out) + ")"
          }
      }
    }
    
    return x.typ match {
      case SMTBoolType() => "(declare-const " + x.id + " " + printType(x.typ) + ")\n"
      case SMTIntType() => "(declare-const " + x.id + " " + printType(x.typ) + ")\n"
      case SMTMapType(ins,out) => 
        "(declare-fun " + x.id + " " + printType(x.typ) + ")\n"
      case SMTArrayType(ins,out) => 
        "(declare-const " + x.id + " " + printType(x.typ) + ")\n"
    }
  }
  
  def generateDatatypes(symbols: Set[SMTSymbol]) : String = {
    var arrayArities : Set[Int] = Set.empty;
    symbols.foreach { x =>
      x.typ match {
        case SMTMapType(ins,out) =>
          arrayArities = arrayArities ++ Set(ins.size)
        case SMTArrayType(ins,out) =>
          arrayArities = arrayArities ++ Set(ins.size)
        case _ => ()
      }
    }

    return arrayArities.foldLeft(""){ (acc,x) => 
      acc + "(declare-datatypes " +
        "(" + ((1 to x).toList).foldLeft("") {
          (acc,i) => acc + " " + "T"+i } + ")" +
        "((MyTuple" + x + " (mk-tuple" + x + 
        ((1 to x).toList).foldLeft("") { 
            (acc,i) => acc + " (elem"+i+" T"+i+")" } + 
        "))))\n"
    }
  }
  
  def translateExpr(e: SMTExpr) : String = {
    def translateOp(op: SMTOperator) : String = {
      op match {
        case SMTIntLTOperator() => "<"
        case SMTIntLEOperator() => "<="
        case SMTIntGTOperator() => ">"
        case SMTIntGEOperator() => ">="
        case SMTIntAddOperator() => "+"
        case SMTIntSubOperator() => "-"
        case SMTIntMulOperator() => "*"
      }
    }
    
    def mkTuple(index: List[SMTExpr]) : String = {
      if (index.size > 1) {
        "(mk-tuple" + index.size + index.foldLeft("")((acc,i) => 
          acc + " " + translateExpr(i)) + ")" 
      }
      else { 
        translateExpr(index(0)) 
      }
    }
    
    e match {
      case SMTSymbol(id,_) => id
      case SMTBiImplication(l,r) => 
        "(= " + translateExpr(l) + " " + translateExpr(r) + ")"
      case SMTImplication(l,r) => 
        "(=> " + translateExpr(l) + " " + translateExpr(r) + ")"
      case SMTConjunction(l,r) => 
        "(and " + translateExpr(l) + " " + translateExpr(r) + ")"
      case SMTDisjunction(l,r) => 
        "(or " + translateExpr(l) + " " + translateExpr(r) + ")"
      case SMTNegation(expr) =>
        "(not " + translateExpr(expr) + ")"
      case SMTEquality(l,r) =>
        "(= " + translateExpr(l) + " " + translateExpr(r) + ")"
      case SMTIFuncApplication(op,operands) =>
        "(" + translateOp(op) +
          operands.foldLeft(""){(acc,i) => 
            acc + " " + translateExpr(i)} + ")"
      case SMTArraySelectOperation(e, index) =>
        "(select " + translateExpr(e) + " " + mkTuple(index) + ")"
      case SMTArrayStoreOperation(e, index, value) =>
        "(store " + translateExpr(e) + " " + mkTuple(index) + " " + translateExpr(value) + ")"
      case SMTFuncApplication(e, args) =>
        UclidUtils.assert(e.isInstanceOf[SMTSymbol], "Did beta sub happen?")
        "(" + translateExpr(e) +
          args.foldLeft(""){(acc,i) => 
            acc + " " + translateExpr(i)} + ")"
      case SMTITE(e,t,f) =>
        "(ite " + translateExpr(e) + " " +
          translateExpr(t) + " " +
          translateExpr(f) +")"
      case SMTLambda(_,_) =>
        throw new Exception("yo lambdas in assertions should have been beta-reduced")
      case SMTNumber(value) => value.toString()
      case SMTBitVector(_,_) =>
        throw new UclidUtils.UnimplementedException("Bitvectors unimplemented")
      case SMTBoolean(value) => 
        value match { case true => "true"; case false => "false" }
    }
  }
  
  def checkFormulaZ3(e : SMTExpr) : String = {
    println("Asserting: " + e)
    val symbols: Set[SMTSymbol] = findSymbolicVariables(e);
    val decl = symbols.foldLeft(""){(acc,x) => acc + generateDeclaration(x)}
    val datatypes = generateDatatypes(symbols)
    val formula = "(assert (not " + translateExpr(e) + "))\n"
    return datatypes + decl + formula + "(check-sat)\n"
  }
  
  def findSymbolicVariables(es: List[SMTExpr]) : Set[SMTSymbol] = {
    es.foldLeft(Set.empty[SMTSymbol])((acc,i) => acc ++ findSymbolicVariables(i))
  }
  
  def findSymbolicVariables(e : SMTExpr) : Set[SMTSymbol] = {
    e match {
      case SMTSymbol(_,_) =>
        return Set(e.asInstanceOf[SMTSymbol])
      case SMTBiImplication(l,r) => 
        return findSymbolicVariables(l) ++ findSymbolicVariables(r)
      case SMTImplication(l,r) => 
        return findSymbolicVariables(l) ++ findSymbolicVariables(r)
      case SMTConjunction(l,r) => 
        return findSymbolicVariables(l) ++ findSymbolicVariables(r)
      case SMTDisjunction(l,r) => 
        return findSymbolicVariables(l) ++ findSymbolicVariables(r)
      case SMTNegation(expr) =>
        return findSymbolicVariables(expr)
      case SMTEquality(l,r) =>
        return findSymbolicVariables(l) ++ findSymbolicVariables(r)
      case SMTIFuncApplication(op,operands) =>
        return findSymbolicVariables(operands)
      case SMTArraySelectOperation(e, index) =>
        return findSymbolicVariables(e) ++ findSymbolicVariables(index)
      case SMTArrayStoreOperation(e, index, value) =>
        return findSymbolicVariables(e) ++ 
          findSymbolicVariables(index) ++ 
          findSymbolicVariables(value)
      case SMTFuncApplication(e, args) =>
        return findSymbolicVariables(e) ++ findSymbolicVariables(args)
      case SMTITE(e,t,f) =>
        return findSymbolicVariables(e) ++
          findSymbolicVariables(t) ++
          findSymbolicVariables(f)
      case SMTLambda(_,_) =>
        throw new Exception("lambdas in assertions should have been beta-reduced")
      case SMTNumber(_) => return Set.empty[SMTSymbol]
      case SMTBitVector(_,_) => return Set.empty[SMTSymbol]
      case SMTBoolean(_) => return Set.empty[SMTSymbol]
    }
  }
}