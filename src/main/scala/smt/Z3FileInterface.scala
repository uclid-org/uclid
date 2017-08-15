
/**
 * @author rohitsinha
 * @author pramod
 */
package uclid {
  package smt {
    import uclid.Utils
    import java.nio.file.{Paths, Files}
    import java.nio.charset.StandardCharsets
    import scala.sys.process._
    
    import scala.language.postfixOps

  
    object Z3FileInterface extends SolverInterface {
      def generateDeclaration(x: Symbol) : String = {
        def printType(t: Type) : String = {
          t match {
            case BoolType() => "Bool"
            case IntType() => "Int"
            case MapType(ins,out) =>
              "(" + ins.foldLeft(""){(acc,i) => 
                acc + " " + printType(i)} + ") " + printType(out)
            case ArrayType(ins,out) =>
              if (ins.size > 1) {
                "(Array " + ins.foldLeft("(MyTuple" + ins.size){(acc,i) => 
                  acc + " " + printType(i)} + ") " + printType(out) + ")"
              } else {
                "(Array " + printType(ins(0)) + " " + printType(out) + ")"
              }
          }
        }
        
        return x.typ match {
          case BoolType() => "(declare-const " + x.id + " " + printType(x.typ) + ")\n"
          case IntType() => "(declare-const " + x.id + " " + printType(x.typ) + ")\n"
          case MapType(ins,out) => 
            "(declare-fun " + x.id + " " + printType(x.typ) + ")\n"
          case ArrayType(ins,out) => 
            "(declare-const " + x.id + " " + printType(x.typ) + ")\n"
        }
      }
      
      def generateDatatypes(symbols: Set[Symbol]) : String = {
        var arrayArities : Set[Int] = Set.empty;
        symbols.foreach { x =>
          x.typ match {
            case MapType(ins,out) =>
              arrayArities = arrayArities ++ Set(ins.size)
            case ArrayType(ins,out) =>
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
      
      def translateExpr(e: Expr) : String = {
        
        def mkTuple(index: List[Expr]) : String = {
          if (index.size > 1) {
            "(mk-tuple" + index.size + index.foldLeft("")((acc,i) => 
              acc + " " + translateExpr(i)) + ")" 
          }
          else { 
            translateExpr(index(0)) 
          }
        }
        
        e match {
          case Symbol(id,_) => id
          case OperatorApplication(op,operands) => e.toString
          case ArraySelectOperation(e, index) =>
            "(select " + translateExpr(e) + " " + mkTuple(index) + ")"
          case ArrayStoreOperation(e, index, value) =>
            "(store " + translateExpr(e) + " " + mkTuple(index) + " " + translateExpr(value) + ")"
          case FunctionApplication(e, args) =>
            Utils.assert(e.isInstanceOf[Symbol], "Did beta sub happen?")
            "(" + translateExpr(e) +
              args.foldLeft(""){(acc,i) => 
                acc + " " + translateExpr(i)} + ")"
          case ITE(e,t,f) =>
            "(ite " + translateExpr(e) + " " +
              translateExpr(t) + " " +
              translateExpr(f) +")"
          case Lambda(_,_) =>
            throw new Exception("yo lambdas in assertions should have been beta-reduced")
          case IntLit(value) => value.toString()
          case BitVectorLit(_,_) =>
            throw new Utils.UnimplementedException("Bitvectors unimplemented")
          case BooleanLit(value) => 
            value match { case true => "true"; case false => "false" }
        }
      }
      
      override def check(e : Expr) : Option[Boolean] = {
        println("*************** Formula Start ***************")
        println("Asserting: " + e)
        val symbols: Set[Symbol] = findSymbols(e);
        val decl = symbols.foldLeft(""){(acc,x) => acc + generateDeclaration(x)}
        val datatypes = generateDatatypes(symbols)
        val assertion = "(assert (not " + translateExpr(e) + "))\n"
        val formula = datatypes + decl + assertion + "(check-sat)\n"
        def getCurrentDirectory = new java.io.File( "." ).getCanonicalPath

        Files.write(Paths.get(getCurrentDirectory + "/tmp.z3"), formula.getBytes(StandardCharsets.UTF_8))
        val z3_output = ("z3 " + getCurrentDirectory + "/tmp.z3 -smt2" !!).trim
        println("z3 says: " + z3_output)
        println("*************** Formula End ***************")
        
        return z3_output match {
          case "sat" => Some(true)
          case "unsat" => Some(false)
          case _ => None
        }
      }
    }
}
}