import scala.util.parsing.combinator._
import java.nio.file.{Paths, Files}
import java.nio.charset.StandardCharsets
import scala.sys.process._

/**
 * Created by Rohit Sinha on 5/23/15.
 */
object UclidMain {
  def main(args: Array[String]) : Unit = {
    println("Input File: " + args(0))
    val input = scala.io.Source.fromFile(args(0)).mkString
    val module = UclidParser.parseModule(input)
    println("Parse Result: " + module)
    UclidSemanticAnalyzer.checkSemantics(module)
    println("Semantic Checking Succeeded")
    //Control module
    val asserts = UclidSymbolicSimulator.simulate_steps(module,2)._2 //simulate for 2 steps
    def getCurrentDirectory = new java.io.File( "." ).getCanonicalPath
    asserts.foreach { x => 
      println("*************** Formula Start ***************")
      var fmla : String = SMTInterface.checkFormulaZ3(x)
      println(fmla)
      Files.write(Paths.get(getCurrentDirectory + "/tmp.z3"), fmla.getBytes(StandardCharsets.UTF_8))
      //Process("z3 " + getCurrentDirectory + "/tmp.z3 -smt2")
      val z3_output = "z3 " + getCurrentDirectory + "/tmp.z3 -smt2" !!;
      println("Z3 says: " + z3_output)
      println("*************** Formula End ***************")
      }
    
  }
}
