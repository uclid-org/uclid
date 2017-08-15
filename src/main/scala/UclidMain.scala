import scala.util.parsing.combinator._

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
    println(UclidSymbolicSimulator.simulate_steps(module,2))
  }
}