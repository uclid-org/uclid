import scala.util.parsing.combinator._

/**
 * Created by Rohit Sinha on 5/23/15.
 */
object UclidMain {
  def main(args: Array[String]) : Unit = {
    println("Input File: " + args(0))
    val input = scala.io.Source.fromFile(args(0)).mkString
    println("result: " + UclidParser.parseProc(input))
  }
}