import scala.util.parsing.combinator._
import scala.collection.immutable._
import java.nio.file.{Paths, Files}
import java.nio.charset.StandardCharsets
import scala.sys.process._

/**
 * Created by Rohit Sinha on 5/23/15.
 */
object UclidMain {
  case class UclidOptions(
      help : Boolean,
      mainModule: String,
      srcFiles: List[String]
  )
  
  def getOptions(args: Array[String]) : UclidOptions = {
    def isSwitch(s : String) = (s(0) == '-')
    var mainModule : String = "main"
    var srcFiles : List[String] = Nil
    var help = false
    var ignore = false;
   
    for (i <- args.indices) {
      if (ignore) {
        ignore = false
      } else if ( isSwitch(args(i)) ) {
        if (args(i) == "--main" || args(i) == "-m") {
          mainModule = args(i+1)
          ignore = true
        } else if (args(i) == "--help" || args(i) == "-h") {
          help = true;
        } else {
          println("Unknown argument: " + args(i))
          exit(1)
        }
      } else {
        srcFiles = args(i) :: srcFiles
      }
    }
    return UclidOptions(help, mainModule, srcFiles)
  }
  
  
  val usage = """
    Usage: UclidMain [options] filename [filenames]
    Options:
      -h/--help : This message.
      -m/--main : Set the main module.
  """
  def main(args: Array[String]) {
    if (args.length == 0) println(usage)
    val opts = getOptions(args)
    
    if (opts.help) {
      println(usage)
      exit(0)
    }
    
    process(opts.mainModule, opts.srcFiles)
  }
  
  def process(main : String, srcFiles : List[String]) : Unit = {
    type ModuleMap = Map[UclIdentifier, UclModule]
    type NameCountMap = Map[UclIdentifier, Int]
    var modules : ModuleMap = Map()
    var nameCnt : NameCountMap = Map().withDefaultValue(0)
    println("Main module: " + main)
    
    for (srcFile <- srcFiles) {
      println("Input File: " + srcFile)
      val text = scala.io.Source.fromFile(srcFile).mkString
      val fileModules = UclidParser.parseModel(text)
      for(module <- fileModules) {
        UclidSemanticAnalyzer.checkSemantics(module)
      }
      nameCnt = fileModules.foldLeft(nameCnt)((cnts : NameCountMap, m : UclModule) => (cnts + (m.id -> (cnts(m.id) + 1))))
      val repeatedNameCnt = nameCnt.filter{ case (name, cnt) => cnt > 1 }
      val repeatedNames = repeatedNameCnt.foldLeft(""){ case (str, (name, cnt)) => str + " " + name }
      UclidUtils.assert(repeatedNameCnt.size == 0, "Repeated module names: " + repeatedNames)
      modules = fileModules.foldLeft(modules)((ms: ModuleMap, m : UclModule) => ms + (m.id -> m)) 
    }
    println("Total number of modules is: " + modules.size)
      //Control module
      /*
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
       */
  }
}
