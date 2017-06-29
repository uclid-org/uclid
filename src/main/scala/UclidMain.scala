package uclid {
  import scala.util.parsing.combinator._
  import scala.collection.immutable._
  import uclid.lang._
  import lang.UclidSemanticAnalyzer
  import lang.Module
  import lang.Identifier
  
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
            sys.exit(1)
          }
        } else {
          srcFiles = args(i) :: srcFiles
        }
      }
      return UclidOptions(help, mainModule, srcFiles)
    }
    
    type ModuleMap = Map[Identifier, Module]
  
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
        sys.exit(0)
      }
      val modules = compile(opts.srcFiles)
      val mainModuleName = Identifier(opts.mainModule)
      Utils.assert(modules.contains(mainModuleName), "Main module (" + opts.mainModule + ") does not exist.")
      val mainModule = modules.get(mainModuleName)
      mainModule match {
        case Some(m) => execute(m)
        case None    => 
      }
    }
    
    def compile(srcFiles : List[String]) : ModuleMap = {
      type NameCountMap = Map[Identifier, Int]
      var modules : ModuleMap = Map()
      var nameCnt : NameCountMap = Map().withDefaultValue(0)
      
      for (srcFile <- srcFiles) {
        println("Input File: " + srcFile)
        val text = scala.io.Source.fromFile(srcFile).mkString
        val fileModules = UclidParser.parseModel(text).map(Typechecker.checkAndRewrite(_))
        for(module <- fileModules) {
          UclidSemanticAnalyzer.checkSemantics(module)
        }
        nameCnt = fileModules.foldLeft(nameCnt)((cnts : NameCountMap, m : Module) => (cnts + (m.id -> (cnts(m.id) + 1))))
        val repeatedNameCnt = nameCnt.filter{ case (name, cnt) => cnt > 1 }
        val repeatedNames = repeatedNameCnt.foldLeft(""){ case (str, (name, cnt)) => str + " " + name }
        Utils.assert(repeatedNameCnt.size == 0, "Repeated module names: " + repeatedNames)
        modules = fileModules.foldLeft(modules)((ms: ModuleMap, m : Module) => ms + (m.id -> m)) 
      }
      println("Total number of modules is: " + modules.size)
      return modules
    }
    
    def execute(module : Module) {
      //Control module
      println("Found main module: " + module.id)
      println(module.toString)
      val asserts = UclidSymbolicSimulator.simulate_steps(module,2)._2 //simulate for 2 steps
      var z3Interface = smt.Z3Interface.newInterface()
      asserts.foreach { x => 
        val assert = smt.OperatorApplication(smt.NegationOp, List(x))
        var result = smt.Z3FileInterface.check(assert)
        var result2 = z3Interface.check(assert)
        println("results = " + result + "/" + result2)
        Utils.assert(result == result2, "Z3FileInterface and Z3Interface are producing differing results.")
        result match {
          case Some(false) => println("Assertion HOLDS.")
          case Some(true)  => println("Assertion FAILED.")
          case None        => println("Assertion INDETERMINATE.")
        }
      }
      //smt.SMTTester.testInts()
    }
  }
}
