package uclid

import scala.util.parsing.combinator._
import scala.collection.immutable._
import uclid.lang._
import lang.Module
import lang.Identifier

/**
 * Created by Rohit Sinha on 5/23/15.
 * With lots of updates by Pramod Subramanyan in the summer of 2017.
 */
object UclidMain {
  object options {
      var help : Boolean = false
      var mainModule: String = "main"
      var srcFiles: List[String] = Nil
      var debugOptions : Set[String] = Set.empty[String]
  }
  
  def getOptions(args: Array[String]) {
    def isSwitch(s : String) = (s(0) == '-')
    var ignore = false
   
    for (i <- args.indices) {
      if (ignore) {
        ignore = false
      } else if ( isSwitch(args(i)) ) {
        if (args(i) == "--main" || args(i) == "-m") {
          if (i+1 < args.length) {
            options.mainModule = args(i+1)
            ignore = true
          } else {
            println("Expected name of main module after switch '" + args(i) + "'")
            options.help = true;
          }
        } else if (args(i) == "--debug" || args(i) == "-d") {
          if (i+1 < args.length) {
            options.debugOptions = args(i+1).split("+").toSet
            ignore = true
          } else {
            println("Expected list of debug modules after switch '" + args(i) + "'")
            options.help = true;
          }
        } else if (args(i) == "--help" || args(i) == "-h") {
          options.help = true;
        } else {
          println("Unknown argument: " + args(i))
          println(usage)
          sys.exit(1)
        }
      } else {
        options.srcFiles = args(i) :: options.srcFiles
      }
    }
  }
  
  type ModuleMap = Map[Identifier, Module]

  val usage = """
    Usage: UclidMain [options] filename [filenames]
    Options:
      -h/--help : This message.
      -m/--main : Set the main module.
      -d/--debug : Debug options.
  """
  def main(args: Array[String]) {
    if (args.length == 0) println(usage)
    val opts = getOptions(args)
    
    if (options.help) {
      println(usage)
      sys.exit(1)
    }
    try { 
      val modules = compile(options.srcFiles)
      val mainModuleName = Identifier(options.mainModule)
      Utils.assert(modules.contains(mainModuleName), "Main module (" + options.mainModule + ") does not exist.")
      val mainModule = modules.get(mainModuleName)
      mainModule match {
        case Some(m) => execute(m)
        case None    => 
      }
    }
    catch  {
      case (p : Utils.ParserError) =>
        val filenameStr = p.filename match {
          case Some(f) => f + ", "
          case None => ""
        }
        val positionStr = p.pos match {
          case Some(pos) => "line " + pos.line.toString
          case None => ""
        }
        val fullStr = p.pos match {
          case Some(pos) => pos.longString
          case None => ""
        }
        println("Error at " + filenameStr + positionStr + ": " + p.getMessage + "\n" + fullStr)
        System.exit(1)
      case (typeErrors : Utils.TypeErrorList) =>
        typeErrors.errors.foreach {
          (err) => {
            println("Type error at " + err.pos.get.toString + ": " + err.getMessage() + "\n" + err.pos.get.longString)
          }
        }
      case (ps : Utils.ParserErrorList) =>
        ps.errors.foreach {
          (err) => {
            println("Error at " + err._2.toString + ": " + err._1 + "\n" + err._2.pos.longString) 
          }
        }
        println("Parsing failed. " + ps.errors.size.toString + " errors found.")
      case(a : Utils.AssertionError) =>
        println("[Assertion Failure]: " + a.getMessage)
        a.printStackTrace()
        System.exit(2)
    }
  }
  
  def compile(srcFiles : List[String]) : ModuleMap = {
    type NameCountMap = Map[Identifier, Int]
    var modules : ModuleMap = Map()
    var nameCnt : NameCountMap = Map().withDefaultValue(0)
    
    val passManager = new PassManager()
    // for certain unfortunate reasons we need to unroll for loops before type checking.
    // passManager.addPass(new ASTPrinter("ASTPrinter$1"))
    val filenameAdderPass = new AddFilenameRewriter(None) 
    passManager.addPass(filenameAdderPass)
    passManager.addPass(new ForLoopIndexRewriter())
    passManager.addPass(new TypeSynonymFinder())
    passManager.addPass(new TypeSynonymRewriter())
    passManager.addPass(new BitVectorSliceFindWidth())
    passManager.addPass(new ExpressionTypeChecker())
    passManager.addPass(new PolymorphicTypeRewriter())
    passManager.addPass(new ASTPrinter("ASTPrinter$1"))
    passManager.addPass(new ModuleTypeChecker())
    passManager.addPass(new SemanticAnalyzer())
    passManager.addPass(new FunctionInliner())
    passManager.addPass(new ForLoopUnroller())
    passManager.addPass(new BitVectorSliceConstify())
    passManager.addPass(new CaseEliminator())
    passManager.addPass(new ControlCommandChecker())
    // passManager.addPass(new ASTPrinter("ASTPrinter$2"))

    for (srcFile <- srcFiles) {
      val text = scala.io.Source.fromFile(srcFile).mkString
      filenameAdderPass.setFilename(srcFile)
      val fileModules = UclidParser.parseModel(srcFile, text).map(passManager.run(_).get)
      nameCnt = fileModules.foldLeft(nameCnt)((cnts : NameCountMap, m : Module) => (cnts + (m.id -> (cnts(m.id) + 1))))
      val repeatedNameCnt = nameCnt.filter{ case (name, cnt) => cnt > 1 }
      val repeatedNames = Utils.join(repeatedNameCnt.map((r) => r._1.toString).toList, ", ")
      Utils.checkError(repeatedNameCnt.size == 0, "Repeated module names: " + repeatedNames)
      modules = fileModules.foldLeft(modules)((ms: ModuleMap, m : Module) => ms + (m.id -> m)) 
    }
    return modules
  }

  def execute(module : Module) : List[CheckResult] = {
    // execute the control module
    var symbolicSimulator = new SymbolicSimulator(module)
    var z3Interface = smt.Z3Interface.newInterface()
    return symbolicSimulator.execute(z3Interface)
  }

}
