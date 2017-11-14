/*
 * UCLID5 Verification and Synthesis Engine
 * 
 * Copyright (c) 2017. The Regents of the University of California (Regents). 
 * All Rights Reserved. 
 * 
 * Permission to use, copy, modify, and distribute this software
 * and its documentation for educational, research, and not-for-profit purposes,
 * without fee and without a signed licensing agreement, is hereby granted,
 * provided that the above copyright notice, this paragraph and the following two
 * paragraphs appear in all copies, modifications, and distributions. 
 * 
 * Contact The Office of Technology Licensing, UC Berkeley, 2150 Shattuck Avenue,
 * Suite 510, Berkeley, CA 94720-1620, (510) 643-7201, otl@berkeley.edu,
 * http://ipira.berkeley.edu/industry-info for commercial licensing opportunities.
 * 
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
 * INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING OUT OF
 * THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS
 * PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 * 
 * Authors: Rohit Sinha, Pramod Subramanyan

 * UCLID main file.
 *
 */

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
      val mainModule = instantiate(modules, mainModuleName)
      mainModule match {
        case Some(m) => execute(m)
        case None    => throw new Utils.ParserError("Unable to find main module: " + mainModule.toString, None, None)
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
        println("Error " + filenameStr + positionStr + ": " + p.getMessage + "\n" + fullStr)
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
  
  def compile(srcFiles : List[String]) : List[Module] = {
    type NameCountMap = Map[Identifier, Int]
    var nameCnt : NameCountMap = Map().withDefaultValue(0)
    
    val passManager = new PassManager()
    // for certain unfortunate reasons we need to unroll for-loops before type checking.
    // passManager.addPass(new ASTPrinter("ASTPrinter$1"))
    val filenameAdderPass = new AddFilenameRewriter(None) 
    passManager.addPass(filenameAdderPass)
    passManager.addPass(new ForLoopIndexRewriter())
    passManager.addPass(new TypeSynonymFinder())
    passManager.addPass(new TypeSynonymRewriter())
    passManager.addPass(new BitVectorSliceFindWidth())
    passManager.addPass(new ExpressionTypeChecker())
    passManager.addPass(new PolymorphicTypeRewriter())
    passManager.addPass(new ModuleTypeChecker())
    passManager.addPass(new SemanticAnalyzer())
    passManager.addPass(new ComputeInstanceTypes())
    passManager.addPass(new ProcedureInliner())
    passManager.addPass(new ForLoopUnroller())
    passManager.addPass(new BitVectorSliceConstify())
    passManager.addPass(new CaseEliminator())
    passManager.addPass(new ControlCommandChecker())
    // passManager.addPass(new ASTPrinter("ASTPrinter$2"))

    def parseFile(srcFile : String) : List[Module] = {
      val text = scala.io.Source.fromFile(srcFile).mkString
      filenameAdderPass.setFilename(srcFile)
      UclidParser.parseModel(srcFile, text).map(passManager.run(_).get)
    }
    
    val modules = srcFiles.foldLeft(List.empty[Module]) {
      (acc, srcFile) => acc ++ parseFile(srcFile) 
    }
    val modIdSeq = modules.map(m => (m.id, m.position))
    val moduleErrors = SemanticAnalyzerPass.checkIdRedeclaration(modIdSeq, List.empty[ModuleError])
    if (moduleErrors.size > 0) {
      val errors = moduleErrors.map((me) => (me.msg, me.position))
      throw new Utils.ParserErrorList(errors)
    }
    
    return modules
  }
  
  def instantiate(moduleList : List[Module], mainModuleName : Identifier) : Option[Module] = {
    // create pass manager.
    val passManager = new PassManager()
    // passManager.addPass(new ASTPrinter("ASTPrinter$3"))
    passManager.addPass(new ModuleInstanceChecker(moduleList))
    passManager.addPass(new ModuleDependencyFinder(moduleList, mainModuleName))
    passManager.addPass(new ModuleFlattener(moduleList, mainModuleName))
    passManager.addPass(new ModuleEliminator(mainModuleName))
    // passManager.addPass(new ModuleCleaner())
    passManager.addPass(new ExpressionTypeChecker())
    passManager.addPass(new ModuleTypeChecker())
    // passManager.addPass(new ASTPrinter("ASTPrinter$4"))
    // passManager.addPass(new SemanticAnalyzer())

    // run passes.
    val moduleListP = passManager.run(moduleList)
    
    // return main module.
    moduleListP.find((m) => m.id == mainModuleName)
  }

  def execute(module : Module) : List[CheckResult] = {
    // execute the control module
    var symbolicSimulator = new SymbolicSimulator(module)
    var z3Interface = smt.Z3Interface.newInterface()
    return symbolicSimulator.execute(z3Interface)
  }
}
