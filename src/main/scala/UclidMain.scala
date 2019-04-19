/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Authors: Rohit Sinha, Pramod Subramanyan
 *
 * Created by Rohit Sinha on 5/23/15.
 * With lots of updates by Pramod Subramanyan in the summer of 2017.
 *
 * UCLID main file.
 *
 */

package uclid

import scala.util.parsing.combinator._
import scala.collection.immutable._
import lang.{Identifier, Module,  _}
import uclid.Utils.ParserErrorList
import com.typesafe.scalalogging.Logger
import uclid.smt.SyGuSInterface
import uclid.smt.InterpolationTest

/** This is the main class for Uclid.
 *
 */
object UclidMain {
  val logger = Logger("uclid.UclidMain")

  def main(args: Array[String]) {
    parseOptions(args) match {
      case None =>
      case Some(config) => main(config)
    }
  }

  /** Command-line configuration flags for uclid5.
   *
   * @param mainModuleName The name of the main module.
   * @param smtSolver The location of an SMT solver executable along with arguments that must be passed to it.
   * @param files List of files that should parsed and analyzed.
   */
  case class Config(
      mainModuleName : String = "main",
      smtSolver: List[String] = List.empty,
      synthesizer: List[String] = List.empty,
      synthesisRunDir: String = "",
      smtFileGeneration: String = "",
      sygusFormat: Boolean = false,
      sygusTypeConvert: Boolean = false,
      enumToNumeric: Boolean = false,
      printStackTrace: Boolean = false,
      verbose : Int = 0,
      files : Seq[java.io.File] = Seq(),
      testFixedpoint: Boolean = false
  )

  def parseOptions(args: Array[String]) : Option[Config] = {
    val parser = new scopt.OptionParser[Config]("uclid") {
      head("uclid", "0.9.5")

      opt[String]('m', "main").valueName("<Module>").action{ 
        (x, c) => c.copy(mainModuleName = x) 
      }.text("Name of the main module.")

      opt[String]('s', "solver").valueName("<Cmd>").action{ 
        (exec, c) => c.copy(smtSolver = exec.split(" ").toList) 
      }.text("External SMT solver binary.")

      opt[String]('y', "synthesizer").valueName("<Cmd>").action{
        (exec, c) => c.copy(synthesizer = exec.split(" ").toList)
      }.text("Command line to invoke SyGuS synthesizer.")

      opt[String]('Y', "synthesizer-run-directory").valueName("<Dir>").action{
        (dir, c) => c.copy(synthesisRunDir = dir)
      }.text("Run directory for synthesizer.")

      opt[String]('g', "smt-file-generation").action{
        (prefix, c) => c.copy(smtFileGeneration = prefix)
      }.text("File prefix to generate smt files for each assertion.")

      opt[Unit]('X', "exception-stack-trace").action{
        (_, c) => c.copy(printStackTrace = true)
      }.text("Print exception stack trace.")

      opt[Unit]('f', "sygus-format").action{
        (_, c) => c.copy(sygusFormat = true)
      }.text("Generate the standard SyGuS format.")

      opt[Unit]('c', "sygus-type-convert").action{
        (_, c) => c.copy(sygusTypeConvert = true)
      }.text("Enable EnumType conversion in synthesis.")

      opt[Unit]('e', "enum-to-numeric").action{
        (_, c) => c.copy(enumToNumeric = true)
      }.text("Enable conversion from EnumType to NumericType.")

      opt[Unit]('t', "test-fixedpoint").action {
        (_, c) => c.copy(testFixedpoint = true)
      }.text("Test fixed point")

      arg[java.io.File]("<file> ...").unbounded().required().action {
        (x, c) => c.copy(files = c.files :+ x)
      }.text("List of files to analyze.")
      
      // override def renderingMode = scopt.RenderingMode.OneColumn
    }
    parser.parse(args, Config())
  }

  /** This version of 'main' does all the real work.
   */
  def main(config : Config) {
    try {
      if (config.testFixedpoint) {
        smt.FixedpointTest.test()
        return
      }
      val mainModuleName = Identifier(config.mainModuleName)
      val modules = compile(config.files, mainModuleName)
      val mainModule = instantiate(config, modules, mainModuleName, true)
      mainModule match {
        case Some(m) => execute(m, config)
        case None    =>
          throw new Utils.ParserError("Unable to find main module", None, None)
      }
      UclidMain.println("Finished execution for module: %s.".format(mainModuleName.toString))
    }
    catch  {
      case (e : java.io.FileNotFoundException) =>
        UclidMain.println("Error: " + e.getMessage() + ".")
        if(config.printStackTrace) { e.printStackTrace() }
        System.exit(1)
      case (p : Utils.ParserError) =>
        UclidMain.println("%s error %s: %s.\n%s".format(p.errorName, p.positionStr, p.getMessage, p.fullStr))
        if(config.printStackTrace) { p.printStackTrace() }
        System.exit(1)
      case (typeErrors : Utils.TypeErrorList) =>
        typeErrors.errors.foreach {
          (p) => {
            UclidMain.println("Type error at %s: %s.\n%s".format(p.positionStr, p.getMessage, p.fullStr))
          }
        }
        UclidMain.println("Parsing failed. %d errors found.".format(typeErrors.errors.size))
        if(config.printStackTrace) { typeErrors.printStackTrace() }
        System.exit(1)
      case (ps : Utils.ParserErrorList) =>
        ps.errors.foreach {
          (err) => {
            UclidMain.println("Error at " + err._2.toString + ": " + err._1 + ".\n" + err._2.pos.longString)
          }
        }
        UclidMain.println("Parsing failed. " + ps.errors.size.toString + " errors found.")
        if(config.printStackTrace) { ps.printStackTrace() }
        System.exit(1)
      case(a : Utils.AssertionError) =>
        UclidMain.println("[Assertion Failure]: " + a.getMessage)
        if(config.printStackTrace) { a.printStackTrace() }
        System.exit(2)
    }
  }

  def createCompilePassManager(test: Boolean, mainModuleName: lang.Identifier) = {
    val passManager = new PassManager("compile")
    // passManager.addPass(new ASTPrinter())
    passManager.addPass(new ModuleCanonicalizer())
    passManager.addPass(new LTLOperatorIntroducer())
    passManager.addPass(new ModuleTypesImportCollector())
    passManager.addPass(new ModuleConstantsImportCollector())
    passManager.addPass(new ModuleFunctionsImportCollector())
    passManager.addPass(new ExternalTypeAnalysis())
    passManager.addPass(new ExternalTypeRewriter())
    passManager.addPass(new FuncExprRewriter())
    passManager.addPass(new InstanceModuleNameChecker())
    passManager.addPass(new InstanceModuleTypeRewriter())
    passManager.addPass(new RewritePolymorphicSelect())
    passManager.addPass(new ConstantLitRewriter())
    passManager.addPass(new TypeSynonymFinder())
    passManager.addPass(new TypeSynonymRewriter())
    passManager.addPass(new BlockVariableRenamer())
    passManager.addPass(new BitVectorSliceFindWidth())
    passManager.addPass(new ExpressionTypeChecker())
    if (!test) passManager.addPass(new VerificationExpressionChecker())
    passManager.addPass(new PolymorphicTypeRewriter())
    passManager.addPass(new FindProcedureDependency())
    passManager.addPass(new DefDepGraphChecker())
    passManager.addPass(new RewriteDefines())
    passManager.addPass(new ModuleTypeChecker())
    passManager.addPass(new PrimedAssignmentChecker())
    passManager.addPass(new SemanticAnalyzer())
    passManager.addPass(new ProcedureChecker())
    passManager.addPass(new ControlCommandChecker())
    passManager.addPass(new ComputeInstanceTypes())
    passManager.addPass(new ModuleInstanceChecker())
    passManager.addPass(new WhileLoopRewriter())
    passManager.addPass(new ForLoopUnroller())
    passManager.addPass(new BitVectorSliceConstify())
    passManager.addPass(new CaseEliminator())
    passManager.addPass(new VariableDependencyFinder())
    passManager.addPass(new StatementScheduler())
    passManager.addPass(new BlockFlattener())
    passManager.addPass(new NewProcedureInliner())
    passManager.addPass(new PrimedVariableCollector())
    passManager.addPass(new PrimedVariableEliminator())
    passManager.addPass(new PrimedHistoryRewriter())
    passManager.addPass(new IntroduceFreshHavocs())
    passManager.addPass(new RewriteFreshLiterals())
    passManager.addPass(new BlockFlattener())
    passManager.addPass(new ModuleCleaner(mainModuleName))
    passManager.addPass(new BlockVariableRenamer())
    passManager
  }  
  /** Parse modules, typecheck them, inline procedures, create LTL monitors, etc. */
  def compile(srcFiles : Seq[java.io.File], mainModuleName : Identifier, test : Boolean = false): List[Module] = {
    type NameCountMap = Map[Identifier, Int]
    var nameCnt : NameCountMap = Map().withDefaultValue(0)
    val passManager = createCompilePassManager(test, mainModuleName)

    val filenameAdderPass = new AddFilenameRewriter(None)
    // Helper function to parse a single file.
    def parseFile(srcFile : String) : List[Module] = {
      val text = scala.io.Source.fromFile(srcFile).mkString
      filenameAdderPass.setFilename(srcFile)
      val modules = UclidParser.parseModel(srcFile, text)
      modules.map(m => filenameAdderPass.visit(m, Scope.empty)).flatten
    }
    val parsedModules = srcFiles.foldLeft(List.empty[Module]) {
      (acc, srcFile) => acc ++ parseFile(srcFile.getPath())
    }

    // now process each module
    val init = (List.empty[Module], Scope.empty)
    // NOTE: The foldLeft/:: combination here reverses the order of modules.
    // The PassManager in instantiate calls run(ms : List[Module]); this version of run uses foldRight.
    // So modules end up being processed in the same order in both PassManagers.
    val processedModules = parsedModules.foldLeft(init) {
      (acc, m) =>
        val modules = acc._1
        val context = acc._2
        val mP = passManager.run(m, context).get
        (mP :: modules, context +& mP)
    }._1
    val moduleNames = processedModules.map(m => (m.id, m.id.position)).reverse
    val errors = SemanticAnalyzerPass.checkIdRedeclaration(moduleNames, List.empty)
    if (errors.size > 0) {
      throw new ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
    processedModules
  }

  /** Instantiate module helper. */
  def instantiateModules(config : Config, moduleList: List[Module], mainModuleName : Identifier) : List[Module] = {
    val passManager = new PassManager("instantiate")
    passManager.addPass(new ModuleDependencyFinder(mainModuleName))
    passManager.addPass(new StatelessAxiomFinder(mainModuleName))
    passManager.addPass(new StatelessAxiomImporter(mainModuleName))
    // passManager.addPass(new ASTPrinter())
    passManager.addPass(new ExternalSymbolAnalysis())
    passManager.addPass(new ModuleFlattener(mainModuleName))
    passManager.addPass(new ModuleEliminator(mainModuleName))
    passManager.addPass(new LTLOperatorRewriter())
    passManager.addPass(new LTLPropertyRewriter())
    passManager.addPass(new Optimizer())
    passManager.addPass(new ModuleCleaner(mainModuleName))
    passManager.addPass(new Optimizer())
    passManager.addPass(new BlockVariableRenamer())
    passManager.addPass(new ExpressionTypeChecker())
    passManager.addPass(new ModuleTypeChecker())
    passManager.addPass(new SemanticAnalyzer())
    if (config.enumToNumeric) passManager.addPass(new EnumTypeAnalysis())
    if (config.enumToNumeric) passManager.addPass(new EnumTypeRenamer("BV"))
    if (config.enumToNumeric) passManager.addPass(new EnumTypeRenamerCons("BV"))

    // run passes.
    passManager.run(moduleList)
  }

  /** Instantiate modules.
   *
   * @param moduleList List of modules to be analyzed.
   * @param mainModuleName Name of main module.
   * @param verbose If this is true, we print the message describing the number of modules parsed and instantiated.
   */
  def instantiate(config : Config, moduleList : List[Module], mainModuleName : Identifier, verbose : Boolean) : Option[Module] = {
    if (moduleList.find(m => m.id == mainModuleName).isEmpty) {
      return None
    }
    val moduleListP = instantiateModules(config, moduleList, mainModuleName)
    if (verbose) {
      UclidMain.println("Successfully parsed %d and instantiated %d module(s).".format(moduleList.size, moduleListP.size))
    }
    // return main module.
    moduleListP.find((m) => m.id == mainModuleName)
  }

  /** Execute the control module.
   *
   */
  def execute(module : Module, config : Config) : List[CheckResult] = {
    var symbolicSimulator = new SymbolicSimulator(module)
    var solverInterface = if (config.smtSolver.size > 0) {
      logger.debug("args: {}", config.smtSolver)
      new smt.SMTLIB2Interface(config.smtSolver)
    } else {
      new smt.Z3Interface()
    }
    val sygusInterface : Option[smt.SynthesisContext] = config.synthesizer match {
      case Nil => None
      case lst => Some(new smt.SyGuSInterface(lst, config.synthesisRunDir, config.sygusFormat))
    }
    solverInterface.filePrefix = config.smtFileGeneration
    val result = symbolicSimulator.execute(solverInterface, sygusInterface, config)
    solverInterface.finish()
    return result
  }

  var stringOutput : StringBuilder = new StringBuilder()
  var stringOutputEnabled = false
  def enableStringOutput() {
    stringOutputEnabled = true
  }
  def clearStringOutput() {
    stringOutput.clear()
  }
  def println(str : String) {
    if (stringOutputEnabled) {
      stringOutput ++= str
      stringOutput ++= "\n"
    } else {
      Console.println(str)
    }
  }
}
