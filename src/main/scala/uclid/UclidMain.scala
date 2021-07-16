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

/** This is the main class for Uclid.
 *
 */
object UclidMain {
  val logger = Logger("uclid.UclidMain")

  var mainVerbosity: Int = 1;

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
      smtFileGeneration: String = "",
      sygusFormat: Boolean = true,
      enumToNumeric: Boolean = false,
      modSetAnalysis: Boolean = false,
      ufToArray: Boolean = false,
      printStackTrace: Boolean = false,
      verbose : Int = 1, // verbosities: 
      // 0: essential: print nothing but results and error messages
      // 1: basic: current default behaviour, includes statuses
      // 2: stats: includes statistics on time/which properties are being solved
      // 3: print everything
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
      }.text("Command line to invoke external SMT solver binary.")

      opt[String]('y', "synthesizer").valueName("<Cmd>").action{
        (exec, c) => c.copy(synthesizer = exec.split(" ").toList)
      }.text("Command line to invoke SyGuS synthesizer.")

      opt[String]('g', "smt-file-generation").action{
        (prefix, c) => c.copy(smtFileGeneration = prefix)
      }.text("File prefix to generate smt files for each assertion.")

      opt[Unit]('X', "exception-stack-trace").action{
        (_, c) => c.copy(printStackTrace = true)
      }.text("Print exception stack trace.")

      opt[Unit]('f', "sygus-format").action{
        (_, c) => c.copy(sygusFormat = true)
      }.text("(deprecated, enabled by default) Generate the standard SyGuS format.")

      opt[Unit]('l', "llama-format").action{
        (_, c) => c.copy(sygusFormat = false)
      }.text("Generates synthesis format for llama.")

      opt[Unit]('e', "enum-to-numeric").action{
        (_, c) => c.copy(enumToNumeric = true)
      }.text("Enable conversion from EnumType to NumericType - KNOWN BUGS.")

      opt[Unit]('M', "mod-set-analysis").action{
        (_, c) => c.copy(modSetAnalysis = true)
      }.text("Infers modifies set automatically.")

      opt[Unit]('u', "uf-to-array").action{
        (_, c) => c.copy(ufToArray = true)
      }.text("Enable conversion from Uninterpreted Functions to Arrays.")

      opt[Int]('w', "verbosity").action {
        ( x, c) => {c.copy(verbose = x)}
      }.text("verbosity level (0-4)")

      help("help").text("prints this usage text")

      arg[java.io.File]("<file> ...").unbounded().required().action {
        (x, c) => c.copy(files = c.files :+ x)
      }.text("List of files to analyze.")
      
      // override def renderingMode = scopt.RenderingMode.OneColumn
    }
    val config = parser.parse(args, Config())
    mainVerbosity = config.getOrElse(Config()).verbose;
    config
  }

  /** This version of 'main' does all the real work.
   */
  def main(config : Config) {
    try {
      val mainModuleName = Identifier(config.mainModuleName)
      val modules = compile(config, mainModuleName)
      val mainModule = instantiate(config, modules, mainModuleName)
      mainModule match {
        case Some(m) => execute(m, config)
        case None    =>
          throw new Utils.ParserError("Unable to find main module", None, None)
      }
      UclidMain.printStatus("Finished execution for module: %s.".format(mainModuleName.toString))
    }
    catch  {
      case (e : java.io.FileNotFoundException) =>
        UclidMain.printError("Error: " + e.getMessage() + ".")
        if(config.printStackTrace) { e.printStackTrace() }
        System.exit(1)
      case (p : Utils.ParserError) =>
        UclidMain.printError("%s error %s: %s.\n%s".format(p.errorName, p.positionStr, p.getMessage, p.fullStr))
        if(config.printStackTrace) { p.printStackTrace() }
        System.exit(1)
      case (typeErrors : Utils.TypeErrorList) =>
        typeErrors.errors.foreach {
          (p) => {
            UclidMain.printError("Type error at %s: %s.\n%s".format(p.positionStr, p.getMessage, p.fullStr))
          }
        }
        UclidMain.printError("Parsing failed. %d errors found.".format(typeErrors.errors.size))
        if(config.printStackTrace) { typeErrors.printStackTrace() }
        System.exit(1)
      case (ps : Utils.ParserErrorList) =>
        ps.errors.foreach {
          (err) => {
            UclidMain.printError("Error at " + err._2.toString + ": " + err._1 + ".\n" + err._2.pos.longString)
          }
        }
        UclidMain.printError("Parsing failed. " + ps.errors.size.toString + " errors found.")
        if(config.printStackTrace) { ps.printStackTrace() }
        System.exit(1)
      case(a : Utils.AssertionError) =>
        UclidMain.printError("[Assertion Failure]: " + a.getMessage)
        if(config.printStackTrace) { a.printStackTrace() }
        System.exit(2)
    }
  }

  def createCompilePassManager(config: Config, test: Boolean, mainModuleName: lang.Identifier) = {
    val passManager = new PassManager("compile")
    // adds init and next to every module
    passManager.addPass(new ModuleCanonicalizer())
    // introduces LTL operators (which were parsed as function applications)
    passManager.addPass(new LTLOperatorIntroducer())
    // imports all declarations except init and next declarations into module
    passManager.addPass(new ModuleImportRewriter())
    // imports types into module
    passManager.addPass(new ModuleTypesImportCollector())
    // imports defines
    passManager.addPass(new ModuleDefinesImportCollector())
    // imports constants
    passManager.addPass(new ModuleConstantsImportRewriter())
    // imports uninterpreted functions
    passManager.addPass(new ModuleFunctionsImportRewriter())
    // automatically compute modifies set
    if (config.modSetAnalysis) {
        passManager.addPass(new ModSetAnalysis())
        passManager.addPass(new ModSetRewriter())
    }
    // collects external types to the current module (e.g., module.mytype)
    passManager.addPass(new ExternalTypeAnalysis())
    // replaces module.mytype with external type 
    passManager.addPass(new ExternalTypeRewriter())
    // turns some specific functions e.g., bv_left_shift into operator applications
    passManager.addPass(new FuncExprRewriter())
    // checks instance module names exist
    passManager.addPass(new InstanceModuleNameChecker())
    // gives types to the instances
    passManager.addPass(new InstanceModuleTypeRewriter())
    // Replace a.b with the appropriate external identifier
    passManager.addPass(new RewritePolymorphicSelect())
    // Replaces constant lits with actual literal value
    passManager.addPass(new ConstantLitRewriter())
    // checks for invalid statements in macros and incorrect usage
    passManager.addPass(new MacroChecker())
    // inlines statement macros
    passManager.addPass(new MacroAnnotator())
    passManager.addPass(new MacroRewriter())
    // finds uses of type defs
    passManager.addPass(new TypeSynonymFinder())
    // rewrites the type defs to be original type
    passManager.addPass(new TypeSynonymRewriter())
    // renames local variables to blocks so that they don't clash?
    passManager.addPass(new BlockVariableRenamer())
    // compute the width of bitvector slice operations.
    passManager.addPass(new BitVectorSliceFindWidth())
    // the big type checker 
    passManager.addPass(new ExpressionTypeChecker())
    // test flag is default false
    // checks if prime/old/history are used in the incorrect places
    if (!test) passManager.addPass(new VerificationExpressionChecker())
    passManager.addPass(new PolymorphicGrammarTypeRewriter())
    // rewrites bitvector operators (except slice) to have a width and returns a "reified" operator
    // runs expression type checker pass again ? is this necessary
    // then replaces operators with operators from the polyOpMap
    passManager.addPass(new PolymorphicTypeRewriter())
    // check for recursive dependencies 
    passManager.addPass(new FindProcedureDependency())
    // check for recursive defines
    passManager.addPass(new DefDepGraphChecker())
    // expands macros
    passManager.addPass(new RewriteDefines())
    // type checker for module specific things e.g., module declarations
    passManager.addPass(new ModuleTypeChecker())
    // checks for incorrect assignments to next state vars
    passManager.addPass(new PrimedAssignmentChecker())
    // looks for semantic errors e.g., redeclarations
    passManager.addPass(new SemanticAnalyzer())
    //  ProcedureChecker
    //  *  If a procedure has pre/post conditions
    //  *    - it should not write to a variable that has not been declared modified.
    //  *    - only state variables should be declared modifiable
    passManager.addPass(new ProcedureChecker())
    // checks arguments of control commands and types etc
    passManager.addPass(new ControlCommandChecker())
    // types of each argument in a module instantiation
    passManager.addPass(new ComputeInstanceTypes())
    // checks module instancs are instantiated correctly
    passManager.addPass(new ModuleInstanceChecker())
    passManager.addPass(new CaseEliminator())
    passManager.addPass(new ForLoopUnroller())
    // hyperproperties for procedures
    passManager.addPass(new ModularProductProgram())
    passManager.addPass(new WhileLoopRewriter())
    passManager.addPass(new BitVectorSliceConstify())
    passManager.addPass(new VariableDependencyFinder())
    passManager.addPass(new StatementScheduler())
    passManager.addPass(new BlockFlattener())

    passManager.addPass(new NewInternalProcedureInliner())
    // self explanatory
    passManager.addPass(new PrimedVariableCollector())
    passManager.addPass(new PrimedVariableEliminator())
    passManager.addPass(new PrimedHistoryRewriter())
    passManager.addPass(new IntroduceFreshHavocs())
    passManager.addPass(new RewriteFreshLiterals())
    // Optimisation, called multiple times. This also calls redundantassignmenteliminator
    passManager.addPass(new BlockFlattener())
    passManager.addPass(new ModuleCleaner())
    passManager.addPass(new BlockVariableRenamer())
    passManager
  }  
  /** Parse modules, typecheck them, inline procedures, create LTL monitors, etc. */
  def compile(config: Config, mainModuleName : Identifier, test : Boolean = false): List[Module] = {
    UclidMain.printVerbose("Compiling modules")
    type NameCountMap = Map[Identifier, Int]
    val srcFiles : Seq[java.io.File] = config.files
    var nameCnt : NameCountMap = Map().withDefaultValue(0)
    val passManager = createCompilePassManager(config, test, mainModuleName)

    val filenameAdderPass = new AddFilenameRewriter(None)
    // Helper function to parse a single file.
    def parseFile(srcFile : String) : List[Module] = {
      val file = scala.io.Source.fromFile(srcFile)
      // TODO: parse line by line instead of loading the complete file into a string
      val modules = UclidParser.parseModel(srcFile, file.mkString)
      file.close()
      filenameAdderPass.setFilename(srcFile)
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
    passManager.addPass(new ExternalSymbolAnalysis())
    passManager.addPass(new ProcedureModifiesRewriter())
    // flattens modules into main
    passManager.addPass(new ModuleFlattener(mainModuleName))
    // gets rid of modules apart from main
    passManager.addPass(new ModuleEliminator(mainModuleName))
    // Expands (grounds) finite_forall and finite_exists quantifiers
    passManager.addPass(new FiniteQuantsExpander())
    passManager.addPass(new LTLOperatorRewriter())
    passManager.addPass(new LTLPropertyRewriter())
    passManager.addPass(new Optimizer())
    // optimisation, has previously been called
    passManager.addPass(new ModuleCleaner())
     // optimisation, has previously been called
    passManager.addPass(new Optimizer())
    // optimisation, has previously been called
    passManager.addPass(new BlockVariableRenamer())
    // optimisation, has previously been called
    passManager.addPass(new ExpressionTypeChecker())
    // optimisation, has previously been called
    passManager.addPass(new ModuleTypeChecker())
    // optimisation, has previously been called
    passManager.addPass(new SemanticAnalyzer())
    // known bugs in the following passes
    if (config.enumToNumeric) passManager.addPass(new EnumTypeAnalysis())
    if (config.enumToNumeric) passManager.addPass(new EnumTypeRenamer("BV"))
    if (config.enumToNumeric) passManager.addPass(new EnumTypeRenamerCons("BV"))
    if (config.ufToArray)     passManager.addPass(new UninterpretedFunctionToArray())
    // run passes.
    passManager.run(moduleList)
  }

  /** Instantiate modules.
   *
   * @param moduleList List of modules to be analyzed.
   * @param mainModuleName Name of main module.
   * @param verbose If this is true, we print the message describing the number of modules parsed and instantiated.
   */
  def instantiate(config : Config, moduleList : List[Module], mainModuleName : Identifier) : Option[Module] = {
    if (moduleList.find(m => m.id == mainModuleName).isEmpty) {
      return None
    }
    val moduleListP = instantiateModules(config, moduleList, mainModuleName)
    UclidMain.printStatus("Successfully instantiated %d module(s).".format(moduleList.size, moduleListP.size))
    // return main module.
    moduleListP.find((m) => m.id == mainModuleName)
  }

  /** Execute the control module.
   *
   */
  def execute(module : Module, config : Config) : List[CheckResult] = {
    UclidMain.printVerbose("Begining execution")
    var symbolicSimulator = new SymbolicSimulator(module)
    var solverInterface = if (config.smtSolver.size > 0) {
      logger.debug("args: {}", config.smtSolver)
      new smt.SMTLIB2Interface(config.smtSolver)
    } else if (config.synthesizer.size > 0) {
      new smt.SynthLibInterface(config.synthesizer, config.sygusFormat)
    } else {
      new smt.Z3Interface()
    }
    solverInterface.filePrefix = config.smtFileGeneration
    val result = symbolicSimulator.execute(solverInterface, config)
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


  def printVerbose(str : String) {
    if(mainVerbosity>=4)
      println(str)
  }

  def printDetailedStats(str : String) {
    if(mainVerbosity>=3)
      println(str)
  }

  def printStats(str : String) {
    if(mainVerbosity>=2)
      println(str)
  }


  def printStatus(str : String) {
    if(mainVerbosity>=1)
      println(str)
  }

  def printResult(str : String) {
    println(str)
  }

  def printError(str : String) {
    println(str)
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
