package uclid

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
import com.typesafe.scalalogging.Logger

object UclidAPI {
  val logger = Logger("uclid.UclidAPI")

  var mainVerbosity: Int = 1;

  var debugReWriteRecord: Boolean = false;

  /** Command-line configuration flags for uclid5.
   *
   * @param mainModuleName The name of the main module.
   * @param smtSolver The location of an SMT solver executable along with arguments that must be passed to it.
   * @param files List of files that should parsed and analyzed.
   */
  case class APIConfig(
      mainModule        : WModule = WModule(),
      smtSolver         : List[String] = List.empty,
      smtFileGeneration : String = "",
      jsonCEXfile       : String = "",
      ufToArray         : Boolean = false,
      printStackTrace   : Boolean = false,
      noLetify          : Boolean = false, // prevents SMTlib interface from letifying
      /* 
        verbosities:
        0: essential: print nothing but results and error messages
        1: basic: current default behaviour, includes statuses
        2: stats: includes statistics on time/which properties are being solved
        3: print everything
      */
      verbose           : Int = 1, 
      testFixedpoint: Boolean = false
  )

  def buildConfig (pconfig: APIConfig) : UclidMain.Config = {
    val config = new UclidMain.Config(
        mainModuleName = pconfig.mainModule.name,
        smtSolver = pconfig.smtSolver,
        smtFileGeneration = pconfig.smtFileGeneration,
        jsonCEXfile = pconfig.jsonCEXfile,
        ufToArray = pconfig.ufToArray,
        printStackTrace = pconfig.printStackTrace,
        noLetify = pconfig.noLetify,
        verbose = pconfig.verbose,
        testFixedpoint = pconfig.testFixedpoint,
    )
    config
  }

  /** This version of 'main' does all the real work.
   */
  def solveProcedural(pconfig : APIConfig) : String = {
    val config = buildConfig(pconfig)
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    try {
      val mainModuleName = Identifier(config.mainModuleName)
      val modules = compile(config, pconfig.mainModule)
      val mainModule = UclidMain.instantiate(config, modules, mainModuleName)
      mainModule match {
        case Some(m) =>
          if(!m.cmds.isEmpty)
          {
            // Split the control block commands to blocks on commands that modify the module
            val cmdBlocks = UclidMain.splitCommands(m.cmds)
            // Execute the commands for each block
            cmdBlocks.foreach(cmdBlock => UclidMain.executeCommands(m, cmdBlock, config, mainModuleName))
          }
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
      case (syn : Utils.SyntaxError) =>
        UclidMain.printError("%s error on %s: %s.\n%s".format(syn.errorName, syn.positionStr, syn.getMessage, syn.shortStr))
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
    UclidMain.stringOutput.toString()
  }




  /** Parse modules, typecheck them, inline procedures, create LTL monitors, etc. */
  def compile(config: UclidMain.Config, wmod : WModule, test : Boolean = false): List[Module] = {
    UclidMain.printVerbose("Compiling modules")
    type NameCountMap = Map[Identifier, Int]
    val srcFiles : Seq[java.io.File] = config.files
    var nameCnt : NameCountMap = Map().withDefaultValue(0)
    val passManager = UclidMain.createCompilePassManager(config, test, wmod.name_)

    val filenameAdderPass = new AddFilenameRewriter(None)
    // // Helper function to parse a single file.
    // def parseFile(srcFile : String) : List[Module] = {
    //   val file = scala.io.Source.fromFile(srcFile)
    //   // TODO: parse line by line instead of loading the complete file into a string
    //   val modules = UclidParser.parseModel(srcFile, file.mkString)
    //   file.close()
    //   filenameAdderPass.setFilename(srcFile)
    //   modules.map(m => filenameAdderPass.visit(m, Scope.empty)).flatten
    // }
    val parsedModules = List(wmod.buildModule())

    //     srcFiles.foldLeft(List.empty[Module]) {
    //   (acc, srcFile) => acc ++ parseFile(srcFile.getPath())
    // }

    // combine all modules with the same name
    val combinedParsedModules = parsedModules
      .groupBy(_.id)
      .map((kv) => {
        val id = kv._1
        val modules = kv._2
        if (modules.size > 1) {
          UclidMain.printStatus("Multiple definitions for module " + modules.head.id.toString() + " were found and have been combined.")
        }
        val combinedModule = modules.foldLeft(Module(id, List.empty, List.empty, List.empty)){
          (acc, module) => {
            val declsP = {
              val nonInitAccDecls = acc.decls.filter(p => !p.isInstanceOf[InitDecl])
              val initAccDecls = acc.decls.filter(p => p.isInstanceOf[InitDecl]).headOption
              val nonInitModuleDecls = module.decls.filter(p => !p.isInstanceOf[InitDecl])
              val initModuleDecls = module.decls.filter(p => p.isInstanceOf[InitDecl]).headOption
              val newInitDecl = initAccDecls match {
                case Some(initAcc) => initModuleDecls match {
                  case Some(initMod) => List(InitDecl(BlockStmt(List[BlockVarsDecl](), 
                    List(initAcc.asInstanceOf[InitDecl].body, initMod.asInstanceOf[InitDecl].body))))
                  case None => List(initAcc)
                }
                case None => initModuleDecls match {
                  case Some(initMod) => List(initMod)
                  case None => List[Decl]()
                }
              }
              newInitDecl ++ nonInitAccDecls ++ nonInitModuleDecls
            }
            val cmdsP = (acc.cmds ++ module.cmds)
            Utils.assert(module.notes.size == 1 && module.notes.head.asInstanceOf[InstanceVarMapAnnotation].iMap.size == 0, "Expected module to initially have empty annotations.")
            // since the notes (list of annotations of the modules) are default values, it's okay to remove the duplicates in the line below
            val notesP = (acc.notes ++ module.notes).distinct
            Module(id, declsP, cmdsP, notesP)
          }
        }
        id -> combinedModule
      })
      .toMap
    // restore ordering of modules
    val combinedParsedModulesP = parsedModules
      .map(module => module.id)
      .distinct
      .map(id => combinedParsedModules.get(id).get)
      .toList

    // now process each module
    val init = (List.empty[Module], Scope.empty)
    // NOTE: The foldLeft/:: combination here reverses the order of modules.
    // The PassManager in instantiate calls run(ms : List[Module]); this version of run uses foldRight.
    // So modules end up being processed in the same order in both PassManagers.
    val processedModules = combinedParsedModulesP.foldLeft(init) {
      (acc, m) =>
        val modules = acc._1
        val context = acc._2
        val mP = passManager.run(m, context).get
        (mP :: modules, context +& mP)
    }._1
    val moduleNames = processedModules.map(m => (m.id, m.id.position)).reverse
    val errors = SemanticAnalyzerPass.checkIdRedeclaration(moduleNames, List.empty)
    if (errors.size > 0) {
      throw new Utils.ParserErrorList(errors.map(e => (e.msg, e.position)))
    }
    processedModules
  }
}