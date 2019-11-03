package uclid.lang.modelcounts

import uclid.UclidMain
import uclid.{lang => l}

object UMCMain {
  def checkModel(f: java.io.File, config: UclidMain.Config) {
    val passManager = createModulePassManager(l.Identifier(config.mainModuleName))
    passManager.run(UMCParser.parseUMCModel(f), l.Scope.empty) match {
      case Some(m) => UclidMain.execute(m, config)
      case None =>
        throw new uclid.Utils.ParserError(
            "Unable to find main module: " + config.mainModuleName, None, None)
    }
  }
  def createModulePassManager(mainModuleName: l.Identifier) = {
    val passManager = new l.PassManager("compile")
    // passManager.addPass(new ASTPrinter())
    passManager.addPass(new l.ModuleCanonicalizer())
    passManager.addPass(new l.ModuleTypesImportCollector())
    passManager.addPass(new l.ModuleConstantsImportCollector())
    passManager.addPass(new l.ModuleFunctionsImportCollector())

    passManager.addPass(new l.ExternalTypeAnalysis())
    passManager.addPass(new l.ExternalTypeRewriter())
    passManager.addPass(new l.FuncExprRewriter())
    passManager.addPass(new l.InstanceModuleNameChecker())
    passManager.addPass(new l.InstanceModuleTypeRewriter())
    passManager.addPass(new l.RewritePolymorphicSelect())
    passManager.addPass(new l.ConstantLitRewriter())
    passManager.addPass(new l.TypeSynonymFinder())
    passManager.addPass(new l.TypeSynonymRewriter())
    passManager.addPass(new l.BlockVariableRenamer())
    passManager.addPass(new l.BitVectorSliceFindWidth())
    passManager.addPass(new l.ExpressionTypeChecker())
    passManager.addPass(new l.VerificationExpressionChecker())
    passManager.addPass(new l.PolymorphicTypeRewriter())
    passManager.addPass(new l.FindProcedureDependency())
    passManager.addPass(new l.DefDepGraphChecker())
    passManager.addPass(new l.RewriteDefines())
    passManager.addPass(new l.ModuleTypeChecker())
    passManager.addPass(new l.SemanticAnalyzer())
    passManager.addPass(new l.ControlCommandChecker())
    passManager.addPass(new l.ComputeInstanceTypes())
    passManager.addPass(new l.ModuleInstanceChecker())
    passManager.addPass(new l.BlockFlattener())
    passManager.addPass(new l.ModuleCleaner(mainModuleName))
    passManager.addPass(new l.BlockVariableRenamer())
    passManager
  }  

}