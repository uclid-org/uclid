package uclid
package lang

import scala.collection.mutable

/*
 *  Collect verified procedures pass
 * 
 *  Author : Elizabeth Polgreen
 *
 * This pass collects a list of procedures which are verified using the verify(cmd)
 * All other procedures can then be removed by the module cleaner pass, since the 
 * all procedure calls have been inlined by the time this pass is run.
 */
   
class CollectVerifiedProceduresPass extends ReadOnlyPass[Set[Identifier]]
{
  override def applyOnCmd(d: TraversalDirection.T, cmd: GenericProofCommand, in: Set[Identifier], context: Scope): Set[Identifier] = {
    if(cmd.isVerify)
    {
      in + cmd.args(0)._1.asInstanceOf[Identifier];
    }
    else
      in
  }
}

class VerifiedProceduresAnalysis() extends ASTAnalyzer("VerifiedProceduresAnalysis", new CollectVerifiedProceduresPass()) {
  override def reset() {
    in = Some(Set[Identifier]())
  }

  override def visit(module : Module, context : Scope) : Option[Module] = {
    val verifiedProcedureSet = visitModule(module, Set[Identifier](), context)
    _out = Some(verifiedProcedureSet)
    return Some(module)
  }
}

class ModuleCleanerPass() extends RewritePass {
  lazy val manager : PassManager = analysis.manager
  
  var doRemoveFunctions = false;
  lazy val verifiedProcedureSet : Set[Identifier] = 
  {
    if(manager.doesPassExist("VerifiedProceduresAnalysis"))
    {
      val verifiedProcedureAnalysis = manager.pass("VerifiedProceduresAnalysis").asInstanceOf[VerifiedProceduresAnalysis]
      doRemoveFunctions=true
      verifiedProcedureAnalysis.out.getOrElse(Set[Identifier]())
    }
    else
    {
      Set[Identifier]()
    }
  }
  
  

  override def rewriteModuleTypesImport(modTypImport : ModuleTypesImportDecl, ctx : Scope) : Option[ModuleTypesImportDecl] = {
    None
  }
  override def rewriteModuleFunctionsImport(modFuncImport : ModuleFunctionsImportDecl, ctx : Scope) : Option[ModuleFunctionsImportDecl] = {
    None
  }
  override def rewriteModuleConstantsImport(modCnstImport : ModuleConstantsImportDecl, ctx : Scope) : Option[ModuleConstantsImportDecl] = {
    None
  }
  override def rewriteModuleDefinesImport(modDefImport : ModuleDefinesImportDecl, ctx : Scope) : Option[ModuleDefinesImportDecl] = {
    None
  }

  override def rewriteProcedure(proc: ProcedureDecl, ctx: Scope): Option[ProcedureDecl] = {
    if(verifiedProcedureSet.contains(proc.id) || !doRemoveFunctions)
      Some(proc)
    else
      None    
  }

  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    val declsP = module.decls.sortWith((d1, d2) => d1.hashId < d2.hashId)
    Some(Module(module.id, declsP, module.cmds, module.notes))
  }
}

class ModuleCleaner() extends ASTRewriter(
    "ModuleCleaner", new ModuleCleanerPass())

class ModuleEliminatorPass(moduleName : Identifier) extends RewritePass {
  override def rewriteModule(module : Module, ctx : Scope) : Option[Module] = {
    if (module.id == moduleName) {
      Some(module)
    } else {
      None
    }
  }
}

class ModuleEliminator(moduleName : Identifier) extends ASTRewriter(
    "ModuleEliminator", new ModuleEliminatorPass(moduleName))
