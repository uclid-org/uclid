package uclid
package lang

import scala.collection.mutable.{ListBuffer,Set} 

class PassManager {
  type PassList = ListBuffer[ASTAnalysis]
  var passes : PassList = new PassList()
  var passNames : Set[String] = Set.empty
  
  def addPass(pass : ASTAnalysis) {
    Utils.assert(!passNames.contains(pass.passName), "Pass with the same name already exists.")
    passNames += pass.passName
    passes += pass
    pass._manager = Some(this)
  }
  
  def run(module : Module) : Option[Module] = {
    passes.foreach{ _.reset() }
    
    val init : Option[Module] = Some(module)
    def applyPass(pass: ASTAnalysis, m: Module) : Option[Module] = {
      val mP = pass.visit(m)
      if (pass.iteratedApply && pass.astChanged && !mP.isEmpty) {
        applyPass(pass, mP.get)
      } else {
        mP
      }
    }
    
    return passes.foldLeft(init){
      (mod, pass) => mod.flatMap(applyPass(pass, _))
    }
  }

  def pass(name : String) : ASTAnalysis = passes.find(_.passName == name).get
  def doesPassExist(name : String) = passNames.contains(name)
  def getPass(name : String) : Option[ASTAnalysis] = passes.find((p) => p.passName == name)
}