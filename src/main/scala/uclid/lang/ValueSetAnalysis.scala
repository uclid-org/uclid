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
 * Author: Elizabeth Polgreen

 * Does a very basic flow-insensitive value set analysis: finds all simple assignments,
 * and builds a map
 *
 */

package uclid
package lang
import collection.mutable.{ HashMap, MultiMap, Set }
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

 class ValueSetAssignRewriterPass(changeSet: mutable.Map[Identifier, Identifier]) extends RewritePass {
  override def rewriteIdentifier(id: Identifier, ctx: Scope): Option[Identifier] = {
   if(changeSet.contains(id))
   {
     Some(changeSet(id))
   }
   else
    Some(id)
  }
}
 class RemoveUnusedDeclarationsRewriterPass(changeSet: mutable.Map[Identifier, Identifier]) extends RewritePass {
  override def rewriteBlockVars(bvars: BlockVarsDecl, ctx: Scope): Option[BlockVarsDecl] = {
    var newIds = Set.empty[Identifier]
    bvars.ids.foldLeft(newIds){(result, v) => 
      if(changeSet.contains(v))
      {
        result
      }
      else
       result+=v
  }
  if(newIds.size>0)
    {
      Some(new BlockVarsDecl(newIds.toList, bvars.typ))
    }
  else
    None
}
}

class ValueSetAnalysis extends ASTAnalysis {

  type ValueSet = HashMap[Identifier, Set[Identifier]] with MultiMap[Identifier, Identifier] 

  class BuildValueSet extends ReadOnlyPass[ValueSet]{
  override def applyOnAssign(d : TraversalDirection.T, st : AssignStmt, in : ValueSet, context : Scope) : ValueSet = {
    val zipped = st.lhss zip st.rhss
    zipped.foldLeft(in) { (result, v) => redundantAssign(v._1,v._2,result)}
  }
        
  def redundantAssign(lhs : Lhs, rhs : Expr, in:ValueSet) : ValueSet = {
    rhs match {
      case e : Identifier => {
        if (e == lhs.ident) {
          in
        } else {
          in.addBinding(lhs.ident, e)
          in       
        }
      }
      case _ => in
    }
   } 
  }

  class BuildReadSetPass extends ReadOnlyPass[Set[Identifier]]{
    // these do nothing, we don't want to find identifiers on the LHS
    override def applyOnExpr(d: TraversalDirection.T, e: Expr, in: mutable.Set[Identifier], context: Scope): mutable.Set[Identifier] = {
      e match {
        case i: Identifier => in +=i
        case _ => in
      }
    }
  }

  class ReadSetBuilder extends ASTAnalyzer("BuildReadSet", new BuildReadSetPass())
  {
    override def visitAssignStatement(st : AssignStmt, in : Set[Identifier], context : Scope) : Set[Identifier] = {
    var result :  Set[Identifier] = in
    result = pass.applyOnAssign(TraversalDirection.Down, st, result, context)
    //result = st.lhss.foldLeft(result)((arg, i) => visitLhs(i, arg, context))
    // result = st.rhss.foldLeft(result)((arg, i) => 
    //   i match {
    //     case e: Identifier => result
    //     case _ =>  visitExpr(i, arg, context)
    // })
    result = st.rhss.foldLeft(result)((arg, i) => visitExpr(i, arg, context))
    result = pass.applyOnAssign(TraversalDirection.Up, st, result, context)
    return result
  }

    // these passes are overridden to prevent them exploring identifiers that aren't reads
    override def visitLhs(lhs : Lhs, in : Set[Identifier], context : Scope) : Set[Identifier] = {in}
    override def visitStateVars(stVars : StateVarsDecl, in : Set[Identifier], context : Scope) : Set[Identifier] = {in}
    override def visitInputVars(inpVars: InputVarsDecl, in: mutable.Set[Identifier], context: Scope): mutable.Set[Identifier] = {in}
    override def visitOutputVars(outVars: OutputVarsDecl, in: mutable.Set[Identifier], context: Scope): mutable.Set[Identifier] = in
    override def visitSharedVars(sharedVars: SharedVarsDecl, in: mutable.Set[Identifier], context: Scope): mutable.Set[Identifier] = in
    override def visitConstantLit(cnstLit: ConstantLitDecl, in: mutable.Set[Identifier], context: Scope): mutable.Set[Identifier] = in
    override def visitConstants(cnst: ConstantsDecl, in: mutable.Set[Identifier], context: Scope): mutable.Set[Identifier] = in
    override def visitModuleConstantsImport(moduleConstantsImport : ModuleConstantsImportDecl, in : Set[Identifier], context : Scope) : Set[Identifier] = {in}
    override def visitTypeDecl(typDec : TypeDecl, in : Set[Identifier], context : Scope) : Set[Identifier] = {in}
    override def visitModuleTypesImport(moduleTypesImport : ModuleTypesImportDecl, in : Set[Identifier], context : Scope) : Set[Identifier] = {in}
    override def visitCmd(cmd : GenericProofCommand, in : Set[Identifier], context : Scope) : Set[Identifier] = {in}
  }

  
  def buildChangeSet(valueSet: ValueSet, readSet: Set[Identifier]): mutable.Map[Identifier, Identifier] = {
    var changeSet = mutable.Map.empty[Identifier,Identifier]
    valueSet.foldLeft(changeSet) {(result,v) => 
    if(/*v._2.size==1 &&*/ !readSet.contains(v._1))
    {
      result += (v._1 -> v._2.head)
    }
     result
   }
   changeSet
  }


  var buildValueSetPass = new BuildValueSet()
  var valueSetBuilder = new ASTAnalyzer("BuildValueSet", buildValueSetPass)
  var readSetBuilder = new ReadSetBuilder()
  
  override def passName = "valueSetAnalysis"

  override def visit(module : Module, context : Scope) : Option[Module] = {
    var modP : Option[Module] = Some(module)
    var modP2: Option[Module] = Some(module)
    var iteration = 0
    val valueSet = new HashMap[Identifier, Set[Identifier]] with MultiMap[Identifier, Identifier]
    
    var done = false
    do {
      modP match {
        case None =>
          done = true
        case Some(mod) =>
          val thisValueSet = valueSetBuilder.visitModule(mod, valueSet, context)
          val thisReadSet  = readSetBuilder.visitModule(mod, Set.empty[Identifier], context)
          done = false
          if (!done) {
            val changeSet = buildChangeSet(thisValueSet,thisReadSet)
            val removeExtraDecls = new ASTRewriter("valueSetAnalysis.RemoveExtraDecls", new RemoveUnusedDeclarationsRewriterPass(changeSet))
            var mod1 = removeExtraDecls.visit(mod,context)
            val valueSetRewriter = new ASTRewriter("valueSetAnalysis.ValueSetRewriter", new ValueSetAssignRewriterPass(changeSet))
            modP = valueSetRewriter.visit(mod1.getOrElse(mod), context)
            done = true;
            
            if(changeSet.size>0)
            {
              println("changeSet: " + changeSet)
            }
            println("changeSet size: " + changeSet.size)

            val redundantAssignmentEliminator = new RedundantAssignmentEliminator()
            modP2 = redundantAssignmentEliminator.visit(modP.getOrElse(mod),context)      
          }
      }
    } while(!done)
    return modP2
  }
}
