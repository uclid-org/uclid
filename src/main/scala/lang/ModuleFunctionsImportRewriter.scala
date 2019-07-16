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
 * Author: Pramod Subramanyan
 * Rewrite function * = moduleId.*; declarations.
 *
 */

package uclid
package lang

import com.typesafe.scalalogging.Logger
import scala.collection.mutable.HashMap

//TODO: Verify that we don't actually need to pull in axioms if we just rewrite
// all functions as 'module' + '.' func

class ModuleFunctionsImportRewriterPass extends RewritePass {

  
}


class ModuleFunctionsImportRewriter extends ASTRewriter(
  "ModuleFunctionsImportRewriter", new ModuleFunctionsImportRewriterPass()) {

  // Collects all functions into map, while checking for redeclaration errors
  def collectFunctionDecls(module : Module, map : HashMap[Identifier, Identifier]) : HashMap[Identifier, Identifier] = {
    module.functions.map(f => map.get(f.id) match {
      case Some(_) => throw new Utils.AssertionError("Redeclaration error in module functions import")
      case None => map += ((f.id, module.id))
    })
    map
  }

  // Collects the names of all modules to import functions from
  // TODO: Add error checking for 'fullList'
  def findModuleDependencies(module : Module, modList: List[Module]) : List[Identifier] = {
    val importList : List[Identifier] = module.decls.collect { case importDecl : ModuleFunctionsImportDecl => importDecl.id }
    val fullList = importList ++ importList.foldLeft(List[Identifier]()) { (list, id) => {
        val mod = modList.find(m => m.id == id)
        if (mod == None) {
          list
        } else {
          val dependencies = findModuleDependencies(mod.get, modList) 
          list ++ dependencies
        }
      }
    }
    fullList
  }


  def collectAllFunctions(module : Module, map : HashMap[Identifier, Identifier], modList : List[Module]) : HashMap[Identifier, Identifier] = {
    val moduleList = findModuleDependencies(module, modList)
    moduleList.map(id => {
      // moduleList should only use available modules
      val mod = modList.find(m => m.id == id).get
      collectFunctionDecls(mod, map)
    })
    map
  }

  
  override def visitModule(module : Module, initContext : Scope) : Option[Module] = {
    
    val funcMap = collectAllFunctions(module, new HashMap(), manager.moduleList)
    val rewriterMap = funcMap.map(p => (p._1 -> OperatorApplication(PolymorphicSelect(p._1), List(p._2)))).asInstanceOf[HashMap[Expr, Expr]].toMap
    val rewriter = new ExprRewriter("FunctionRewriter", rewriterMap)


    
    val context = initContext + module
    val id = visitIdentifier(module.id, context)
    val decls = module.decls.map(visitDecl(_, context)).flatten.map(rewriter.visitDecl(_, context)).flatten
    val initR : (List[Option[GenericProofCommand]], Scope) = (List.empty, initContext)
    val cmds = module.cmds.foldRight(initR)((cmd, acc) => (visitCommand(cmd, acc._2) :: acc._1, acc._2 + cmd))._1.flatten
    val notes = module.notes.map(note => visitNote(note, context)).flatten
    val moduleIn = id.flatMap((i) => Some(Module(i, decls, cmds, notes)))
    val moduleP = moduleIn.flatMap((m) => pass.rewriteModule(m, initContext))

    return (ASTNode.introducePos(true, true, moduleP, module.position) match {
      case Some(m) =>
        module.filename match {
          case Some(fn) => Some(m.withFilename(fn))
          case None     => Some(m)
        }
      case None =>
        None
    })
  }

}

class ModuleFunctionsImportCollectorPass extends ReadOnlyPass[List[Decl]] {
  lazy val logger = Logger(classOf[ModuleFunctionsImportCollector])
  type T = List[Decl]
  
  def isStatelessExpression(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)    | Scope.InputVar(_, _)  |
               Scope.OutputVar(_, _)   | Scope.SharedVar(_, _) |
               Scope.FunctionArg(_, _) | Scope.Define(_, _, _) |
               Scope.Instance(_)       =>
             false
          case Scope.ConstantVar(_, _)    | Scope.Function(_, _)       |
               Scope.LambdaVar(_ , _)     | Scope.ForallVar(_, _)      |
               Scope.ExistsVar(_, _)      | Scope.EnumIdentifier(_, _) |
               Scope.ConstantLit(_, _)    =>
             true
          case Scope.ModuleDefinition(_)      | Scope.Grammar(_, _)             |
               Scope.TypeSynonym(_, _)        | Scope.Procedure(_, _)           |
               Scope.ProcedureInputArg(_ , _) | Scope.ProcedureOutputArg(_ , _) |
               Scope.ForIndexVar(_ , _)       | Scope.SpecVar(_ , _, _)         |
               Scope.AxiomVar(_ , _, _)       | Scope.VerifResultVar(_, _)      |
               Scope.BlockVar(_, _)           | Scope.SelectorField(_)          =>
             throw new Utils.RuntimeError("Can't have this identifier in assertion: " + namedExpr.toString())
        }
      case None =>
        throw new Utils.UnknownIdentifierException(id)
    }
  }
  def isStatelessExpr(e: Expr, context : Scope) : Boolean = {
    e match {
      case id : Identifier =>
        isStatelessExpression(id, context)
      case ei : ExternalIdentifier =>
        true
      case lit : Literal =>
        true
      case rec : Tuple =>
        rec.values.forall(e => isStatelessExpr(e, context))
      case OperatorApplication(ArraySelect(inds), args) =>
        inds.forall(ind => isStatelessExpr(ind, context)) &&
        args.forall(arg => isStatelessExpr(arg, context))
      case OperatorApplication(ArrayUpdate(inds, value), args) =>
        inds.forall(ind => isStatelessExpr(ind, context)) &&
        args.forall(arg => isStatelessExpr(arg, context)) &&
        isStatelessExpr(value, context)
      case opapp : OperatorApplication =>
        opapp.operands.forall(arg => isStatelessExpr(arg, context + opapp.op))
      case a : ConstArray =>
        isStatelessExpr(a.exp, context)
      case fapp : FuncApplication =>
        isStatelessExpr(fapp.e, context) && fapp.args.forall(a => isStatelessExpr(a, context))
      case lambda : Lambda =>
        isStatelessExpr(lambda.e, context + lambda)
    }
  }
  
  def isFunctionExpression(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) => 
        namedExpr match {
          case Scope.Function(_, _) => true
          case _ => false;
        }
      case None => {
        throw new Utils.UnknownIdentifierException(id)
      }
    }
  }
  
  def isFunctionExpr(e : Expr, context : Scope) : Boolean = {
      e match {
      case id : Identifier =>
        isFunctionExpression(id, context)
      case ei : ExternalIdentifier =>
        false
      case lit : Literal =>
        false
      case rec : Tuple =>
        rec.values.exists(e => isFunctionExpr(e, context))
      case OperatorApplication(ArraySelect(inds), args) =>
        inds.exists(ind => isFunctionExpr(ind, context)) || 
        args.exists(arg => isFunctionExpr(arg, context))
      case OperatorApplication(ArrayUpdate(inds, value), args) =>
        inds.exists(ind => isFunctionExpr(ind, context)) || 
        args.exists(arg => isFunctionExpr(arg, context)) ||
        isStatelessExpr(value, context)
      case opapp : OperatorApplication =>
        opapp.operands.exists(arg => isFunctionExpr(arg, context + opapp.op))
      case a : ConstArray =>
        isFunctionExpr(a.exp, context)
      case fapp : FuncApplication =>
        isFunctionExpr(fapp.e, context) || fapp.args.exists(a => isFunctionExpr(a, context))
      case lambda : Lambda =>
        isFunctionExpr(lambda.e, context + lambda)
    }
  }

  def isStatelessAndFunctionExpr(e : Expr, context : Scope) : Boolean = {
    isStatelessExpr(e, context) && isFunctionExpr(e, context)
  }

  override def applyOnModuleFunctionsImport(d : TraversalDirection.T, modFuncImport : ModuleFunctionsImportDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      //logger.debug("statement: {}", modFuncImport.toString())
      val id = modFuncImport.id
      context.map.get(id) match {
        case Some(Scope.ModuleDefinition(mod)) => {
          val newFuncs : List[Decl]  = mod.functions.map {
            f => {
              ASTNode.introducePos(true, true, f, modFuncImport.position)
            }
          } ++ in
          // Add axioms related to functions
          
          val newAxioms : List[Decl] = mod.axioms.filter(a => isStatelessAndFunctionExpr(a.expr, Scope.empty + mod))
          newAxioms.map {
            a => {
              ASTNode.introducePos(true, true, a, modFuncImport.position)
            }
          } ++ newFuncs
        }
        case _ => in
      }
    } else {
      in
    }
  }
}

class ModuleFunctionsImportCollector extends ASTAnalyzer("ModuleFunctionsImportCollector", new ModuleFunctionsImportCollectorPass()) {
  lazy val logger = Logger(classOf[ModuleFunctionsImportCollector])
  
  override def reset() {
    in = Some(List.empty)
  }
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val externalIds = visitModule(module, List.empty, context)
    val newImports = externalIds.map {
      d => {
        d match {
          case d : AxiomDecl     => ASTNode.introducePos(true, true, d, d.position)
          case d : FunctionDecl  => ASTNode.introducePos(true, true, d, d.position)
          case _ => throw new Utils.RuntimeError("Shouldn't have anything but axioms and functions.")
        }
      }
    }
    
    //logger.debug("newImports: " + newImports.toString())
    val modP = Module(module.id, newImports ++ module.decls, module.cmds, module.notes)
    return Some(modP)
  }
}



