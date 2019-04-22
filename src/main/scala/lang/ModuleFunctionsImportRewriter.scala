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

//TODO: Rewrite method that calls `applyOnModuleFunctionsImport` to collect external mappings (just
//        functions) and aggregate the function declarations; if any identifiers clash, throw a 
//        redeclaration error. 
//
//        NOTE: We could also enhance UCLID's type inference system by using the function signature 
//        ( paramater and return types ) to identify a function.

//TODO: Pass the aggregated list to a following step, where all of the functions in the module are
//        checked for declaration in the module or checked in the aggregated list and written as 
//        an external type.
//
//        NOTE: If the identifier is double declared in the current environment and the imported
//          environment, then throw a DoubleDecl error. If not declared in either, then throw 
//          a NotDefined error.
//        

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
        throw new Utils.RuntimeError("Unknown identifiers should have been detected by now.")
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
        println("Unnamed expression :(")
        false
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

  def isStatelessAndFunctionAxiom(e : Expr, context : Scope) : Boolean = {
    isStatelessExpr(e, context) && isFunctionExpr(e, context)
  }

  override def applyOnModuleFunctionsImport(d : TraversalDirection.T, modFuncImport : ModuleFunctionsImportDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      logger.debug("statement: {}", modFuncImport.toString())
      val id = modFuncImport.id
      context.map.get(id) match {
        case Some(Scope.ModuleDefinition(mod)) => {
          val newFuncs : List[Decl]  = mod.functions.map {
            f => {
              ASTNode.introducePos(true, true, f, modFuncImport.position)
            }
          } ++ in
          // Add axioms related to functions
          
          val newAxioms : List[Decl] = mod.axioms.filter(a => isStatelessAndFunctionAxiom(a.expr, Scope.empty + mod))
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
  lazy val funcStatelessAxiomFinder = manager.pass("ModuleFunctionsStatelessAxiomFinderPass").asInstanceOf[ModuleFunctionsStatelessAxiomFinderPass]
  
  
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
    
    logger.debug("newImports: " + newImports.toString())
    val modP = Module(module.id, newImports ++ module.decls, module.cmds, module.notes)
    return Some(modP)
  }
}


class ModuleFunctionsStatelessAxiomFinderPass(mainModuleName : Identifier) extends StatelessAxiomFinderPass(mainModuleName : Identifier) {

  def isFunctionExpression(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) => 
        namedExpr match {
          case Scope.Function(_, _) => true
          case _ => false;
        }
      case None => {
        println("Unnamed expression :(")
        false
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
        rec.values.forall(e => isFunctionExpr(e, context))
      case OperatorApplication(ArraySelect(inds), args) =>
        inds.forall(ind => isFunctionExpr(ind, context)) &&
        args.forall(arg => isFunctionExpr(arg, context))
      case OperatorApplication(ArrayUpdate(inds, value), args) =>
        inds.forall(ind => isFunctionExpr(ind, context)) &&
        args.forall(arg => isFunctionExpr(arg, context)) &&
        isStatelessExpr(value, context)
      case opapp : OperatorApplication =>
        opapp.operands.forall(arg => isFunctionExpr(arg, context + opapp.op))
      case a : ConstArray =>
        isFunctionExpr(a.exp, context)
      case fapp : FuncApplication =>
        isFunctionExpr(fapp.e, context) && fapp.args.forall(a => isFunctionExpr(a, context))
      case lambda : Lambda =>
        isFunctionExpr(lambda.e, context + lambda)
    }
  }
    

  override def applyOnAxiom(d : TraversalDirection.T, axiom : AxiomDecl, in : T, context : Scope) : T = {
    if (in._1 && d == TraversalDirection.Down && super.isStatelessExpr(axiom.expr, context) &&
          isFunctionExpr(axiom.expr, context)) {
      //val moduleName = context.module.get.id
      //val exprP = rewriteToExternalIds(moduleName, axiom.expr, context)
      //val name = axiom.id match {
      //  case Some(id) => "_" + id.toString()
      //  case None => ""
      //}
      //val nameP = Identifier("$axiom_" + moduleName.toString + name + "_" + in._2.size.toString)
      //val axiomP = AxiomDecl(Some(nameP), exprP, axiom.params)
      
      // Do not rewrite the axioms
      (in._1, (context.module.get.id, axiom) :: in._2)
    } else {
      in
    }
  }
}

class ModuleFunctionsStatelessAxiomFinder(mainModuleName : Identifier) extends ASTAnalyzer(
  "ModuleFunctionsStatelessAxiomFinder", new ModuleFunctionsStatelessAxiomFinderPass(mainModuleName))
{
  override def reset() {
    in = Some((true, List.empty))
  }
}


class ModuleFunctionsStatelessAxiomImporterPass(mainModuleName : Identifier) extends RewritePass
{
  lazy val manager : PassManager = analysis.manager
  lazy val statelessAxiomFinder = manager.pass("ModuleFunctionsStatelessAxiomFinder").asInstanceOf[ModuleFunctionsStatelessAxiomFinder]
  override def rewriteModule(module : Module, context : Scope) : Option[Module] = {
    if (module.id == mainModuleName) {
    val axioms = statelessAxiomFinder.out.get._2
      val otherModuleAxioms = axioms.filter(p => p._1 != mainModuleName).map(p => p._2)
      val declsP = otherModuleAxioms ++ module.decls
      val moduleP = Module(module.id, declsP, module.cmds, module.notes)
      Some(moduleP)
    } else {
      Some(module)
    }
  }
}

class ModuleFunctionsStatelessAxiomImporter(mainModuleName : Identifier) extends ASTRewriter(
    "ModuleFunctionsStatelessAxiomImporter", new ModuleFunctionsStatelessAxiomImporterPass(mainModuleName))

  




    
