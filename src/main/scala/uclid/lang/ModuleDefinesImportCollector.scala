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
 * Author: Pranav Gaddamadugu
 * Rewrite define * = moduleId.*; declarations.
 *
 * Note: Only stateless define declarations are collected.
 *
 */



package uclid
package lang

import com.typesafe.scalalogging.Logger

/**
 * A ReadOnlyPass that collects 'define' declarations from a target module.
 *
 */
class ModuleDefinesImportCollectorPass extends ReadOnlyPass[List[Decl]] {
  lazy val logger = Logger(classOf[ModuleDefinesImportCollector])
  type T = List[Decl]
  
  /*
   * Checks that an identifier, in a specific context, does not reference any 
   * state variables.
   *
   * @param id Name of the expression
   * @param context Current scope
   *
   */
  def isStatelessIdentifier(id : Identifier, context : Scope) : Boolean = {
    context.get(id) match {
      case Some(namedExpr) =>
        namedExpr match {
          case Scope.StateVar(_, _)    | Scope.InputVar(_, _)  |
               Scope.OutputVar(_, _)   | Scope.SharedVar(_, _) |
               Scope.Instance(_)       =>
             false
          case Scope.ConstantVar(_, _)    | Scope.Function(_, _)       |
               Scope.LambdaVar(_ , _)     | Scope.ForallVar(_, _)      |
               Scope.ExistsVar(_, _)      | Scope.EnumIdentifier(_, _) |
               Scope.FunctionArg(_, _)    | Scope.Define(_, _, _) |
               Scope.ConstantLit(_, _)    | Scope.SynthesisFunction(_, _, _, _, _) =>
             true
          case Scope.ModuleDefinition(_)      | Scope.Grammar(_, _, _)             |
               Scope.TypeSynonym(_, _)        | Scope.Procedure(_, _)           |
               Scope.ProcedureInputArg(_ , _) | Scope.ProcedureOutputArg(_ , _) |
               Scope.ForIndexVar(_ , _)       | Scope.SpecVar(_ , _, _)         |
               Scope.AxiomVar(_ , _, _)       | Scope.VerifResultVar(_, _)      |
               Scope.BlockVar(_, _)           | Scope.SelectorField(_)          =>
             throw new Utils.ParserError("Can't have this identifier in define declaration: " + namedExpr.toString(), None, None)
        }
      case None =>
        throw new Utils.UnknownIdentifierException(id)
    }
  }

  /*
   * Checks that an expression does not reference any state variables.
   *
   * @param e The expression being checked
   * @param context The current scope
   */
  def isStatelessExpr(e: Expr, context : Scope) : Boolean = {
    e match {
      case id : Identifier =>
        isStatelessIdentifier(id, context)
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
  
  /*
   * Collects define declarations from a module.
   *
   * @param d Direction of AST traversal
   * @param modDefImport Import declaration
   * @param in HashMap[Identifier, Identifier]
   * @param context Scope containing ModuleDefinitions
   */
  override def applyOnModuleDefinesImport(d : TraversalDirection.T, modDefImport : ModuleDefinesImportDecl, in : T, context : Scope) : T = {
    if (d == TraversalDirection.Up) {
      //logger.debug("statement: {}", modFuncImport.toString())
      val id = modDefImport.id
      context.map.get(id) match {
        case Some(Scope.ModuleDefinition(mod)) => {
          val newDefs : List[Decl]  = mod.defines.filter(d => isStatelessExpr(d.expr, (Scope.empty + mod) + d.sig)) ++ in
          newDefs
        } 
        case _ => throw new Utils.ParserError(s"Trying to import from a module that does not exist: ${id}", None, None)
      }
    } else {
      in
    }
  }
}

/*
 * Introduces new define declarations into the module calling the import
 *
 */
class ModuleDefinesImportCollector extends ASTAnalyzer("ModuleDefinesImportCollector", new ModuleDefinesImportCollectorPass()) {
  lazy val logger = Logger(classOf[ModuleDefinesImportCollector])
  
  override def reset() {
    in = Some(List.empty)
  }

  /*
   * Explictly adds a collected list of define declarations to a module
   *
   * @param module The module to be visited
   * @param context The context of the current module (technically accumulated
   *    by the PassManager)
   */
  override def visit(module : Module, context : Scope) : Option[Module] = {
    val externalDefs = visitModule(module, List.empty, context)
    val newImports = externalDefs.map {
      d => {
        d match {
          case d : DefineDecl => ASTNode.introducePos(true, true, d, d.position)
          case _ => throw new Utils.RuntimeError("Should not have anything but define declarations.")
        }
      }
    }
    
    val modP = Module(module.id, newImports ++ module.decls, module.cmds, module.notes)
    return Some(modP)
  }
}




