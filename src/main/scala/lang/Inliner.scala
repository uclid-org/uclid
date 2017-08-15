package uclid
package lang

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}
import scala.collection.immutable.Map
import scala.collection.immutable.Set

class FindLeafProceduresPass extends ReadOnlyPass[Set[IdGenerator.Id]] {
  var procedureMap = MutableMap.empty[IdGenerator.Id, ProcedureDecl]  
  override def reset() { 
    procedureMap.clear()
  }
  override def applyOnProcedure(d : TraversalDirection.T, proc : ProcedureDecl, in : Set[IdGenerator.Id], ctx : ScopeMap) : Set[IdGenerator.Id] = {
    if (d == TraversalDirection.Down) return in
    
    val hasProcedureCalls = proc.body.exists((st) => {
      st match {
        case ProcedureCallStmt(_,_,_) => true
        case _ => false
      }
    })
    if (!hasProcedureCalls) {
      procedureMap.put(proc.astNodeId, proc)
      return in + proc.astNodeId
    } else {
      return in
    }
  }
  def procedure(i : IdGenerator.Id) : ProcedureDecl = procedureMap.get(i).get
}

class FindLeafProcedures extends ASTAnalyzer("FindLeafProcedures", new FindLeafProceduresPass) {
  override def pass : FindLeafProceduresPass = super.pass.asInstanceOf[FindLeafProceduresPass]
  in = Some(Set.empty)
  override def reset() {
    in = Some(Set.empty)
  }
  
  // Mainly for debugging.
  def printLeafProcedures() {
    out match {
      case Some(list) => println("Found some leaf procedures.")
                         list.foreach{ (astNodeId) => println("--> " + pass.procedure(astNodeId).id.toString) }
      case None       => println("No leaf procedures. (ERROR!)")
    }
  }
}

class InlineProcedurePass(proc : ProcedureDecl) extends RewritePass {
  type UniqueNameProvider = (Identifier, String) => Identifier
  class ContextualNameProvider(ctx : ScopeMap, prefix : String) {
    var assignedNames = MutableSet.empty[Identifier] 
    def apply(name: Identifier, tag : String) : Identifier = {
      var newId = Identifier(prefix + "$" + tag + "$" + name)
      var index = 0
      while (ctx.doesNameExist(newId)) {
        index = index + 1
        newId = Identifier(prefix + "$" + tag + "$" + name + "$" + index.toString)
      }
      return newId
    }
  }
  
  override def rewriteProcedure(p : ProcedureDecl, ctx : ScopeMap) : Option[ProcedureDecl] = {
    val nameProvider = new ContextualNameProvider(ctx + p, "proc$" + p.id + "$" + proc.id)
    val (stmts, newVars) = inlineProcedureCalls((id, p) => nameProvider(id, p), proc.body)
    val newDecls = newVars.map((t) => LocalVarDecl(t._1, t._2))
    return Some(ProcedureDecl(p.id, p.sig, p.decls ++ newDecls, stmts))
  }
  
  override def rewriteModule(m : Module, ctx : ScopeMap) : Option[Module] = {
    val initNameProvider = new ContextualNameProvider(ctx, "init$" + proc.id)
    val nextNameProvider = new ContextualNameProvider(ctx, "next$" + proc.id)
    
    val decls = m.decls.foldLeft((List.empty[Decl], List.empty[StateVarDecl]))((acc, decl) => {
      decl match {
        case InitDecl(body) => 
          val (stmts, vars) = inlineProcedureCalls((id, p) => initNameProvider(id, p), body)
          (acc._1 ++ List(InitDecl(stmts)), acc._2 ++ vars.map((t) => StateVarDecl(t._1, t._2)))
        case NextDecl(body) => 
          val (stmts, vars) = inlineProcedureCalls((id, p) => nextNameProvider(id, p), body)
          (acc._1 ++ List(NextDecl(stmts)), acc._2 ++ vars.map((t) => StateVarDecl(t._1, t._2)))
        case stmt =>
          (acc._1 ++ List(stmt), acc._2)
      }
    })
    return Some(Module(m.id, decls._2 ++ decls._1, m.cmds))
  }
  
  def inlineProcedureCalls(uniqNamer : UniqueNameProvider, stmts : List[Statement]) : (List[Statement], List[(Identifier, Type)]) = {
    val init = (List.empty[Statement], List.empty[(Identifier, Type)])
    // we walk through the list of statements accumulating inlined procedures and new declarations.
    return stmts.foldLeft(init)((acc, stmt) => {
      stmt match {
        case ProcedureCallStmt(id, lhss, args) =>
          if (id != proc.id) {
            (acc._1 ++ List(stmt), acc._2) 
          }
          // Sanity check.
          Utils.assert(args.size == proc.sig.inParams.size, "Incorrect number of arguments to procedure: " + proc.id)
          Utils.assert(lhss.size == proc.sig.outParams.size, "Incorrect number of return values from procedure: " + proc.id)
          // what are the arguments?
          val argVars : List[Identifier] = proc.sig.inParams.map(_._1)
          // return values original names.
          var retVars : List[Identifier] = proc.sig.outParams.map(_._1)
          // new variables for the return values.
          var retNewVars : List[(Identifier, Type)] = proc.sig.outParams.map((r) => (uniqNamer(r._1, "ret"), r._2))
          // new variables for the local variables.
          val localNewVars : List[(Identifier, Type)] = proc.decls.map((v) => (uniqNamer(v.id, "loc"), v.typ))
          // map procedure formal arguments to actual
          val mEmpty = Map.empty[Expr, Expr]
          val mArgs = (argVars zip args).foldLeft(mEmpty)((map, t) => map + (t._1 -> t._2))
          val mRet  = (retVars zip retNewVars).foldLeft(mEmpty)((map, t) => map + (t._1 -> t._2._1))
          val mLocal = (proc.decls zip localNewVars).foldLeft(mEmpty)((map, t) => map + (t._1.id -> t._2._1))
          val resultAssignStatment = AssignStmt(lhss, retNewVars.map(_._1))
          val rewriteMap = mArgs ++ mRet ++ mLocal
          val rewriter = new ExprRewriter("ProcedureInlineRewriter", rewriteMap)
          (acc._1 ++ rewriter.rewriteStatements(proc.body) ++ List(resultAssignStatment), acc._2 ++ retNewVars ++ localNewVars)
        case _ => (acc._1 ++ List(stmt), acc._2)
      }
    })
  }
}

class TupleFlattenerPass extends RewritePass {
  def rewriteTuple(id : Identifier, typ : Type) : List[(Identifier, Type)] = {
    typ match {
      case RecordType(fields) => fields.map{ (f) => (Identifier(id + "_$field$_" + f._1.value), f._2) }
      case TupleType(fields) => fields.zipWithIndex.map{ case (f, i) => (Identifier(id.value + "_$tuple$_" + i.toString), f) }
      case _ => List((id, typ))
    }
  }
  
  override def rewriteModule(module: Module, ctx : ScopeMap) : Option[Module] = {
    val newDecls : List[Decl] = module.decls.flatMap{ (decl) =>
      decl match {
        case StateVarDecl(id, typ) => rewriteTuple(id, typ).map((t) => StateVarDecl(t._1, t._2))
        case InputVarDecl(id, typ) => rewriteTuple(id, typ).map((t) => InputVarDecl(t._1, t._2))
        case OutputVarDecl(id, typ) => rewriteTuple(id, typ).map((t) => OutputVarDecl(t._1, t._2))
        case ConstantDecl(id, typ) => rewriteTuple(id, typ).map((t) => ConstantDecl(t._1, t._2))
        case FunctionDecl(id, sig) => throw new Utils.UnimplementedException("TODO")
        case _ => List(decl)
      }
    }
    return Some(Module(module.id, newDecls, module.cmds))
  }
}
class TupleFlattener extends ASTRewriter("TupleExpander", new TupleFlattenerPass())
