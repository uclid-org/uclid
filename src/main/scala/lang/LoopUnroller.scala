package uclid
package lang

class FindInnermostLoopsPass extends ReadOnlyPass[Set[IdGenerator.Id]] {
  override def applyOnFor(d : TraversalDirection.T, st : ForStmt, in : Set[IdGenerator.Id], context : ScopeMap) : Set[IdGenerator.Id] = {
    if(!st.body.exists(_.isLoop)) {
      in + st.astNodeId
    } else {
      in
    }
  }
}

class ForLoopRewriterPass(forStmts: Set[IdGenerator.Id]) extends RewritePass {
  def rewriteForStatement(st: ForStmt) : List[Statement] = {
     if (forStmts.contains(st.astNodeId)) {
       val low = st.range._1.value
       val high = st.range._2.value
       def rewriteForValue(value : BigInt) : List[Statement] = {
         val rewriteMap = Map.empty[Expr, Expr] + (st.id -> IntLit(value))
         val rewriter = new ExprRewriter("ForRewriter(i)", rewriteMap)
         rewriter.rewriteStatements(st.body)
       }
       (low to high).foldLeft(List.empty[Statement])((acc, i) => acc ++ rewriteForValue(i))
     } else {
       List(st)
     }
  }
  def rewriteStatement(stmt: Statement) : List[Statement] = {
    stmt match {
      case st : ForStmt => rewriteForStatement(st)
      case _            => List(stmt)
    }
  }
  override def rewriteProcedure(proc : ProcedureDecl, ctx : ScopeMap) : Option[ProcedureDecl] = {
    val bodyP = proc.body.flatMap(rewriteStatement(_))
    return Some(ProcedureDecl(proc.id, proc.sig, proc.decls, bodyP))
  }
  override def rewriteInit(init : InitDecl, ctx : ScopeMap) : Option[InitDecl] = { 
    val bodyP = init.body.flatMap(rewriteStatement(_))
    return Some(InitDecl(bodyP))
  }
  override def rewriteNext(next : NextDecl, ctx : ScopeMap) : Option[NextDecl] = { 
    val bodyP = next.body.flatMap(rewriteStatement(_))
    return Some(NextDecl(bodyP))
  }
}

class ForLoopUnroller extends ASTAnalysis {
  var findInnermostLoopsPass = new FindInnermostLoopsPass()
  var findInnermostLoopsAnalysis = new ASTAnalyzer("ForLoopUnroller.FindInnermostLoops", findInnermostLoopsPass)
  var _astChanged = false 
  
  override def passName = "ForLoopUnroller"
  override def reset() = {
    findInnermostLoopsAnalysis.reset()
    _astChanged = false
  }
  override def astChanged = _astChanged
  def visit(module : Module) : Option[Module] = {
    _astChanged = false
    var modP : Option[Module] = Some(module)
    var iteration = 0
    var done = false
    val MAX_ITERATIONS = 100
    do {
      findInnermostLoopsAnalysis.reset()
      modP match {
        case None => 
          done = true
        case Some(mod) =>
          val innermostLoopSet = findInnermostLoopsAnalysis.visitModule(mod, Set.empty[IdGenerator.Id])
          println("Innermost loops: " + innermostLoopSet.toString)
          done = innermostLoopSet.size == 0
          if (!done) {
            _astChanged = true
            val forLoopRewriter = new ASTRewriter("ForLoopUnroller.LoopRewriter", new ForLoopRewriterPass(innermostLoopSet))
            modP = forLoopRewriter.visit(mod)
            if(!modP.isEmpty) {
              println("** AFTER UNROLLING **")
              println(modP.get)
            }
          }
      }
      iteration = iteration + 1
    } while(!done && iteration < MAX_ITERATIONS)
    Utils.assert(iteration < MAX_ITERATIONS, "Too many rewriting iterations.")
    return modP
  }
}