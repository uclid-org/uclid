package uclid
package lang

class FindInnermostLoopsPass extends ReadOnlyPass[Set[ForStmt]] {
  override def applyOnFor(d : TraversalDirection.T, st : ForStmt, in : Set[ForStmt], context : ScopeMap) : Set[ForStmt] = {
    if(!st.body.exists(_.isLoop)) {
      in + st
    } else {
      in
    }
  }
}

class ForLoopRewriterPass(forStmtsToRewrite: Set[ForStmt]) extends RewritePass {
  override def rewriteFor(st: ForStmt, ctx : ScopeMap) : List[Statement] = {
     if (forStmtsToRewrite.contains(st)) {
       val low = st.range._1
       val high = st.range._2
       def rewriteForValue(value : NumericLit) : List[Statement] = {
         val rewriteMap = Map.empty[Expr, Expr] + (st.id -> value)
         val rewriter = new ExprRewriter("ForRewriter(i)", rewriteMap)
         rewriter.rewriteStatements(st.body)
       }
       (low to high).foldLeft(List.empty[Statement])((acc, i) => acc ++ rewriteForValue(i))
     } else {
       List(st)
     }
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
          val innermostLoopSet = findInnermostLoopsAnalysis.visitModule(mod, Set.empty[ForStmt])
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