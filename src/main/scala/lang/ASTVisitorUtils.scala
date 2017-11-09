/*
 * UCLID5
 * 
 * Author : Pramod Subramanyan
 * 
 * A couple of AST-handling utilities.
 *   (i) ASTPrinterPass  : Prints out the module
 *  (ii) ExprRewriterPas : Replaces all instances of an expression with another. 
 */
package uclid
package lang

/** Very simple pass too print module. */
class ASTPrinterPass extends ReadOnlyPass[Unit] {
  override def applyOnModule(d : TraversalDirection.T, module : Module, in : Unit, context : ScopeMap) : Unit = {
    if (d == TraversalDirection.Down) {
      println(module)
    }
  }
}
/** Simple analysis that instantiates ASTPrinterPass to print module. */
class ASTPrinter(name: String) extends ASTAnalyzer(name, new ASTPrinterPass()) {
  override def pass = super.pass.asInstanceOf[ASTPrinterPass]
  in = Some(Unit)
}

class ExprRewriterPass(rewrites : Map[Expr, Expr]) extends RewritePass
{
  override def rewriteExpr(e: Expr, context: ScopeMap) : Option[Expr] = {
    rewrites.get(e) match {
      case Some(eprime) => Some(eprime)
      case None => Some(e)
    }
  }
  override def rewriteIdentifier(i: Identifier, context: ScopeMap) : Option[Identifier] = {
    rewrites.get(i) match {
      case None => Some(i)
      case Some(eprime) => eprime match {
        case idprime : Identifier => Some(idprime)
        case _ => Some(i)
      }
    }
  }
}

class ExprRewriter(name: String, rewrites : Map[Expr, Expr]) 
  extends ASTRewriter(name, new ExprRewriterPass(rewrites))
{
  def rewriteStatements(stmts : List[Statement]) : List[Statement] = {
    val emptyContext = ScopeMap.empty
    return stmts.flatMap(visitStatement(_, emptyContext))
  }
}
