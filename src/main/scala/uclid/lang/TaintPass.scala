package uclid
package lang

object TaintVarMap {
  var map  = scala.collection.mutable.Map[Identifier, Identifier]()
  def insert(v: Identifier, v_taint: Identifier) = {
    map += (v -> v_taint)
    //UclidMain.println("MAP ins: " + map.toString())
  }

  def get(v: Identifier) = {
      //UclidMain.println("MAP get: " + map.toString())
      map.get(v)
  }
}

class TaintModulePass extends RewritePass {

    override def rewriteModule(moduleIn: Module, ctx: Scope) : Option[Module] = {

      val taint_var_decls: List[StateVarsDecl] = moduleIn.decls.filter(decl => decl match {
          case StateVarsDecl(_,_) => true
          case _ => false
      }).map(state_var_decl => state_var_decl match {
          case StateVarsDecl(ids,_) => {
            val taint_vars_ids = ids.map(id => {
              val id_new = Identifier(id.name + "_taint_var");
              TaintVarMap.insert(id, id_new);
              id_new
            })
            StateVarsDecl(taint_vars_ids, new BooleanType())
          }
          case _ => StateVarsDecl(List(), new BooleanType())

      })
      val new_module = Module(moduleIn.id, taint_var_decls ++ moduleIn.decls, moduleIn.cmds, moduleIn.notes)
      Some(new_module)

    }


}

class TaintNextPass extends RewritePass {

  def get_taint_vars(vars: List[BlockVarsDecl]) : List[BlockVarsDecl] = {
    vars.map(blkVarsDecl => {
      val taint_ids = blkVarsDecl.ids.map(id => {
        val taint_id = Identifier(id.name + "_taint_var")
        TaintVarMap.insert(id, taint_id)
        assert(TaintVarMap.get(id) == Some(taint_id))
        taint_id
      })
      BlockVarsDecl(taint_ids, new BooleanType)
    })
  }

  def generateTaintExpr(expr: Expr) : Option[Expr] = {
    expr match {
      // External identifiers/Fresh Literals not handled at the moment

      case Identifier(name) => {
        //UclidMain.println("HERE " + name)
        //UclidMain.println(TaintVarMap.get(Identifier(name)).toString())
        TaintVarMap.get(Identifier(name))
      }
      case FreshLit(_) => None
      case IntLit(_) => None
      case ConstArray(_,_) => None
      case StringLit(_) => None
      case Tuple(_) => None // Not handled
      case OperatorApplication(ArraySelect(_), _) |
           OperatorApplication(ArrayUpdate(_, _), _) =>
            throw new Utils.UnimplementedException("TODO: Implement tainting for arrays.")
      case OperatorApplication(RecordUpdate(_, _), _) =>
            throw new Utils.UnimplementedException("TODO: Implement tainting for records.")
      case OperatorApplication(_, operands) => {
        val opers = operands.map(expr => generateTaintExpr(expr)).flatten
        if (opers.length > 1)
          Some(OperatorApplication(DisjunctionOp(), opers))
        else
          Some(opers(0))
      }
      case FuncApplication(_,_) => None
      case Lambda(_,_) => None
      case _ => None

    }
  }

  def get_taint_assignment(assgn: (Lhs, Expr), precondition: List[Expr]) : Option[(Lhs, Expr)] = {
    val taint_var = assgn._1 match {
      case LhsId(id) => TaintVarMap.get(id)
      case LhsNextId(id) => TaintVarMap.get(id)
      case LhsArraySelect(id, _) => TaintVarMap.get(id)
      case LhsRecordSelect(id, _) => TaintVarMap.get(id)
      case LhsSliceSelect(id, _) => TaintVarMap.get(id)
      case LhsVarSliceSelect(id, _) => TaintVarMap.get(id)
    }

    val taint_exprs = (List(assgn._2) ++ precondition).map(expr => generateTaintExpr(expr)).flatten
    //UclidMain.println("LHS: " + assgn._1.asInstanceOf[LhsId].id.toString())
    //UclidMain.println("Rhs: " + assgn._2.toString())
    //UclidMain.println("Taint exprs" + taint_exprs.toString())
    if (taint_exprs.length == 0 || taint_var == None)
      None
    else
      Some(LhsId(taint_var.get), if (taint_exprs.length > 1) OperatorApplication(DisjunctionOp(), taint_exprs) else taint_exprs(0))

  }
  // Takes a statement as input and adds taint expressions to the statements recursively
  def addTaintToStatement(statement: Statement, precondition: List[Expr]): List[Statement] = {
    statement match {
      case BlockStmt(vars, stmts) => {
        val taint_vars = get_taint_vars(vars)
        val new_stmts = stmts.map(st => addTaintToStatement(st, precondition)).flatten
        List(BlockStmt(taint_vars ++ vars, new_stmts))
      }
      case HavocStmt(havocable) => {
        havocable match {
          case HavocableId(id) => {
            val taint_var = TaintVarMap.get(id).get
            val taint_assign = AssignStmt(List(LhsId(taint_var)), List(new BoolLit(false)))
            List(taint_assign, HavocStmt(havocable))
          }
          case HavocableNextId(id) => {
            val taint_var = TaintVarMap.get(id).get
            val taint_assign = AssignStmt(List(LhsId(taint_var)), List(new BoolLit(false)))
            List(taint_assign, HavocStmt(havocable))
          }
          case HavocableFreshLit(_) => List()
          case HavocableInstanceId(_) => throw new Utils.AssertionError("Should be no havocable instance ids at this point")
        }
      }
      case IfElseStmt(cond, ifblock, elseblock) => {
        val newif = addTaintToStatement(ifblock, precondition ++ List(cond))
        val newelse = addTaintToStatement(elseblock, precondition ++ List(cond))
        List(IfElseStmt(cond, newif(0), newelse(0))) // Assuming that ifblock and elseblock are block statements
      }
      case CaseStmt(body) => {
        // Assuming each statement is a block statment
        val new_body = body.map(x => (x._1, addTaintToStatement(x._2, precondition ++ List(x._1))(0)))
        List(CaseStmt(new_body))

      }
      case AssignStmt(lhss, rhss) => {
        val taint_exprs = lhss.zip(rhss).map(pair => get_taint_assignment(pair, precondition)).flatten
        val newlhss = lhss ++ taint_exprs.map(pair => pair._1)
        val newrhss = rhss ++ taint_exprs.map(pair => pair._2)
        List(AssignStmt(newlhss, newrhss))
      }
      case _ => List()

    }

  }

  override def rewriteNext(next: NextDecl, ctx: Scope) : Option[NextDecl] = {

    // Maintain a map from variables to taint variables
    // Add taint vars for each variable decl in BlockStmt
    // propagate taint vars for each statement

    val new_next = addTaintToStatement(next.body, List())
    Some(NextDecl(new_next(0)))
  }

}

class TaintModPass extends ASTRewriter(
  "TaintModulePass", new TaintModulePass())

class TaintNPass extends ASTRewriter(
  _passName = "TaintNextPass", new TaintNextPass())
