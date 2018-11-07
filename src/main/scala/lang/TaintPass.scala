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
          case StateVarsDecl(ids, typ) => true
          case _ => false
      }).map(state_var_decl => state_var_decl match {
          case StateVarsDecl(ids, typ) => {
            var taint_vars_ids = ids.map(id => {
              var id_new = Identifier(id.name + "_taint_var");
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
      var taint_ids = blkVarsDecl.ids.map(id => {
        var taint_id = Identifier(id.name + "_taint_var")
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
      case FreshLit(typ) => None
      case IntLit(int) => None
      case ConstArray(l, typ) => None
      case StringLit(v) => None
      case Tuple(values) => None // Not handled
      case OperatorApplication(op, operands) => {
        var opers = operands.map(expr => generateTaintExpr(expr)).flatten
        if (opers.length > 1)
          Some(OperatorApplication(DisjunctionOp(), opers))
        else
          Some(opers(0))
      }
      case ArraySelectOperation(e, index) => {
        var taint_exprs = (List(generateTaintExpr(e)) ++ index.map(expr => generateTaintExpr(expr))).flatten
        if (taint_exprs.length > 1)
          Some(OperatorApplication(DisjunctionOp(), taint_exprs))
        else
          Some(taint_exprs(0))
      }
      case ArrayStoreOperation(e, index, value) => {
        var taint_exprs = (List(generateTaintExpr(e)) ++ index.map(expr => generateTaintExpr(expr))).flatten
        if (taint_exprs.length > 1)
          Some(OperatorApplication(DisjunctionOp(), taint_exprs))
        else
          Some(taint_exprs(0))
      }
      case FuncApplication(e, args) => None
      case Lambda(ids, e) => None
      case _ => None

    }
  }

  def get_taint_assignment(assgn: (Lhs, Expr), precondition: List[Expr]) : Option[(Lhs, Expr)] = {
    var taint_var = assgn._1 match {
      case LhsId(id) => TaintVarMap.get(id)
      case LhsNextId(id) => TaintVarMap.get(id)
      case LhsArraySelect(id, indices) => TaintVarMap.get(id)
      case LhsRecordSelect(id, fields) => TaintVarMap.get(id)
      case LhsSliceSelect(id, bitslice) => TaintVarMap.get(id)
      case LhsVarSliceSelect(id, bitslice) => TaintVarMap.get(id)
    }

    var taint_exprs = (List(assgn._2) ++ precondition).map(expr => generateTaintExpr(expr)).flatten
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
        var taint_vars = get_taint_vars(vars)
        var new_stmts = stmts.map(st => addTaintToStatement(st, precondition)).flatten
        List(BlockStmt(taint_vars ++ vars, new_stmts))
      }
      case HavocStmt(havocable) => {
        havocable match {
          case HavocableId(id) => {
            var taint_var = TaintVarMap.get(id).get
            var taint_assign = AssignStmt(List(LhsId(taint_var)), List(new BoolLit(false)))
            List(taint_assign, HavocStmt(havocable))
          }
          case HavocableNextId(id) => {
            var taint_var = TaintVarMap.get(id).get
            var taint_assign = AssignStmt(List(LhsId(taint_var)), List(new BoolLit(false)))
            List(taint_assign, HavocStmt(havocable))
          }
          case HavocableFreshLit(f) => List()
        }
      }
      case IfElseStmt(cond, ifblock, elseblock) => {
        var newif = addTaintToStatement(ifblock, precondition ++ List(cond))
        var newelse = addTaintToStatement(elseblock, precondition ++ List(cond))
        List(IfElseStmt(cond, newif(0), newelse(0))) // Assuming that ifblock and elseblock are block statements
      }
      case CaseStmt(body) => {
        // Assuming each statement is a block statment
        var new_body = body.map(x => (x._1, addTaintToStatement(x._2, precondition ++ List(x._1))(0)))
        List(CaseStmt(new_body))

      }
      case AssignStmt(lhss, rhss) => {
        var taint_exprs = lhss.zip(rhss).map(pair => get_taint_assignment(pair, precondition)).flatten
        var newlhss = lhss ++ taint_exprs.map(pair => pair._1)
        var newrhss = rhss ++ taint_exprs.map(pair => pair._2)
        List(AssignStmt(newlhss, newrhss))
      }
      case _ => List()

    }

  }

  override def rewriteNext(next: NextDecl, ctx: Scope) : Option[NextDecl] = {

    // Maintain a map from variables to taint variables
    // Add taint vars for each variable decl in BlockStmt
    // propagate taint vars for each statement

    var new_next = addTaintToStatement(next.body, List())
    Some(NextDecl(new_next(0)))
  }

}

class TaintModPass extends ASTRewriter(
  "TaintModulePass", new TaintModulePass())

class TaintNPass extends ASTRewriter(
  _passName = "TaintNextPass", new TaintNextPass())