package uclid
package lang



class TaintPass extends RewritePass {

    override def rewriteModule(moduleIn: Module, ctx: Scope) : Option[Module] = {

      val taint_var_decls: List[StateVarsDecl] = moduleIn.decls.filter(decl => decl match {
          case StateVarsDecl(ids, typ) => true
          case _ => false
      }).map(state_var_decl => state_var_decl match {
          case StateVarsDecl(ids, typ) => {
            var taint_vars_ids = ids.map(id => Identifier(id.name + "_taint_var"))
            StateVarsDecl(taint_vars_ids, new BooleanType())
          }
          case _ => StateVarsDecl(List(), new BooleanType())

      })
      val new_module = Module(moduleIn.id, taint_var_decls ++ moduleIn.decls, moduleIn.cmds, moduleIn.notes)
      Some(new_module)

    }

}

class TaintVarPass extends ASTRewriter(
  "TaintVariablePass", new TaintPass())