package uclid
package lang

class RecordRewriterPass(recType : RecordType, typecheckerPass : TypecheckPass) extends RewritePass {
  val tupType = TupleType(recType.fields.map(_._2))
  def fieldNameToTupleIndex (field: Identifier) : Option[Identifier] = {
    recType.fieldIndex(field) match {
      case -1 => None
      case  i => Some(Identifier("_" + (i+1).toString()))
    }
  }
  
  override def rewriteType(typ : Type, ctx : ScopeMap) : Option[Type] = {
    if (typ == recType) {
      Some(tupType)
    } else {
      Some(typ)
    }
  }
  override def rewriteOperatorApp(opapp: OperatorApplication, ctx : ScopeMap) : Option[OperatorApplication] = {
    opapp.op match {
      case RecordSelect(r) => 
        val rec = opapp.operands(0)
        val typ = typecheckerPass.typeOf(rec, ctx)
        if (typ == recType) {
          Some(OperatorApplication(RecordSelect(fieldNameToTupleIndex(r).get), opapp.operands))
        } else {
          Some(opapp)
        }
      case _ =>
        Some(opapp)
    }
  }
}

