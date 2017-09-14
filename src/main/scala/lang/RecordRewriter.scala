package uclid
package lang

import scala.collection.immutable.Set

class RecordRewriterPass(typechecker : TypecheckPass) extends RewritePass {
  override def reset() = {
    typechecker.reset()
  }

  def toTupleType(recType: RecordType) : TupleType = {
    TupleType(recType.fields.map(_._2))
  }
  
  def fieldNameToTupleIndex (recType : RecordType, field: Identifier) : Option[Identifier] = {
    recType.fieldIndex(field) match {
      case -1 => None
      case  i => Some(Identifier("_" + (i+1).toString()))
    }
  }
  
  override def rewriteType(typ : Type, ctx : ScopeMap) : Option[Type] = {
    typ match {
      case recType : RecordType => Some(toTupleType(recType))
      case _ => Some(typ)
    }
  }
  
  override def rewriteOperatorApp(opapp: OperatorApplication, ctx : ScopeMap) : Option[OperatorApplication] = {
    opapp.op match {
      case RecordSelect(r) =>
        val rec = opapp.operands(0)
        typechecker.typeOf(rec, ctx) match {
          case recTyp : RecordType => 
            Some(OperatorApplication(RecordSelect(fieldNameToTupleIndex(recTyp, r).get), opapp.operands))
          case _ =>
            Some(opapp)
        }
      case _ =>
        Some(opapp)
    }
  }
  
  override def rewriteLHS(lhs : Lhs, ctx : ScopeMap) : Option[Lhs] = {
    lhs.recordSelect match {
      case Some(fields) => 
        val idType = ctx.typeOf(lhs.id).get
        val foldInit : (Type, List[Identifier]) = (idType, List.empty[Identifier])
        val fieldsP = fields.foldLeft(foldInit)(
          (acc, fld) => {
            val prodType = acc._1.asInstanceOf[ProductType]
            val fldType = prodType.fieldType(fld).get
            val fldNameP = prodType match {
              case recType : RecordType =>
                fieldNameToTupleIndex(recType, fld).get
              case _ =>
                fld
            }
            (fldType, fldNameP::acc._2)
          }
        )
        Some(Lhs(lhs.id, lhs.arraySelect, Some(fieldsP._2.reverse), lhs.sliceSelect))
      case _ =>
        Some(lhs)
    }
  }
}

class RecordRewriter extends ASTRewriter(
    "RecordRewriter", new RecordRewriterPass(new TypecheckPass()))
