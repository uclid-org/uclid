package uclid
package lang
class RewriteRecordSelectPass extends RewritePass {

  def recordPrefix = "_rec_"

  def hasRecPrefix(field: (Identifier,Type)) = field._1.toString.startsWith(recordPrefix)

  override def rewriteRecordType(recordT : RecordType, context : Scope) : Option[RecordType] = { 
    if(recordT.members.filter(hasRecPrefix).size!=recordT.members.size)
    {
      val newMembers = recordT.members.map{case (i: Identifier, t:Type) => (Identifier(recordPrefix+i.toString), t)}
      //print("we have rewritten this record type " + recordT.toString + " to have members " + newMembers.toString)
      Some(RecordType(newMembers))
    }
    else
    {
      UclidMain.printDebugRewriteRecord("we have not rewritten this record type " + recordT.toString )
      Some(recordT)
    }
  }

  override def rewriteDataType(dataT : DataType, context : Scope) : Option[DataType] = { 
    Some(DataType(dataT.id, dataT.constructors.map(c => (c._1, c._2.map(s => {
      if(!hasRecPrefix(s))
      {
        (Identifier(recordPrefix+s._1.toString), s._2)
      }
      else
      {
        UclidMain.printDebugRewriteRecord("we have not rewritten this selector " + dataT.toString )
        s
      }
    })))))
  }
}

class RewriteRecordSelect extends ASTRewriter(
    "RewriteRecordSelect", new RewriteRecordSelectPass())