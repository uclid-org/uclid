/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Pramod Subramanyan
 *
 * Replace a.b with the appropriate select operator.
 *
 */

package uclid
package lang

// this must be run after user defined types are resolved, otherwise we can't tell what is a record and 
// what is a tuple
class RewriteRecordSelectPass extends RewritePass {

  override def rewriteRecordType(recordT : RecordType, context : Scope) : Option[RecordType] = { 
    val newMembers = recordT.members.map{case (i: Identifier, t:Type) => (Identifier("_rec_"+i.toString), t)}
    Some(RecordType(newMembers))
  }

  override def rewriteLHS(lhs : Lhs, context : Scope) : Option[Lhs] = {
    lhs match {
      case LhsRecordSelect(id, fields) => 
        val newFields = fields.map{case i: Identifier => Identifier("_rec_"+i.toString)}
        Some(LhsRecordSelect(id, newFields))
      case _ => Some(lhs)
    }
  }

  // def rewriteRecordFields(id: Identifier, opapp: OperatorApplication, t: Type) : Option[OperatorApplication] = {
  //   if(t.isRecord)
  //     Some(OperatorApplication(PolymorphicSelect(Identifier("_rec_"+id.toString)), List(opapp.operands(0))))
  //   else
  //     Some(opapp)
  // }

  def rewriteRecordFields(selectid: Identifier, argid: Identifier, opapp: OperatorApplication, context: Scope) : Option[OperatorApplication] = {
    val isRecord = context.map.get(argid) match {
      case Some(Scope.StateVar(i,t)) => t.isRecord
      case Some(Scope.ProcedureInputArg(i,t)) => t.isRecord
      case Some(Scope.ProcedureOutputArg(i,t)) => t.isRecord
      case Some(Scope.BlockVar(i,t)) => t.isRecord
      case Some(Scope.FunctionArg(i,t)) => t.isRecord
      case Some(Scope.LambdaVar(i,t)) => t.isRecord
      case _ => false
    }
    if(isRecord)
      Some(OperatorApplication(PolymorphicSelect(Identifier("_rec_"+selectid.toString)), List(opapp.operands(0))))
    else
     Some(opapp)
  }

  def getBaseIdentifier(expr: Expr) : Option[Identifier] = {
    expr match{
      case Identifier(_) => Some(expr.asInstanceOf[Identifier])
      case ExternalIdentifier(mid, id) => Some(id)
      case OperatorApplication(op, operands) => 
        if(operands.size==1)
          getBaseIdentifier(operands(0))
        else
          None
      case _ => None
    }
  }


  // rename record fields
  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    opapp.op match {
      case PolymorphicSelect(id) =>
        val expr = opapp.operands(0)
        expr match {
          case arg : Identifier =>
            rewriteRecordFields(id, arg, opapp, context)
          case opapp2 : OperatorApplication  => 
          // this is probably a primed var
              val baseId = getBaseIdentifier(opapp2)
              if(baseId.isDefined)
              {
                newOpApp2 = rewriteRecordFields(id, baseId.get, opapp, context)
              }
              else
                Some(opapp)
          case _ => 
          Some(opapp)
        }
      case _ => 
        Some(opapp)
    }
  }
}

class RewriteRecordSelect extends ASTRewriter(
    "RewriteRecordSelect", new RewriteRecordSelectPass())

class RewritePolymorphicSelectPass extends RewritePass {

  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    opapp.op match {
      case PolymorphicSelect(id) =>
        val expr = opapp.operands(0)
        expr match {
          case arg : Identifier =>
            context.map.get(arg) match {
              case Some(Scope.ModuleDefinition(_)) => Some(ExternalIdentifier(arg, id))
              case _ =>        
              Some(opapp)
            }
          case _ => Some(opapp)
        }
      case _ => Some(opapp)
    }
  }
}

class RewritePolymorphicSelect extends ASTRewriter(
    "RewritePolymorphicSelect", new RewritePolymorphicSelectPass())