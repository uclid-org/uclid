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



class RewritePolymorphicSelectPass extends RewritePass {
  def recordPrefix = "_rec_"
  override def rewriteOperatorApp(opapp : OperatorApplication, context : Scope) : Option[Expr] = {
    UclidMain.printDetailedStats("Try to rewrite "+opapp+"\n")
    opapp.op match {
      //[linedata := 2022]
      case RecordUpdate(id,e)=>
        {
          val newOpApp = Some(OperatorApplication(RecordUpdate(Identifier(recordPrefix+id.toString),e),List(opapp.operands(0))))
          UclidMain.printDetailedStats("it is rewriten to "+opapp+"\n")
          newOpApp
        }
        // (__).(___)
      case PolymorphicSelect(id) =>
        val expr = opapp.operands(0)    
        expr match {
          // x.x
          case arg : Identifier =>
            context.map.get(arg) match {
              case Some(Scope.ModuleDefinition(_)) =>
                Some(ExternalIdentifier(arg, id))
              case _ =>
              {
                if(isVarState(arg,id,context)){
                  val newOpApp = Some(OperatorApplication(PolymorphicSelect(Identifier(recordPrefix+id.toString)), List(opapp.operands(0))))
                  UclidMain.printDetailedStats("it is rewriten to "+opapp+"\n")
                  newOpApp
                }
                else{
                  Some(opapp)
                }
              }
                
            }
          // (x.x).x
          case subopp: OperatorApplication =>{
            if(RewriterAble(subopp,context)){
              val newOpApp = Some(OperatorApplication(PolymorphicSelect(Identifier(recordPrefix+id.toString)), List(opapp.operands(0))))
              UclidMain.printDetailedStats("it is rewriten to "+opapp+"\n")
              newOpApp
            }
            else
              Some(opapp)
          }
          // ConstRecord{ ...}.x
          case ConstRecord(_) | ExternalIdentifier(_,_) |FuncApplication(_,_)=>
          {
            val newOpApp = Some(OperatorApplication(PolymorphicSelect(Identifier(recordPrefix+id.toString)), List(opapp.operands(0))))
            UclidMain.printDetailedStats("it is rewriten to "+opapp+"\n")
            newOpApp
          }
          //common.random().x
          case _ =>
          Some(opapp)
        }
      case _ => Some(opapp)
    }
  }

  def RewriterAble(opapp : OperatorApplication, context:Scope): Boolean = {
    opapp.op match {
      case PolymorphicSelect(id) =>
        val expr = opapp.operands(0)
        expr match {
          case arg : Identifier => isVarState(arg,id,context)||isVarInModule(id,arg,context)
          case subopp: OperatorApplication =>{
            if(RewriterAble(subopp,context))
              true
            else
            {
              val LastInstance = getLastInstance(subopp,context);
              LastInstance match{
                case mid : Identifier => isVarInModule(id,mid,context)
                case _ => false
              }
            }
          }
          case _ => false
        }
      //such as:
      // cache[0]
      case _ => {
        val expr = opapp.operands(0)
        expr match {
          case arg : Identifier => isVarState(arg,Identifier(""),context)
          case subopp: OperatorApplication =>
            RewriterAble(subopp,context)
          case _ => false
        }  
      }
    }
  }

  def checkIdDecl(decls:List[Decl],id:Identifier): Option[Identifier] ={
    decls match{
      case decl::otherdecls =>{
        decl match{
          case inst : InstanceDecl =>
          if(inst.instanceId == id){
            Some(inst.moduleId)
          }
          else{
            checkIdDecl(otherdecls,id)
          }
          case vardecl : StateVarsDecl =>
          if(vardecl.ids.head == id){
            Some(vardecl.ids.head)
          }
            
          else{
            checkIdDecl(otherdecls,id)
          }
          case _ => checkIdDecl(otherdecls,id)
        }
      }
      case List() => None
    }
  }
  def getLastInstance(opapp : OperatorApplication, context:Scope): Expr ={
    opapp.op match {
      case PolymorphicSelect(id) =>{
        opapp.operands(0) match {
          case arg : Identifier =>
            { 
              context.map.get(arg) match 
              {
              case Some(module:Scope.ModuleDefinition) => {
                checkIdDecl(module.mod.decls,id) match{
                    case Some(ident) => ident
                    case _ => opapp
                  }
              }
              case Some(Scope.Instance(instD)) => {
                context.map.get(instD.moduleId) match{
                  case Some(module:Scope.ModuleDefinition) =>
                  {
                  
                     checkIdDecl(module.mod.decls,id) match{
                      case Some(ident) => ident
                      case _ => opapp
                    }
                  }
                  case _ => opapp
                }
              }
              case _ => opapp
              }
            }
          case subopp: OperatorApplication =>{
            val expr = getLastInstance(subopp,context);
            expr match{
              case arg : Identifier =>
            { 
              context.map.get(arg) match 
              {
                case Some(module:Scope.ModuleDefinition) => {
                  checkIdDecl(module.mod.decls,id) match{
                    case Some(ident) => ident
                    case _ => opapp
                  }
                }
                case Some(Scope.Instance(instD)) => {
                  context.map.get(instD.moduleId) match{
                    case Some(module:Scope.ModuleDefinition) =>
                    {
                      checkIdDecl(module.mod.decls,id) match{
                        case Some(ident) => ident
                        case _ => opapp
                      }
                    }
                    case _ => opapp
                  }
                }
                case _ => opapp
              }
            }
              case _ => opapp
            }
          }
          case _ => opapp
        }
      }
      case GetNextValueOp() =>  
        val expr = opapp.operands(0)     
        expr match {
          case subopp: OperatorApplication =>
            getLastInstance(subopp,context)
          case _ => opapp
        }
      case _ => opapp
    }
  }

  def isVarInModule(id:Identifier,mid:Identifier,context:Scope): Boolean ={
    val IdentifierType = context.map.get(mid)
    IdentifierType match 
    {
      //if (module.var).,then it is okey
      case Some(module:Scope.ModuleDefinition) => {
           val match_var = Identifier(id.toString)
           lazy val vars : List[Identifier] =
          module.mod.decls.collect { case vars : StateVarsDecl => vars }.flatMap(v => v.ids.map(id => id))
          vars.contains(id)
        }
        //if (instance.var).,then it is okey
      case Some(Scope.Instance(instD)) => {
          context.map.get(instD.moduleId) match{
            case Some(model:Scope.ModuleDefinition) =>
            {
              val match_var = Identifier(id.toString)
              lazy val vars : List[Identifier] =
               model.mod.decls.collect { case vars : StateVarsDecl=> vars }.flatMap(v => v.ids.map(id => id))
              vars.contains(id)
             }
             case _ => false
           }
         }
      case _ => false        
    }
  }
  
  def isVarState(arg: Identifier,id:Identifier,context:Scope): Boolean = {
    UclidMain.printDetailedStats("We are going to check "+arg+"\n")
    UclidMain.printDetailedStats("its type is "+context.map.get(arg)+"\n")
    context.map.get(arg) match{
      case  Some(Scope.ProcedureInputArg(_,_)) | Some(Scope.StateVar(_,_)) | Some(Scope.ProcedureOutputArg(_,_))|
            Some(Scope.BlockVar(_,_)) | Some(Scope.FunctionArg(_,_)) | Some(Scope.LambdaVar(_,_))|
            Some(Scope.InputVar(_,_)) | Some(Scope.OutputVar(_,_)) | Some(Scope.SharedVar(_,_)) |
            Some(Scope.ConstantVar(_,_)) | Some(Scope.SelectorField(_))
              =>{
                if(id.toString.startsWith("_") && id.toString.substring(1).forall(Character.isDigit))
                  false
                else
                  true
              }
      case _ => false
    }
  }
  
  override def rewriteLHS(lhs : Lhs, context : Scope) : Option[Lhs] = {
    lhs match {
      case LhsRecordSelect(id, fields) =>
        val newFields = fields.map{case i: Identifier => 
        if(i.toString.startsWith("_") && i.toString.substring(1).forall(Character.isDigit))
          Identifier(i.toString)
        else
          Identifier(recordPrefix+i.toString)}
        Some(LhsRecordSelect(id, newFields))          
      case _ => Some(lhs)
    }
  }

  override def rewriteConstRecordLit(cr:ConstRecord, context : Scope) : Option[ConstRecord]={
    val new_field = cr.fieldvalues.map{case (id:Identifier,expr:Expr)=>(Identifier(recordPrefix+id.toString),expr)}
    Some(ConstRecord(new_field))
  }
}

class RewritePolymorphicSelect extends ASTRewriter(
    "RewritePolymorphicSelect", new RewritePolymorphicSelectPass())


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
      UclidMain.printVerbose("we have not rewritten this record type " + recordT.toString )
      Some(recordT)
    }
  }


  def isTypeRecord(t: Type) : Boolean = {
    if(!t.isRecord)
    {
      if(t.isArray)
       t.asInstanceOf[ArrayType].outType.isRecord
      else
       false
    }
    else
     true
  }

  def isRecord(id: Identifier, context: Scope): Boolean = {
    context.map.get(id) match {
      case Some(Scope.StateVar(i,t)) => isTypeRecord(t)
      case Some(Scope.ProcedureInputArg(i,t)) => isTypeRecord(t)
      case Some(Scope.ProcedureOutputArg(i,t)) => isTypeRecord(t)
      case Some(Scope.BlockVar(i,t)) => isTypeRecord(t)
      case Some(Scope.FunctionArg(i,t)) => isTypeRecord(t)
      case Some(Scope.LambdaVar(i,t)) => isTypeRecord(t)
      case Some(Scope.InputVar(i,t)) => isTypeRecord(t)
      case Some(Scope.OutputVar(i,t)) => isTypeRecord(t)
      case Some(Scope.SharedVar(i,t)) => isTypeRecord(t)
      case Some(Scope.ConstantVar(i,t)) => isTypeRecord(t)
      case _ =>  false
    }
  }

  def rewriteRecordFields(selectid: Identifier, argid: Identifier, opapp: OperatorApplication, context: Scope) : Option[OperatorApplication] = {   
    if(isRecord(argid, context))
    {
      UclidMain.printVerbose("rewriting record, the original identifier is " + selectid)
      Some(OperatorApplication(PolymorphicSelect(Identifier(recordPrefix+selectid.toString)), List(opapp.operands(0))))
    }
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
}

class RewriteRecordSelect extends ASTRewriter(
    "RewriteRecordSelect", new RewriteRecordSelectPass())