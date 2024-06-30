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
    UclidMain.printDebugRewriteRecord("Try to rewrite "+opapp+"\n")
    opapp.op match {
      case RecordUpdate(id,e)=>
        {
          val newOpApp = Some(OperatorApplication(RecordUpdate(Identifier(recordPrefix+id.toString),e),List(opapp.operands(0))))
          UclidMain.printDebugRewriteRecord("it is rewriten to "+newOpApp+"\n")
          newOpApp
        }
      case PolymorphicSelect(id) =>
        val expr = opapp.operands(0)    
        expr match {
          case arg : Identifier =>
            context.map.get(arg) match {
              case Some(Scope.ModuleDefinition(_)) =>
                Some(ExternalIdentifier(arg, id))
              case _ =>
              {
                if(isVarState(arg,id,context)){
                  val newOpApp = Some(OperatorApplication(PolymorphicSelect(Identifier(recordPrefix+id.toString)), List(opapp.operands(0))))
                  UclidMain.printDebugRewriteRecord("it is rewriten to "+newOpApp+"\n")
                  newOpApp
                }
                else{
                  Some(opapp)
                }
              }
                
            }
          case subopp: OperatorApplication =>{
            if(IsRewritable(subopp,context)){
              val newOpApp = Some(OperatorApplication(PolymorphicSelect(Identifier(recordPrefix+id.toString)), List(opapp.operands(0))))
              UclidMain.printDebugRewriteRecord("it is rewriten to "+newOpApp+"\n")
              newOpApp
            }
            else
              Some(opapp)
          }
          case ConstRecord(_) | ExternalIdentifier(_,_) |FuncApplication(_,_)=>
          {
            val newOpApp = Some(OperatorApplication(PolymorphicSelect(Identifier(recordPrefix+id.toString)), List(opapp.operands(0))))
            UclidMain.printDebugRewriteRecord("it is rewriten to "+newOpApp+"\n")
            newOpApp
          }
          case _ =>
          Some(opapp)
        }
      case _ => Some(opapp)
    }
  }

  def IsRewritable(candidate: Expr, context: Scope): Boolean = {
    candidate match {
      case OperatorApplication(PolymorphicSelect(id), operands) =>
        val expr = operands(0)
        expr match {
          case arg : Identifier => 
            isVarState(arg,id,context)||isVarInModule(id,arg,context)
          case OperatorApplication(_, _) | FuncApplication(_, _) => {
            if(IsRewritable(expr,context)) {
              true
            }
            else
            {
              val LastInstance = getLastInstance(expr, context);
              LastInstance match{
                case mid : Identifier => 
                  isVarInModule(id,mid,context)
                case _ => false
              }
            }
          }
          case _ => false
        }
      case OperatorApplication(op, operands) => {
        val expr = operands(0)
        expr match {
          case arg : Identifier => 
            isVarState(arg,Identifier(""),context)
          case subopp: OperatorApplication =>
            IsRewritable(subopp,context)
          case _ => false
        }  
      }
      case FuncApplication(func, operands) => {
        func match {
          case arg : Identifier => 
            isVarState(arg,Identifier(""),context)
          case subopp: OperatorApplication =>
            IsRewritable(subopp,context)
          case _ => false
        }
      }
      case _ => false
    }
  }

  // input: list of Decl in a external module 
  // output: return this identifier if it is a InstanceDecl, VarsDecl  
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

  def getLastInstance(target: Expr, context: Scope): Expr ={
    target match {
      case OperatorApplication(PolymorphicSelect(id), operands) => {
        operands(0) match {
          case arg : Identifier =>
            { 
              context.map.get(arg) match 
              {
              case Some(module:Scope.ModuleDefinition) => {
                checkIdDecl(module.mod.decls,id) match{
                    case Some(ident) => ident
                    case _ => target
                  }
              }
              case Some(Scope.Instance(instD)) => {
                context.map.get(instD.moduleId) match{
                  case Some(module:Scope.ModuleDefinition) =>
                  {
                  
                     checkIdDecl(module.mod.decls,id) match{
                      case Some(ident) => ident
                      case _ => target
                    }
                  }
                  case _ => target
                }
              }
              case _ => target
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
                    case _ => target
                  }
                }
                case Some(Scope.Instance(instD)) => {
                  context.map.get(instD.moduleId) match{
                    case Some(module:Scope.ModuleDefinition) =>
                    {
                      checkIdDecl(module.mod.decls,id) match{
                        case Some(ident) => ident
                        case _ => target
                      }
                    }
                    case _ => target
                  }
                }
                case _ => target
              }
            }
              case _ => target
            }
          }
          case _ => target
        }
      }
      case OperatorApplication(GetNextValueOp(), operands) =>  
        val expr = operands(0)     
        expr match {
          case subopp: OperatorApplication =>
            getLastInstance(subopp,context)
          case _ => target
        }
      case _ => target
    }
  }

  def isVarInModule(id:Identifier,mid:Identifier,context:Scope): Boolean ={
    val IdentifierType = context.map.get(mid)
    IdentifierType match 
    {
      case Some(module:Scope.ModuleDefinition) => {
           val match_var = Identifier(id.toString)
           lazy val vars : List[Identifier] =
          module.mod.decls.collect { case vars : StateVarsDecl => vars }.flatMap(v => v.ids.map(id => id))
          vars.contains(id)
        }
      case Some(Scope.Instance(instD)) => {
          context.map.get(instD.moduleId) match{
            case Some(model:Scope.ModuleDefinition) =>
            {
              val match_var = Identifier(id.toString)
              lazy val vars : List[Identifier] =
               model.mod.decls.collect { case vars : StateVarsDecl=> vars }.flatMap(v => v.ids.map(id => id))
              //if instance.var, then variable is in module
              vars.contains(id)
             }
             case _ => false
           }
         }
      case _ => false        
    }
  }
  
  def isVarState(arg: Identifier, id: Identifier, context: Scope): Boolean = {
    UclidMain.printDebugRewriteRecord("We are going to check "+arg+"\n")
    UclidMain.printDebugRewriteRecord("its type is "+context.map.get(arg)+"\n")
    context.map.get(arg) match{
      case  Some(Scope.ProcedureInputArg(_,_)) | Some(Scope.StateVar(_,_)) | Some(Scope.ProcedureOutputArg(_,_))|
            Some(Scope.BlockVar(_,_)) | Some(Scope.FunctionArg(_,_)) | Some(Scope.LambdaVar(_,_))|
            Some(Scope.InputVar(_,_)) | Some(Scope.OutputVar(_,_)) | Some(Scope.SharedVar(_,_)) |
            Some(Scope.ConstantVar(_,_)) | Some(Scope.SelectorField(_)) | Some(Scope.Function(_,_))
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
