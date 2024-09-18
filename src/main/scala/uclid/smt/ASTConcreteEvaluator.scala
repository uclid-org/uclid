package uclid
package smt

import uclid.lang

object ASTConcreteEvaluator
{
  def evalExpr(expr: Option[Expr], modelUclid: lang.AssignmentModel): Option[Expr] = {
    expr match {
      case Some(e) => { 
        val ret = e match {
          case BooleanLit(value) => Some(BooleanLit(value))
          case IntLit(value) => Some(IntLit(value))
          case RealLit(integral, frac) => Some(RealLit(integral, frac))
          case FloatLit(integral, frac, exp, sign) => Some(FloatLit(integral, frac, exp, sign))
          case BitVectorLit(value, width) => Some(BitVectorLit(value, width))
          case OperatorApplication(op, operands) => {
            val concrete_operands = operands.map(o => evalExpr(Some(o), modelUclid) match {
              case Some(e) => e
              case None => return None
            })
            op match {
              case RecordSelectOp(field) => {
                val record = concrete_operands(0)
                record match {
                  case ConstRecord(fields) => {
                    fields.find(_._1 == field) match {
                      case Some((_, value)) => Some(evalExpr(Some(value), modelUclid).get)
                      case None => throw new Utils.UnimplementedException("Record select on non-existent field")
                    }
                  }
                  // case _ => throw new Utils.UnimplementedException("Record select on non-record")
                  case _ => None
                }
              }
              case RecordUpdateOp(field) => {
                val record = concrete_operands(0)
                val value = concrete_operands(1)
                record match {
                  case ConstRecord(fields) => {
                    val newFields = fields.map(f => if (f._1 == field) (f._1, value) else f)
                    Some(ConstRecord(newFields))
                  }
                  // case _ => throw new Utils.UnimplementedException("Record update on non-record")
                  case _ => None
                }
              }
              case EqualityOp => {
                val op1 = concrete_operands(0)
                val op2 = concrete_operands(1)
                Some(BooleanLit(op1 == op2))
              }
              case InequalityOp => {
                val op1 = concrete_operands(0)
                val op2 = concrete_operands(1)
                Some(BooleanLit(op1 != op2))
              }
              case IntGEOp => {
                val op1 = concrete_operands(0).asInstanceOf[IntLit].value
                val op2 = concrete_operands(1).asInstanceOf[IntLit].value
                Some(BooleanLit(op1 >= op2))
              }
              case IntLEOp => {
                val op1 = concrete_operands(0).asInstanceOf[IntLit].value
                val op2 = concrete_operands(1).asInstanceOf[IntLit].value
                Some(BooleanLit(op1 <= op2))
              }
              case IntGTOp => {
                val op1 = concrete_operands(0).asInstanceOf[IntLit].value
                val op2 = concrete_operands(1).asInstanceOf[IntLit].value
                Some(BooleanLit(op1 > op2))
              }
              case IntLTOp => {
                val op1 = concrete_operands(0).asInstanceOf[IntLit].value
                val op2 = concrete_operands(1).asInstanceOf[IntLit].value
                Some(BooleanLit(op1 < op2))
              }
              case IntAddOp => {
                val ints = concrete_operands.map(_.asInstanceOf[IntLit].value)
                Some(IntLit(ints.reduce(_ + _)))
              }
              case IntSubOp => {
                concrete_operands.size match {
                  case 1 => Some(IntLit(-concrete_operands(0).asInstanceOf[IntLit].value))
                  case 2 => {
                    val op1 = concrete_operands(0).asInstanceOf[IntLit]
                    val op2 = concrete_operands(1).asInstanceOf[IntLit]
                    Some(IntLit(op1.value - op2.value))
                  }
                  case _ => throw new Utils.UnimplementedException("Unimplemented operator application evaluation")
                }
              }
              case ITEOp => {
                val cond = concrete_operands(0).asInstanceOf[BooleanLit].value
                if (cond) Some(concrete_operands(1)) else Some(concrete_operands(2))
              }
              // case _ => Some(e) // Unimplemented operator application evaluation
              case _ => throw new Utils.UnimplementedException("Unimplemented operator application evaluation")
            }
          }
          case ConstRecord(fields) => Some(ConstRecord(fields))
          case Symbol(id, typ) => {
            val definitions = modelUclid.functions.filter(fun => fun._1.asInstanceOf[lang.DefineDecl].id.name == id.toString)
            definitions.size match {
              case 0 => { 
                // println("No symbol found: " + id.toString)
                None
              } // No definition found, return the symbol. Should raise some error here
              case 1 => {
                val valueExpr = definitions.head._1.asInstanceOf[lang.DefineDecl].expr
                Some(Converter.exprToSMT(valueExpr, lang.Scope.empty))
              }
              case _ => throw new Utils.RuntimeError("Found more than one definition in the assignment model!")
            }
          }
        }
        ret
      }
      case None => None
    }
  }
}
