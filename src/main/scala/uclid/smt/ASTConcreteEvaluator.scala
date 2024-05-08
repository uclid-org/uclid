package uclid
package smt


object ASTConcreteEvaluator
{
  def evalExpr(expr: Option[Expr], modelUclid: lang.AssignmentModel): Option[Expr] = {
    expr match {
      case Some(e) => { 
        val ret = e match {
          case BooleanLit(value) => BooleanLit(value)
          case IntLit(value) => IntLit(value)
          case RealLit(integral, frac) => RealLit(integral, frac)
          case FloatLit(integral, frac, exp, sign) => FloatLit(integral, frac, exp, sign)
          case BitVectorLit(value, width) => BitVectorLit(value, width)
          case OperatorApplication(op, operands) => {
            val concrete_operands = operands.map(o => evalExpr(Some(o), modelUclid).get)
            op match {
              case RecordSelectOp(field) => {
                val record = concrete_operands(0)
                record match {
                  case ConstRecord(fields) => {
                    fields.find(_._1 == field) match {
                      case Some((_, value)) => evalExpr(Some(value), modelUclid).get
                      case None => throw new Utils.UnimplementedException("Record select on non-existent field")
                    }
                  }
                  case _ => throw new Utils.UnimplementedException("Record select on non-record")
                }
              }
              case IntSubOp => {
                concrete_operands.size match {
                  case 1 => IntLit(-concrete_operands(0).asInstanceOf[IntLit].value)
                  case 2 => {
                    val op1 = concrete_operands(0).asInstanceOf[IntLit]
                    val op2 = concrete_operands(1).asInstanceOf[IntLit]
                    IntLit(op1.value - op2.value)
                  }
                  case _ => throw new Utils.UnimplementedException("Unimplemented operator application evaluation")
                }
              }
              case _ => e // Unimplemented operator application evaluation
            }
          }
          case ConstRecord(fields) => ConstRecord(fields)
          case Symbol(id, typ) => {
            val definitions = modelUclid.functions.filter(fun => fun._1.asInstanceOf[lang.DefineDecl].id.name == id.toString)
            definitions.size match {
              case 0 => e // No definition found, return the symbol. Should raise some error here
              case 1 => {
                val valueExpr = definitions.head._1.asInstanceOf[lang.DefineDecl].expr
                Converter.exprToSMT(valueExpr, lang.Scope.empty)
              }
              case _ => throw new Utils.RuntimeError("Found more than one definition in the assignment model!")
            }
          }
        }
        Some(ret)
      }
      case None => None
    }
  }
}
