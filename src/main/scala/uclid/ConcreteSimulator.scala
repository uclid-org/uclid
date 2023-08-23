package uclid

import scala.util.parsing.combinator._
// changed this from immutable to mutable
import scala.collection.mutable._
import lang.{Identifier, Module,  _}
import uclid.Utils.ParserErrorList
import com.typesafe.scalalogging.Logger



sealed abstract class ConcreteValue

case class ConcreteUndef () extends ConcreteValue
case class ConcreteBool (value: Boolean) extends ConcreteValue
//Leiqi:
//I change the definition of ConcreteInt as Uclid5 define int as BigInt
case class ConcreteInt (value: BigInt) extends ConcreteValue 
case class ConcreteBV (value: BigInt, width: Int) extends ConcreteValue
case class ConcreteArray (value: Map[ConcreteValue, ConcreteValue]) extends ConcreteValue
// case class ConcreteRecord (value: Map[Identifier, ConcreteValue]) extends ConcreteValue


// class ConcreteAssignment () {
//     // assignment is a map between identifier and the value that it takes on
//     // identifier is going to be a extension of the ConcreteValue?
//     val assignment : Map[Identifier, ConcreteValue] = Map()

//     // do we need to define the bool symbols here like it is done in Symbolic Simulator
// }

object ConcreteSimulator {

    
    /**
    execute executes one step in the system

    Input:
        List[context]
        List[Commands]
    Output:
        List[context]

    */ 
    def execute (module: Module, config: UclidMain.Config) : List[CheckResult] = {
        // End goal
        UclidMain.printVerbose("HELLO IN EXECUTE")
        //println(module)
        
        // create a new variable for ConcreteBool with a value and then try to print that

        // var - mutable, open to reassignment
        // val - immutable, cannot reassign
        // val test_bool = ConcreteBool(false)

        // val test_int = ConcreteInt(3)

        // println(module.vars)

        val preinit = collection.mutable.Map[Identifier, ConcreteValue](
            module.vars.map(v => (v._1, ConcreteUndef())): _*)

        // TODO: Create context for each block stmt (LEIQI)
        
        
        println("Simulating init block")
        // result of applying init block to preinit
        val postinit = module.init match {
            case Some(init) => initialize(preinit, init.body)
            case None => preinit
        }

        println("After initialize")
        pretty_print(postinit)
        
        var cntInt = 0
        
        module.cmds.foreach {
            cmd => cmd.name.toString match {
                case "concrete" => {
                    val cntLit = cmd.args(0)
                    // Utils.checkParsingError(cntLit._1.isInstanceOf[IntLit], "'%s' command expects a constant integer argument".format(cmd.name.toString), cmd.pos, filename)
                    val cnt = cntLit._1.asInstanceOf[IntLit].value
                    cntInt = cnt.intValue()
                }

                case _ => {
                    
                }

            }
                
        }
        println(cntInt)
        
        val next_stmt = module.next match {
            case Some(next) => 
            {
                var newContext = postinit
                for (a <- 1 to cntInt) {
                    newContext = simulate_stmt(newContext, next.body)
                }
                newContext
            }
        }

        println("\n\n\nAfter next")
        pretty_print(next_stmt)
        // check that none of the values are ConcreteUndef

        // println("Simulate next block")
        // println(module.next.get.getClass)
        
        // val context : scala.collection.mutable.Map[Identifier, ConcreteValue] = Map.empty
        // println("preinit")
        // pretty_print(preinit)
        // println("postinit")
        // pretty_print(postinit)
        // initialize(context)
        
        // need to access the variables in the 
        // 

        // Define initial assignment
        // val init_assignment = initialize()

        // // Simulate
        // simulate_helper(init_assignment, stmt)
        return List()
    }

    def initialize (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        stmt: Statement) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        simulate_stmt(context, stmt)
    }

    def simulate_stmt (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        stmt: Statement) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        
        stmt match {
            case AssignStmt(lhss, rhss) => {
                // println("looking at assign stmt")
                val rhseval = rhss.map(rhs => evaluate_expr(context, rhs))
                if (rhseval.size == 1) {
                    lhss.foldLeft(context)((a, l) => update_lhs(a, l, rhseval(0)))
                } else {
                    throw new NotImplementedError(s"RHS must be singleton")
                }
            }

            case BlockStmt(vars, stmts) => {
                // println("looking at block stmt")
                //before entering block, create a new context

                var localContext = extendContext(context,vars)
                // println("local context: ", localContext)
                localContext = stmts.foldLeft(localContext)((a, stmt) => simulate_stmt(a, stmt))
                var newContext = mergeContext(context,localContext,vars)
                // println("new context: ", newContext)
                newContext
                //simulate_stmt(newContext,stmt)
                //when we left the block, create a correct context
            }
            
            case SkipStmt() => {
                context
            }
            case AssertStmt(e, id) => {
                throw new NotImplementedError(s"AssertStmt not implemented")
            }
            case AssumeStmt(e, id) => {
                throw new NotImplementedError(s"AssumeStmt not implemented")
            }
            case HavocStmt(havocable) => {
                throw new NotImplementedError(s"HavocStmt not implemented")
            }
            case IfElseStmt(cond, ifblock, elseblock) => {
                if (evaluateBoolExpr(context, cond)) {
                    simulate_stmt(context, ifblock)
                } else {
                    simulate_stmt(context, elseblock)
                }
            }
            case ForStmt(id, typ, range, body) => {
                // these are ConcreteValues as the bounds
                println("in for loop")
                var low = evaluate_expr(context, range._1)
                var high = evaluate_expr(context, range._2)
                
                // id can be int, bv, float
                typ match {
                    case IntegerType() => {
                        val low_ = low match {
                            case l: ConcreteInt => l.value
                            // case _ => throw new 
                        }                        
                        val high_ = high match {
                            case h : ConcreteInt => h.value
                        }
                        (low_ to high_).foldLeft(context)((con_, it) => {
                            val newcon_ = simulate_stmt(con_.+(id -> ConcreteInt(it)), body)
                            newcon_.-(id)
                            newcon_
                        })
                    }
                }
                // for (id <- range._1 to range._2) {
                // simulate_stmt(body)
                // }
                // throw new NotImplementedError(s"ForStmt not implemented")
            }
            case WhileStmt(cond, body, invariants) => {
                // cond: Expr, body: Statement, invariants: List[Expr]
                // not sure what the difference is between cond and invariants but every loop through we keep checking the cond
                // if the cond holds then simulate_stmt on body
                if (evaluateBoolExpr(context, cond)) {
                    var newContext = simulate_stmt(context, body)
                    while (evaluateBoolExpr(newContext, cond)) {
                        newContext = simulate_stmt(newContext, body)
                    }
                    newContext
                } else {
                    context
                }
            }
            case CaseStmt(body) => {

                // body: List[(Expr,Statement)]
                // since it is a list of expr with statements, we go through the list, evaluate_expr and once it is true, simulate_stmt
                println("in case...")
                context
            }
            case ProcedureCallStmt(id, callLhss, args, instanceId, moduleId) => {
                throw new NotImplementedError(s"ProcedureCallStmt not implemented")
            }
            case MacroCallStmt(id) => {
                throw new NotImplementedError(s"MacroCallStmt not implemented")
            }
            case ModuleCallStmt(id) => {
                throw new NotImplementedError(s"ModuleCallStmt not implemented")
            }
        }
    }

    """
    Evaluates a condition (Expr) in a context and returns a boolean if the cond is held or not.
    """
    def evaluateBoolExpr(context: scala.collection.mutable.Map[Identifier, ConcreteValue],
        cond: Expr) : Boolean = {
            evaluate_expr(context,cond) match {
                case ConcreteBool(b) => {
                    if (b) {
                        return true
                    } else {
                        return false
                    }
                }
            }
        }

    def update_lhs (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        lhs: Lhs, v: ConcreteValue) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {  
        // TODO: More updates to LHS (Adwait)
        lhs match {
            case LhsId(id) => {
                context(id) = v
                context
            }
            case _ => throw new NotImplementedError(s"LHS Update for ${lhs}")
        }
        }


    def evaluate_expr (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        expr: lang.Expr) : ConcreteValue = {
        
        expr match {
            case a : Identifier => context(a)
            case BoolLit(b) => ConcreteBool(b)
            case IntLit(b) => ConcreteInt(b)
            // case RealLit(a,b) => 
            // case FloatLit(a,b,c,d) =>
            case BitVectorLit(a,b) => ConcreteBV(a,b)
            // case StringLit(a) =>
            // case EnumLit????
            // case NumericLit??
            // case FreshLit??
            // case ConstArray
            // case UninterpretedTypeLiteral
            // case ConstRecord
            // case Tuple

            // case PolymorphicSelect
            // case RecordSelect
            // case HyperSelect
            // case SelectFromInstance
            // case ITEOp
            // case ForallOp

            // // PolymorphicOperator
            // case LTOp()
            // case LEOp()
            // case GTOp()
            // case GEOp()
            // case AddOp()
            // case SubOp()
            // case MulOp()
            // case UnaryMinusOp()
            // case DivOp()

            // // RealArgOperator
            // case RealLTOp()
            // case RealLEOp()
            // case RealGTOp()
            // case RealGEOp()
            // case RealAddOp()
            // case RealSubOp()
            // case RealMulOp()
            // case RealUnaryMinusOp()
            // case RealDivOp()

            // // FloatArgOperator
            // case FPLTOp(e,s)
            // case FPGTOp(e,s) 
            // case FPLEOp(e,s)
            // case FPGEOp(e,s)
            // case FPSubOp(e,s)
            // case FPAddOp(e,s)
            // case FPMulOp(e,s)
            // case FPDivOp(e,s)
            // case FPIsNanOp(e,s)
            // case FPUnaryMinusOp(e,s)

            // // QuantifiedBooleanOperator??

            // case ForallOp(vs, patterns) 
            // case ExistsOp(vs, patterns) 
            // case FiniteForallOp(id, groupId) 
            // case FiniteExistsOp(id, groupId) 

            // // inequality operator
            // case EqualityOp()
            // case InequalityOp()
            
            // // BV2Int and Int2BV
            // case BV2SignedIntOp()
            // case BV2UnsignedIntOp()

            // // Int2BV
            // case Int2BVOp()

            // // LTL Operators
            // case GloballyTemporalOp()
            // case NextTemporalOp()
            // case UntilTemporalOp()
            // case FinallyTemporalOp()
            // case ReleaseTemporalOp()
            // case WUntilTemporalOp()

            // // Old Operator
            // case OldOperator()
            // case PastOperator()
            // case HistoryOperator()

            // // ITE operator
            // case ITEOp()

            

            // // ExtractOp
            // case ConstExtractOp(slice)
            // case VarExtractOp(slice)
            // case ConcatOp()

            // // SelectorOperator
            // case PolymorphicSelect(id)
            // case RecordSelect(id)
            // case SelectFromInstance(varId)
            // case HyperSelect(i)
            // case ArraySelect(indices)
            // case ArrayUpdate(indices,value)
            // case RecordUpdate(fieldid, value)
            // case GetNextValueOp()
            // case DistinctOp()



            // case class ConcreteArray 
            // additiion / subtract  (Look at OperatorApplication)
            // case class OperatorApplication(op: Operator, operands: List[Expr])
                // do a case match on the op
            
            
            // case NegationOp()
            case OperatorApplication(op:Operator, operands:List[Expr])=>{

                val operand_0 = evaluate_expr(context,operands.head);
                //if this is binary operation
                if(operands.tail.size==0){
                    operand_0 match{
                        case ConcreteBool(bool_0) => {
                            op match{
                                case NegationOp() => ConcreteBool(!bool_0)
                                case _ => throw new NotImplementedError("Not implements the Operator for ConcreteBool"+op.toString) 
                            }
                        }

                        case ConcreteInt(int_0) => {
                            op match{
                                case IntUnaryMinusOp() => ConcreteInt(-int_0)
                                case ConcatOp() => throw new NotImplementedError("Have not emplement ++ by now")
                                case _ => throw new NotImplementedError("Not implements the Operator"+op.toString) 
                            }
                        }
                        case ConcreteBV(int_0,length) => {
                            op match{
                                case ConcatOp() => throw new NotImplementedError("Have not emplement ++ by now")
                                case BVNotOp(w) => ConcreteBV((~int_0) & ((1 << length) - 1), length)
                                case BVUnaryMinusOp(w) => ConcreteBV((-int_0)& ((1 << length) - 1), length)
                                case BVLeftShiftBVOp(w) => ConcreteBV((int_0<<w) & ((1 << length) - 1), length)
                                case BVLRightShiftBVOp(w) => ConcreteBV((int_0>>w) & ((1 << length) - 1), length)
                                case BVARightShiftBVOp(w) => ConcreteBV((int_0>>w) & ((1 << length) - 1) | (((1 << length) - 1)<<w & ((1 << length) - 1)), length)
                                case ConstExtractOp(slide) => ConcreteBV((int_0&((1 << (slide.hi+1) - 1)))>>slide.lo, slide.hi-slide.lo+1)
                                // case ConstBitVectorSlice(hi,lo) => ConcreteBV((int_0&((1 << (hi-lo)) - 1))>>lo, length)
                                // case VarBitVectorSlice(hi, lo, wd)
                                case _ => throw new NotImplementedError("Not implements unary operation "+op.toString+" for BV\n")
                            }
                            
                        }
                        
                        case _ => throw new NotImplementedError("Should not entry this line"+op.toString) 
                    }            
                }
                else{
                    val operand_1 = evaluate_expr(context,operands.tail.head);
                    operand_0 match{
                        case ConcreteBool(bool_0) =>{
                            operand_1 match{
                                case ConcreteBool(bool_1) => {
                                    op match{
                                        case ConjunctionOp() => ConcreteBool(bool_0&&bool_1)
                                        case DisjunctionOp() => ConcreteBool(bool_0||bool_1)
                                        case IffOp() => ConcreteBool(bool_0 == bool_1)
                                        case ImplicationOp() => ConcreteBool(!bool_0 || bool_1)
                                        case _ => throw new NotImplementedError("Not implements the Operator for Bool"+op.toString) 
                                    }
                                }
                                case _ => throw new NotImplementedError("Should not reach here")
                            }
                        }
                        case ConcreteInt(int_0) => {
                            operand_1 match{
                                case ConcreteInt(int_1) =>{
                                    op match{
                                        case IntAddOp()=> ConcreteInt(int_0+int_1)
                                        case IntSubOp() => ConcreteInt(int_0-int_1)
                                        case IntMulOp() => ConcreteInt(int_0*int_1)
                                        case IntDivOp() => ConcreteInt(int_0/int_1)
                                        case IntLTOp() => ConcreteBool(int_0 < int_1)
                                        case IntLEOp() => ConcreteBool(int_0 <= int_1)
                                        case IntGEOp() => ConcreteBool(int_0 >= int_1)
                                        case IntGTOp() => ConcreteBool(int_0 > int_1)
                                        case _ => throw new NotImplementedError("Not implements the Operator"+op.toString) 
                                    }
                                }
                                case _ => throw new NotImplementedError("Should not entry this line"+op.toString) 
                            }
                        }    
                        case ConcreteBV(int_0, length) =>{
                            operand_1 match{
                                case ConcreteBV(int_1, length) =>{
                                    val unint_0 = (~int_0) & ((1 << length) - 1)
                                    val unint_1 = (~int_0) & ((1 << length) - 1)
                                    op match{
                                        
                                        case BVLTOp(w) => ConcreteBool(int_0 < int_1)
                                        case BVLEOp(w) => ConcreteBool(int_0 <= int_1)
                                        case BVGTOp(w) => ConcreteBool(int_0 > int_1)
                                        case BVGEOp(w) => ConcreteBool(int_0 >= int_1)
                                        case BVAddOp(w) => ConcreteBV((int_0 + int_1) & ((1 << length) - 1),w)
                                        case BVSubOp(w) => ConcreteBV((int_0 - int_1) & ((1 << length) - 1),w) 
                                        case BVMulOp(w) => ConcreteBV((int_0 * int_1) & ((1 << length) - 1),w)
                                        case BVDivOp(w) => ConcreteBV((int_0 / int_1) & ((1 << length) - 1),w)
                                        case BVAndOp(w) => ConcreteBV((int_0 & int_1) & ((1 << length) - 1),w)
                                        case BVOrOp(w)  => ConcreteBV((int_0 | int_1) & ((1 << length) - 1),w)
                                        case BVXorOp(w) => ConcreteBV((int_0 ^ int_1) & ((1 << length) - 1),w)
                                        case BVSremOp(w) => ConcreteBV((int_0 % int_1) & ((1 << length) - 1),w)

                                        case BVLTUOp(w) => ConcreteBool(unint_0 < unint_1)
                                        case BVLEUOp(w) => ConcreteBool(unint_0 <= unint_1)
                                        case BVGTUOp(w) => ConcreteBool(unint_0 > unint_1)
                                        case BVGEUOp(w) => ConcreteBool(unint_0 >= unint_1)
                                        case BVUremOp(w) => ConcreteBV(unint_0 % unint_1,w)
                                        case BVUDivOp(w) => ConcreteBV(unint_0 / unint_1,w)
     
                                        //Those operations do not exist in parser??
                                        // case BVSignExtOp(w,e) 
                                        // case BVZeroExtOp(w,e) 
                                    
                                        case _ => throw new NotImplementedError("Not implements the Operator for BV"+op.toString) 
                                    }
                                }
                            }
                        }
                        case _ => {
                        throw new NotImplementedError("Does not support this type yet")
                        }
                    }
                }
                
            }
            case _ => throw new NotImplementedError(s"Expression evaluation for ${expr}")
        }
    }

    def pretty_print(context: scala.collection.mutable.Map[Identifier, ConcreteValue]) : Unit = {
        for (a <- context) {
            println(a)
        }   
    }
    def extendContext (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        vars: List[BlockVarsDecl]) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        //Leiqi:
        //initilze those variables here????
            

        val newContext = collection.mutable.Map[Identifier, ConcreteValue]();
        
        vars.foreach(
            vardecl =>
            {
                vardecl.ids.foreach(
                    id => {
                        newContext+= (id -> ConcreteUndef())
                    }
                )
            }
        );
        //Leiqi:
        //there might be some bugs
        context.++(newContext)
    }
    
    def mergeContext (
        original: scala.collection.mutable.Map[Identifier, ConcreteValue],
        newContext: scala.collection.mutable.Map[Identifier, ConcreteValue],
        vars: List[BlockVarsDecl]) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        
        //those variables is local variables, should not be updated into the original context
        vars.foreach(
            vardecl =>
            {
                vardecl.ids.foreach(
                    id => {
                        newContext.-(id);
                        original.get(id) match{
                            case value: ConcreteValue =>{
                                newContext += (id->value)
                            }
                            case _  => {
                                
                            }
                        }
                    }
                )
            }
        );
        //so, the newContext does not contain local varibales now
        newContext
    }
    // context(Id("n")) = ConcreteInt(context(Id("n")).value + 1)

    /**
    executeOneStep is responsible for taking in a current assignment and a command to find out the next assignment for the variables

    Input:
        context
        stmt
    Output:
        context
    */ 
    // def executeOneStep (context: ConcreteAssignment, stmt: Statement) : Assignment = {}
            // check the type of assignment
            
            // execute statement
            // context(Id("n")) = ConcreteInt(context(Id("n")).value + 1)


    //     return Assignment

}