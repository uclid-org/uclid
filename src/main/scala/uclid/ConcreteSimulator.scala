package uclid

import scala.util.parsing.combinator._
import scala.collection.mutable._
import lang.{Identifier, Module,  _}
import uclid.Utils.ParserErrorList
import com.typesafe.scalalogging.Logger

sealed abstract class ConcreteValue
case class ConcreteUndef () extends ConcreteValue
case class ConcreteBool (value: Boolean) extends ConcreteValue{
    override def toString = value.toString
} 
case class ConcreteInt (value: BigInt) extends ConcreteValue{
    override def toString = value.toString
} 
case class ConcreteBV (value: BigInt, width: Int) extends ConcreteValue{
    override def toString = value.toString+"bv"+width.toString
} 
case class ConcreteArray (value: Map[List[ConcreteValue], ConcreteValue]) extends ConcreteValue{
    override def toString = value.toString
} 
case class ConcreteRecord (value: Map[Identifier, ConcreteValue]) extends ConcreteValue{
    override def toString = value.toString
} 

object ConcreteSimulator {
    var isPrintDebug: Boolean = false;
    var needToPrintResults = false;
    var isPrintResult: Boolean = true;
    var terminate: Boolean = false;
    def execute (module: Module, config: UclidMain.Config) : List[CheckResult] = {

        UclidMain.printVerbose("HELLO IN EXECUTE")

        val preinit = collection.mutable.Map[Identifier, ConcreteValue](
            module.vars.map(v => v._2 match {
                case IntegerType() => {
                    (v._1, ConcreteUndef())
                }
                case BooleanType() => {
                    (v._1, ConcreteUndef())
                }
                case BitVectorType(w) => {
                    (v._1, ConcreteUndef())
                }
                //... fill in
                case ArrayType(inType, outType) => {
                    // TODO: outType could be complex type like another array or record
                    (v._1, ConcreteArray(scala.collection.mutable.Map[List[ConcreteValue], ConcreteValue]().withDefaultValue(ConcreteUndef())))
                }
                case RecordType(members) => {
                    val RecordMap = scala.collection.mutable.Map[Identifier, ConcreteValue]();
                    for(member<-members){
                        RecordMap(member._1)=ConcreteUndef();
                    }
                    (v._1, ConcreteRecord(RecordMap))
                }
            }) : _*)

        val postinit = module.init match {
            case Some(init) => initialize(preinit, init.body)
            case None => preinit
        }

        if (terminate) {
            printResult("Terminated Early")
        }
        printResult("Context after Simulating init block:")
        printContext(postinit,module)
        
        var cntInt = 0
        
        module.cmds.foreach {
            cmd => cmd.name.toString match {
                case "concrete" => {
                    val cntLit = cmd.args(0)
                    val cnt = cntLit._1.asInstanceOf[IntLit].value
                    cntInt = cnt.intValue()
                    needToPrintResults = true
                }
                case _ => {}
            }
        }
        printDebug("Running Concrete Simulation for "+cntInt+ " steps")
        var terminate_printed = false
        val next_stmt = module.next match {
            case Some(next) => 
            {
                var newContext = postinit
                for (a <- 1 to cntInt) {
                    if (!terminate) {
                        newContext = simulate_stmt(newContext, next.body)   
                    } else {
                        if (!terminate_printed) {
                            printResult(s"Failed on iteration ${a-1}")
                            terminate_printed = true
                        } 
                    }
                    
                    
                }
                newContext
            }
        }

        if (terminate) {
            printResult("Early Terminate")
        }
        printResult("\n\n\nContext after simulating the next block")
        printContext(next_stmt,module)

        return List()}
    def initialize (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        stmt: Statement) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        simulate_stmt(context, stmt)}

    def simulate_stmt (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        stmt: Statement) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        
        stmt match {
            case AssignStmt(lhss, rhss) => {
                val rhseval = rhss.map(rhs => evaluate_expr(context, rhs))
                if (rhseval.size == 1) {
                    lhss.foldLeft(context)((a, l) => update_lhs(a, l, rhseval(0)))
                } else {
                    throw new NotImplementedError(s"RHS must be singleton")
                }
            }

            case BlockStmt(vars, stmts) => {
                var localContext = extendContext(context,vars)
                localContext = stmts.foldLeft(localContext)((a, stmt) => simulate_stmt(a, stmt))
                var newContext = mergeContext(context,localContext,vars)
                newContext
            }
            
            case SkipStmt() => {
                context
            }
            case AssertStmt(e, id) => {
                if (!evaluateBoolExpr(context, e)){ 
                    terminate = true
                    printResult("failed assert statement")
                }
                context
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
                println("in for loop")
                var low = evaluate_expr(context, range._1)
                var high = evaluate_expr(context, range._2)
                typ match {
                    case IntegerType() => {
                        val low_ = low match {
                            case l: ConcreteInt => l.value
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
                printDebug("in case...")
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
        }}
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
            case LhsArraySelect(id,indices)=>{
                context(id) match {
                    case ca:ConcreteArray => {
                        val eval_indices = indices.map(a => evaluate_expr(context,a)) // list of concrete expr
                        var old_map = ca.value // old array 
                        old_map(eval_indices) = v
                        val new_arr = ConcreteArray(old_map)
                        context(id) = new_arr
                        context
                    }
                    case _ => {
                        throw new Error("attempting to do array select on a non-array object")
                        
                    }
                }
                context
            }
            case LhsRecordSelect(id,fieldid)=>{
                context(id) = updateRecordValue(fieldid,v,context(id))
                context     
            }
            case _ => {
                throw new NotImplementedError(s"LHS Update for ${lhs}")
            }
            
        }
        }


    def evaluate_expr (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        expr: lang.Expr) : ConcreteValue = {
        
        expr match {
            case a : Identifier => context(a)
            case BoolLit(b) => ConcreteBool(b)
            case IntLit(b) => ConcreteInt(b)
            case BitVectorLit(a,b) => ConcreteBV(a,b)
            case OperatorApplication(op:Operator, operands:List[Expr])=>{
                val operand_0 = evaluate_expr(context,operands.head);
                //if this is not binary operation
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
                        case ConcreteArray(valuemap) => {
                            op match {
                                case ArraySelect(indices) => {
                                    val eval_indices = indices.map(a => evaluate_expr(context,a)) // list of concrete expr
                                    valuemap(eval_indices)
                                }
                                case ArrayUpdate(indices, value) => {
                                    val eval_value = evaluate_expr(context, value)
                                    val eval_indices = indices.map(a => evaluate_expr(context,a)) // list of concrete expr
                                    var old_map = valuemap // old array 
                                    old_map(eval_indices) = eval_value
                                    ConcreteArray(old_map)   
                                    
                                }
                                // TODO: Any additional unary array operators should be handled here
                                case _ => throw new NotImplementedError("Not implements unary operation for ConcreteArray "+"op: "+op + "operands: "+ operands+ "operand_0"+ operand_0)
                            }
                        }
                        case ConcreteRecord(valuemap) => {
                            op match{
                                case RecordSelect(id) =>{
                                    if(valuemap.contains(id))
                                        valuemap(id)
                                    else
                                        ConcreteUndef()
                                }
                                case _ => throw new NotImplementedError("Not implements unary operation for ConcreteRecord"+"op: "+op + "operands: "+ operands+ "operand_0"+ operand_0)
                            }
                        }
                        case _ => throw new NotImplementedError("Not implements unary operation "+"op: "+op + "operands: "+ operands+ "operand_0"+ operand_0) 
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
        }}
    def extendContext (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        vars: List[BlockVarsDecl]) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
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
        context.++(newContext)}
    def mergeContext (
        original: scala.collection.mutable.Map[Identifier, ConcreteValue],
        newContext: scala.collection.mutable.Map[Identifier, ConcreteValue],
        vars: List[BlockVarsDecl]) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
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
        newContext}
    def updateRecordValue(fields: List[Identifier],value: ConcreteValue,recordValue: ConcreteValue): ConcreteRecord = {
        if(fields.size == 1){
            recordValue match{
                case ConcreteUndef() => ConcreteRecord(Map(fields.head->value))
                case ConcreteRecord(map) => {
                    var newMap = map;
                    newMap(fields.head) = value;
                    ConcreteRecord(newMap)
                }
                
                case _ => throw new NotImplementedError(s"Should not touch here")
            }
        }
        else{
            // now, we have one recordValue and we have not touch the end of the Record
            recordValue match{
                case ConcreteUndef() => ConcreteRecord(Map(fields.head->updateRecordValue(fields.tail,value,ConcreteUndef())))
                case ConcreteRecord(map) => {
                    var newMap = map;
                    newMap(fields.head) = updateRecordValue(fields.tail,value,map(fields.head));
                    ConcreteRecord(newMap)
                }
                case _ => throw new NotImplementedError(s"Should not touch here")
            }
        }}

    
    def printDebug(str: String){
        if(isPrintDebug)
            println(str)}

    def printResult(str: String){
        if(isPrintResult)
            println(str)}
    def printContext(context: scala.collection.mutable.Map[Identifier, ConcreteValue],module: Module) : Unit = {
        for (variable <- module.vars){
            println(variable._1+":  "+context(variable._1).toString)
        }
    }
}