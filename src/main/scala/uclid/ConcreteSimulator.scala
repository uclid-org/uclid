package uclid

import scala.util.parsing.combinator._
import scala.collection.mutable._
import lang.{Identifier, Module,  _}
import uclid.Utils.ParserErrorList
import com.typesafe.scalalogging.Logger
import org.json4s._
import org.json4s.jackson.JsonMethods._
import scala.io.Source

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
case class ConcreteEnum (ids:List[Identifier],value:BigInt) extends ConcreteValue{
    override def toString = value.toString
}

object ConcreteSimulator {
    var isPrintDebug: Boolean = false;
    var needToPrintResults = false;
    var isPrintResult: Boolean = true;
    var terminate: Boolean = false;
    var trace = Map[BigInt,scala.collection.mutable.Map[Identifier, ConcreteValue]]();
    var passCount: Int = 0;
    var failCount: Int = 0;
    var undetCount: Int = 0;
    var cntInt:Int = 0;
    var terminateInt: Int = 0;
    //var properties module.properties???
    // module properties.
    //lazy val properties : List[SpecDecl] = decls.collect{ case spec : SpecDecl => spec }
    //case class SpecDecl(id: Identifier, expr: Expr, params: List[ExprDecorator]) extends Decl {
    def execute (module: Module, config: UclidMain.Config) : List[CheckResult] = {

        UclidMain.printVerbose("HELLO IN EXECUTE")
        val jsonString: String = Source.fromFile("cex.json").mkString

        // Parse JSON into case class
        implicit val formats: DefaultFormats.type = DefaultFormats
        
        // Parse JSON into a JValue, provided by the json4s class
        val json: JValue = parse(jsonString)

        def parseArray(array: List[JValue]): List[String] = {
            array.collect {
                case JString(value) => value
                }
            }

        def parseTrace(trace: JValue): Unit = trace match {
            case JString(errorMessage) =>
                printDebug(s"Error Message: $errorMessage")
            case JArray(fields) =>
                fields.foreach {
                    case JObject(item) =>
                        val myMap: collection.mutable.Map[String, ConcreteInt] = collection.mutable.Map()
                        item.foreach {
                            listItem => {
                                var varName = listItem._1
                                listItem._2 match {
                                    case JArray(list) =>
                                        list.foreach {
                                            it =>
                                            it match {
                                                case JString(value) =>
                                                    var varValue = ConcreteInt(BigInt(value))
                                                    myMap += (varName -> varValue)
                                            }
                                        }
                                }
                                
                            }
                            
                        }
                        printDebug("Final Map: " + myMap)
                    
                    case _ => printDebug("invalid obj format")
                }

            case _ =>
                printDebug("Invalid trace format")
            }

        val properties: Map[String, JValue] = json.extract[Map[String, JValue]]
        properties.foreach {
            case (propertyName, propertyJson) =>
                val length: Int = (propertyJson \ "length").extract[Int]
                val trace: JValue = (propertyJson \ "trace").extract[JValue]

                printDebug(s"Property Name: $propertyName")
                printDebug(s"Length: $length")
                printDebug("Trace: ")
                parseTrace(trace)
                printDebug("")
        }


        //Leiqi: We started with a empty context
        //Read from json file and get a context
        //Read from enum
        val emptyContext = collection.mutable.Map[Identifier, ConcreteValue]()
        val varContext = collection.mutable.Map[Identifier, ConcreteValue](
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
                case EnumType(ids) => {
                    (v._1,ConcreteEnum(ids,-1))
                }   
                case _ => {
                    throw new NotImplementedError(v.toString+" has not been support yet!")
                }
            }) : _*)
        val preInitContext = varContext
        val postInitContext = module.init match {
            case Some(init) => initialize(preInitContext, init.body)
            case None => preInitContext
        }
        if (terminate) {
            printResult("Terminated Early")
        }

        trace(0) = postInitContext;  
        
        module.cmds.foreach {
            cmd => cmd.name.toString match {
                case "concrete" => {
                    val cntLit = cmd.args(0)
                    val cnt = cntLit._1.asInstanceOf[IntLit].value
                    cntInt = cnt.intValue()
                    terminateInt = cntInt;
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
                var newContext = postInitContext
                for (a <- 1 to cntInt) {
                    if (!terminate) {
                        newContext = simulate_stmt(newContext, next.body)
                        trace(a) = newContext   
                    } else {
                        terminateInt = a;
                        if (!terminate_printed) {
                            printDebug(s"Failed on iteration ${a-1}")
                            terminate_printed = true
                        } 
                    }
                    
                }
                newContext
            }
        }
        if(needToPrintResults){
            UclidMain.printResult("%d assertions passed.".format(passCount))
            UclidMain.printResult("%d assertions failed.".format(failCount))
            UclidMain.printResult("%d assertions indeterminate.".format(undetCount))
        }
        
        module.cmds.foreach{
            cmd => cmd.name.toString match {
                case "print_concrete_trace" =>
                    printConcretetTrace(trace, cmd.args, cmd.argObj)
                case _ => {}
            }
        }

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
                    failCount = failCount+1;
                    terminate = true
                    printResult("failed assert statement")
                }else{
                    passCount = passCount+1;
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
                                        case InequalityOp() => ConcreteBool(int_0 != int_1)
                                        case EqualityOp() => ConcreteBool(int_0 == int_1)
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
    /**
    * return a context
    * with vars added into Context
    **/
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
        context.++(newContext)
        
    }
    /**
    * return a context
    * Remove @vars from newContext
    */
    def mergeContext (
        oldContext: scala.collection.mutable.Map[Identifier, ConcreteValue],
        newContext: scala.collection.mutable.Map[Identifier, ConcreteValue],
        vars: List[BlockVarsDecl]) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        vars.foreach(
            vardecl =>
            {
                vardecl.ids.foreach(
                    id => {
                        newContext.-(id);
                        oldContext.get(id) match{
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
    def printContext(context: scala.collection.mutable.Map[Identifier, ConcreteValue],vars: List[(Expr, String)]) : Unit = {
        for (variable <- vars){
            println(variable._1+":  "+evaluate_expr(context,variable._1).toString)
        }}
    def printConcretetTrace(trace:Map[BigInt,scala.collection.mutable.Map[Identifier, ConcreteValue]],exprs : List[(Expr, String)], arg : Option[Identifier]){
        UclidMain.printStatus("Generated Trace of length " + (terminateInt).toString())
        UclidMain.printStatus("=================================")
        for (a <- 0 to terminateInt) {
            if(a<terminateInt){
                UclidMain.printStatus("=================================")
                UclidMain.printStatus("Step # "+a.toString)
                printContext(trace(a),exprs)
                UclidMain.printStatus("=================================")
            }
        }}
}
