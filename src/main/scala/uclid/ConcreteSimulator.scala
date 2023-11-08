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
case class ConcreteEnum (ids:List[Identifier],value:Int) extends ConcreteValue{
    override def toString = {
        if(value>0)
            ids(value).toString
        else
            "undefined"
    }
}

object ConcreteSimulator {
    var isPrintResult: Boolean = true;
    var isPrintDebug: Boolean = true;
    var needToPrintResults = false;
    var needToPrintTrace = false;
    var terminate: Boolean = false;
    var trace = Map[BigInt,scala.collection.mutable.Map[Identifier, ConcreteValue]]();
    var passCount: Int = 0;
    var failCount: Int = 0;
    var undetCount: Int = 0;
    var cntInt:Int = 0;
    var terminateInt: Int = 0;
    var readFromJson = false;
    var jsonFileName = "Null";

    def execute (module: Module, config: UclidMain.Config) : List[CheckResult] = {
        var printTraceCmd = module.cmds(0);
        lazy val properties = module.properties;
        UclidMain.printVerbose("HELLO IN EXECUTE")
        

        module.cmds.foreach {
            cmd => cmd.name.toString match {
                case "concrete" => {
                    val cntLit = cmd.args(0)
                    val cnt = cntLit._1.asInstanceOf[IntLit].value
                    cntInt = cnt.intValue()
                    needToPrintResults = true
                }
                case "print_concrete_trace" =>{
                    needToPrintTrace = true;
                    printTraceCmd = cmd;
                }
                case "read_from_json" =>{
                    
                    jsonFileName = cmd.args(0)._2;
                    //println(jsonFileName)
                    readFromJson = true;
                }
                case _ => {}
            }
        }
        val frame = 0
        val emptyContext = collection.mutable.Map[Identifier, ConcreteValue]()
        var varContext = extendContextVar(emptyContext,module.vars)
        // printContext(varContext,List())
        
        if(readFromJson)
            varContext = extendContextJson(varContext, frame, module.vars)
        
        val preInitContext = varContext
        val postInitContext = module.init match {
            case Some(init) => initialize(preInitContext, init.body)
            case None => preInitContext
        }
        
        //get more inforamtion
        //it should be here

        //Get random value for all unknow value
        //Get random value for unknow value when we hit that value


        checkProperties(properties,postInitContext);
        trace(0) = postInitContext; 

        if (terminate) {
            terminateInt = 0;
            printResult("Terminated in step 0")
        }
        
        else{
            printDebug("Running Concrete Simulation for "+cntInt+ " steps")
            var terminate_printed = false
            val next_stmt = module.next match {
                case Some(next) => 
                {
                    var newContext = postInitContext
                    for (a <- 1 to cntInt) {
                        if (!terminate) {
                            newContext = simulate_stmt(newContext, next.body)
                            checkProperties(properties,newContext)
                            trace(a) = newContext
                            terminateInt = a;   
                        } 
                        else {
                            if (!terminate_printed) {
                                printDebug(s"Failed on iteration ${a-1}")
                                terminate_printed = true
                            }    
                        }
                    }
                newContext
                }
                case _ => {}
            }
        }
        
        
        if(needToPrintResults){
            UclidMain.printResult("%d assertions passed.".format(passCount))
            UclidMain.printResult("%d assertions failed.".format(failCount))
            UclidMain.printResult("%d assertions indeterminate.".format(undetCount))

            if(needToPrintTrace){
                printConcretetTrace(trace, printTraceCmd.args, printTraceCmd.argObj)
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
                val flatVars : List[(Identifier, Type)] = vars.flatMap(v => v.ids.map(id => (id, v.typ)))
                var localContext = extendContextVar(context,flatVars)
                localContext = stmts.foldLeft(localContext)((a, stmt) => simulate_stmt(a, stmt))
                var newContext = cutContextVar(localContext,flatVars,context)
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
                        case ConcreteEnum(ids,index1) =>{
                            operand_1 match{
                                case ConcreteEnum(ids2, index2) =>{
                                    op match{
                                        case EqualityOp() => ConcreteBool(index1 == index2)
                                        case InequalityOp() => ConcreteBool(index1 != index2)
                                        case _ => throw new NotImplementedError("Not implements the Operator for enum"+op.toString) 
                                    }
                                }
                            }
                        }
                        case _ => {
                        throw new NotImplementedError("Does not support operation on this type yet")
                        }
                    }
                }
                
            }
            case _ => throw new NotImplementedError(s"Expression evaluation for ${expr}")
        }}
    def extendContextVar (context: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        vars: List[(Identifier, Type)]) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        var returnContext = context;
        var enumContext = collection.mutable.Map[Identifier, ConcreteValue]();
        val newContext = collection.mutable.Map[Identifier, ConcreteValue](
            vars.map(v => v._2 match {
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
                    for((id,i)<-ids.view.zipWithIndex){
                        enumContext(id)=ConcreteEnum(ids,i)
                    };
                    (v._1,ConcreteEnum(ids,-1))
                }   
                case _ => {
                    throw new NotImplementedError(v.toString+" has not been support yet!")
                }
            }) : _*)
            
        returnContext = returnContext.++(newContext);
        returnContext = returnContext.++(enumContext);
        returnContext
        }
    def extendContextJson(context: scala.collection.mutable.Map[Identifier, ConcreteValue], frame:Int, vars: List[(Identifier, Type)]): scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        val jsonString: String = Source.fromFile("cex.json").mkString;
        //println("So, json file name is "+jsonFileName);
        // Parse JSON into case class
        implicit val formats: DefaultFormats.type = DefaultFormats
        
        // Parse JSON into a JValue, provided by the json4s class
        val json: JValue = parse(jsonString)

        def parseArray(array: List[JValue]): List[String] = {
            array.collect {
                case JString(value) => value
                }
            }
        def findValueforVar(value: String, vars: List[(Identifier, Type)], varName: Identifier): ConcreteValue = {
            /*
            This function will go through the list of variables to find and create the proper variable type for the identifier passed into varName.
            */
            for (variable <- vars) {
                if (variable._1 == varName) {
                    variable._2 match {
                        case IntegerType() => {
                            return ConcreteInt(BigInt(value))
                        }
                        case BooleanType() => {
                            return ConcreteBool(value.toBoolean)
                        }
                    }
                }
                
            }
            return ConcreteInt(5)
        }
        def parseTrace(trace: JValue, frame: Int, vars: List[(Identifier, Type)]): scala.collection.mutable.Map[String, ConcreteValue] = {
            trace match {
                case JObject(item) =>
                    val tuple = item(1)._2
                    val myMap: collection.mutable.Map[String, ConcreteValue] = collection.mutable.Map()
                    tuple match {
                        case JArray(list) =>
                            var i: Int = 0
                            for (it <- list) {
                                if (i == frame) {
                                    it match {
                                        case JObject(item2) => {
                                            item2.foreach {
                                                listItem => {
                                                    var varName = listItem._1
                                                    listItem._2 match {
                                                        case JArray(list) => 
                                                            list.foreach {
                                                                item3 =>
                                                                item3 match {
                                                                    case JString(value) =>
                                                                        var varValue: ConcreteValue = findValueforVar(value, vars, Identifier(varName))
                                                                        myMap += (varName -> varValue)
                                                                }

                                                            }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                i = i + 1
                            }

                    }
                    // printDebug("Final Map: " + myMap)  
                    return myMap 
        }
        

        }
            

        val properties: Map[String, JValue] = json.extract[Map[String, JValue]]
        val propertyName = "property__jump_b__0"
        val property = properties(propertyName)
        val valueMap = parseTrace(property, frame, vars)

        val finalContext : scala.collection.mutable.Map[Identifier, ConcreteValue] = collection.mutable.Map()
        
        // for every variable in context, get the value from the valueMap
        context.foreach { 
            case (key, value) =>
            // val newValue: Identifier = key.toIdentifier
            println(value)
            val newvalue = valueMap(key.toString)
            finalContext += (key -> newvalue)
        }
        printDebug("")      
        printContext(finalContext, List())
        finalContext
        // context
        }
    def cutContextVar (
        newContext: scala.collection.mutable.Map[Identifier, ConcreteValue],
        vars: List[(Identifier, Type)],
        oldContext: scala.collection.mutable.Map[Identifier, ConcreteValue],
        ) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        for (id <-vars ){
            newContext.-(id._1);
            if(oldContext.contains(id._1)){
                newContext += (id._1->oldContext(id._1))
            }
        };
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

    
    def checkProperties(properties: List[SpecDecl],context:scala.collection.mutable.Map[Identifier, ConcreteValue]){
        for(property <- properties){
            if (!evaluateBoolExpr(context, property.expr)){ 
                    failCount = failCount+1;
                    terminate = true
                    printResult("failed assert statement")
                }else{
                    passCount = passCount+1;
                }
        }}
    def printDebug(str: String){
        if(isPrintDebug)
            println(str)}

    def printResult(str: String){
        if(isPrintResult)
            println(str)}
    /*
    * @context : The context needed to be print
    * @vars:     The picked variables inside the context
    * if vars is Empty List, then all the vars.
    */
    def printContext(context: scala.collection.mutable.Map[Identifier, ConcreteValue],vars: List[(Expr, String)]) : Unit = {
        printDebug("Call Print Context")
        if(vars.isEmpty){
            //println("Vars is empty and print all variables")
            for((key,value)<-context){
                println(key.toString+": "+value.toString)
            }
        }
        for (variable <- vars){
            println(variable._1+":  "+evaluate_expr(context,variable._1).toString)
        }}
    def printConcretetTrace(trace:Map[BigInt,scala.collection.mutable.Map[Identifier, ConcreteValue]],exprs : List[(Expr, String)], arg : Option[Identifier]){
        UclidMain.printStatus("Generated Trace of length " + (terminateInt).toString())
        UclidMain.printStatus("=================================")
        printDebug("The terminateInt is "+terminateInt.toString)
        printDebug("The trace's size is "+trace.size)
        for (a <- 0 to terminateInt) {
            if(a<=terminateInt){
                UclidMain.printStatus("=================================")
                UclidMain.printStatus("Step # "+a.toString)
                printContext(trace(a),exprs)
                UclidMain.printStatus("=================================")
            }
        }}
}
