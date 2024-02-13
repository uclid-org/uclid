package uclid

import scala.util.parsing.combinator._
import scala.collection.mutable._
import org.json4s._
import org.json4s.jackson.JsonMethods._
import scala.util.Random
import scala.math._
import scala.collection.mutable.ArrayBuffer

import lang._
import Utils.ParserErrorList


sealed trait CmdsMod
case object Fuzzing extends CmdsMod
case object Default extends CmdsMod
case object Json extends CmdsMod
case object Panic extends CmdsMod


sealed abstract class ConcreteValue{
    def valueClone: ConcreteValue;
}
case class ConcreteUndef () extends ConcreteValue{
    override def valueClone: ConcreteValue = new ConcreteUndef ();
}
case class ConcreteBool (value: Boolean) extends ConcreteValue{
    override def toString = value.toString
    override def valueClone: ConcreteValue = new ConcreteBool(value);
} 
case class ConcreteInt (value: BigInt) extends ConcreteValue{
    override def toString = value.toString
    override def valueClone: ConcreteValue = new ConcreteInt(value);
} 
case class ConcreteBV (value: BigInt, width: Int) extends ConcreteValue{
    override def toString = value.toString+"bv"+width.toString;
    override def valueClone: ConcreteValue = new ConcreteBV(value,width);
} 

case class ConcreteArray (value: Map[List[ConcreteValue], ConcreteValue]) extends ConcreteValue{
    override def toString = value.toString;
    override def valueClone = new ConcreteArray(value.clone);
} 
case class ConcreteRecord (value: Map[Identifier, ConcreteValue]) extends ConcreteValue{
    override def toString = value.toString;
    override def valueClone = new ConcreteRecord(value.clone);
} 
case class ConcreteEnum (ids:List[Identifier], value: Int) extends ConcreteValue{
    override def toString = {
        if (value >=0) ids(value).toString
        else "Enum undefined"
    }
    override def valueClone = new ConcreteEnum(ids, value)
}

object ConcreteSimulator {
    //debug useful flag
    var isPrintResult: Boolean = true;
    var isPrintDebug: Boolean = false;


    //cmds requirements
    var runtimeMod: CmdsMod = Panic;
    var jsonFileName = "Null";
    var needToPrintResults = false;
    var needToPrintTrace = false;
    
    
    //runtime count data
    var terminate: Boolean = false;
    var trace = Map[BigInt,ConcreteContext]();
    var passCount: Int = 0;
    var failCount: Int = 0;
    var undetCount: Int = 0;
    var cntInt:Int = 0;
    var terminateInt: Int = 0;
    
    //util
    val random = new Random()
    case class ConcreteContext() {
        var varMap: scala.collection.mutable.Map[Identifier, ConcreteValue] = collection.mutable.Map();
        var inputMap: scala.collection.mutable.Map[Identifier, ConcreteValue] = collection.mutable.Map();
        var outputMap: scala.collection.mutable.Map[Identifier, ConcreteValue] = collection.mutable.Map();

        val assumeTable: ArrayBuffer[Expr] = ArrayBuffer.empty[Expr];
        val assumeRecommendTable: scala.collection.mutable.Map[Identifier, ConcreteValue] = collection.mutable.Map();
        
        def read (variable: Identifier) : ConcreteValue = {
            if (varMap.contains(variable)) varMap(variable)
            else if (inputMap.contains(variable)) inputMap(variable)
            else throw new Error(f"Variable ${variable.toString} not found in context")}
        def write (variable: Identifier, value: ConcreteValue) {
            if (varMap.contains(variable)) varMap(variable) = value
            else if (inputMap.contains(variable)) inputMap(variable) = value
            else throw new Error(f"Variable ${variable.toString} not found in context")}
        def updateVar (lhs: Lhs, value: ConcreteValue) {
            lhs match {
                case LhsId(id) => {
                    varMap(id) = value
                }
                case LhsArraySelect(id, indices) => {
                    varMap(id) match {
                        case ca: ConcreteArray => {
                            // List of concrete indices expressions 
                            val eval_indices = indices.map(a => evaluate_expr(this, a)) 
                            var old_map = ca.value // old array 
                            old_map(eval_indices) = value
                            val new_arr = ConcreteArray(old_map)
                            varMap(id) = new_arr
                        }
                        case _ => 
                            throw new Error(f"Attempting ArraySelect on a non-array object ${id.name}")
                    }
                }
                case LhsRecordSelect(id, fieldid) => {
                    printDebug(s"Update: record ${id.toString}, fieldid ${fieldid}")
                    varMap(id) = updateRecordValue(fieldid, value, varMap(id))  
                }
                case _ => {
                    throw new NotImplementedError(s"LHS Update for ${lhs}")
                }
            }}

        def extendVar (vars: List[(Identifier, Type)]) : Unit = {
            var enumContext = collection.mutable.Map[Identifier, ConcreteValue]()
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
                    // TODO: ... fill in
                    case ArrayType(inType, outType) => {
                        // TODO: outType could be complex type like another array or record
                        (v._1, ConcreteArray(scala.collection.mutable.Map[List[ConcreteValue], ConcreteValue]().withDefaultValue(ConcreteUndef())))
                    }
                    case RecordType(members) => {
                        (v._1, ConcreteRecord(scala.collection.mutable.Map(members.map(m => (m._1, ConcreteUndef())): _*)))
                    }
                    case EnumType(ids) => {
                        for ((id,i) <- ids.view.zipWithIndex) {
                            enumContext(id) = ConcreteEnum(ids, i)
                        }
                        // TODO: Should this be ConcreteUndef?
                        (v._1, ConcreteEnum(ids, -1))
                    }   
                    case _ => {
                        throw new NotImplementedError(v.toString + " has not been supported yet!")
                    }
                }) : _*
            )
            varMap = varMap.++(newContext);}
        
        def removeVar (vars: List[(Identifier, Type)]) : Unit = {
            for ((variable_name, variable_type) <- vars) {
                varMap.-(variable_name)
            }}
    
        def extendVarJson(frame:Int, vars: List[(Identifier, Type)]): Unit= {
            // TODO: grab values from JSON file that are mentioned in vars and copy into context.varMap(frame)
            // val jsonString: String = Source.fromFile("cex.json").mkString;
            // //println("So, json file name is "+jsonFileName);
            // // Parse JSON into case class
            // implicit val formats: DefaultFormats.type = DefaultFormats
            
            // // Parse JSON into a JValue, provided by the json4s class
            // val json: JValue = parse(jsonString)

            // def parseArray(array: List[JValue]): List[String] = {
            //     array.collect {
            //         case JString(value) => value
            //         }
            //     }
            // def findValueforVar(value: String, vars: List[(Identifier, Type)], varName: Identifier): ConcreteValue = {
            //     /*
            //     This function will go through the list of variables to find and create the proper variable type for the identifier passed into varName.
            //     */
            //     for (variable <- vars) {
            //         if (variable._1 == varName) {
            //             variable._2 match {
            //                 case IntegerType() => {
            //                     return ConcreteInt(BigInt(value))
            //                 }
            //                 case BooleanType() => {
            //                     return ConcreteBool(value.toBoolean)
            //                 }
            //             }
            //         }
                    
            //     }
            //     return ConcreteInt(5)
            // }
            // def parseTrace(trace: JValue, frame: Int, vars: List[(Identifier, Type)]): scala.collection.mutable.Map[String, ConcreteValue] = {
            //     trace match {
            //         case JObject(item) =>
            //             val tuple = item(1)._2
            //             val myMap: collection.mutable.Map[String, ConcreteValue] = collection.mutable.Map()
            //             tuple match {
            //                 case JArray(list) =>
            //                     var i: Int = 0
            //                     for (it <- list) {
            //                         if (i == frame) {
            //                             it match {
            //                                 case JObject(item2) => {
            //                                     item2.foreach {
            //                                         listItem => {
            //                                             var varName = listItem._1
            //                                             listItem._2 match {
            //                                                 case JArray(list) => 
            //                                                     list.foreach {
            //                                                         item3 =>
            //                                                         item3 match {
            //                                                             case JString(value) =>
            //                                                                 var varValue: ConcreteValue = findValueforVar(value, vars, Identifier(varName))
            //                                                                 myMap += (varName -> varValue)
            //                                                         }

            //                                                     }
            //                                             }
            //                                         }
            //                                     }
            //                                 }
            //                             }
            //                         }
            //                         i = i + 1
            //                     }

            //             }
            //             // printDebug("Final Map: " + myMap)  
            //             return myMap 
            // }
            

            // }
                

            // val properties: Map[String, JValue] = json.extract[Map[String, JValue]]
            // val propertyName = "property__jump_b__0"
            // val property = properties(propertyName)
            // val valueMap = parseTrace(property, frame, vars)

            // val finalContext : scala.collection.mutable.Map[Identifier, ConcreteValue] = collection.mutable.Map()
            
            // // for every variable in context, get the value from the valueMap
            // context.foreach { 
            //     case (key, value) =>
            //     // val newValue: Identifier = key.toIdentifier
            //     println(value)
            //     val newvalue = valueMap(key.toString)
            //     finalContext += (key -> newvalue)
            // }
            // printDebug("")      
            // //printVar(finalContext, List())
            // finalContext
            // // context
            ;}

        def assignUndefVar(vars: List[(Identifier, Type)],isInput: Boolean): Unit = {
            //TODO:
            //to make sure the ganerateValue is not out of AssumeTable
            if(isInput){
                var retContext = inputMap;
                for ((key, value) <- inputMap){     
                    for((id,typ) <- vars){
                        if(key == id){
                            //if we do not have recommend assign value and the random does work, do random again
                            var cnt: Int = 0;

                            retContext(key) = ganerateValue(value,typ,isInput)
                            while(!checkAssume() && (!assumeRecommendTable.contains(id))){
                                retContext(key) = ganerateValue(value,typ,isInput)
                                cnt = cnt +1;
                                if(cnt>100){
                                    println("Now the rTable is "+assumeRecommendTable.toString)
                                    throw new Error("inifinte Loop for getting value of "+key.toString)
                                }
                            }
                            //random does not work and we have recommend value
                            if(!checkAssume()&assumeRecommendTable.contains(id)){
                                retContext(key) = assumeRecommendTable(id)
                            }
                        }
                    }
                }
                inputMap = retContext
            }
            else{
                    //Loop over the context and assign good value according its type
                var retContext = varMap;
                //check the varMap
                for ((key, value) <- varMap){     
                    for((id,typ) <- vars){
                        if(key == id){
                            //if we do not have recommend assign value and the random does work, do random again
                            var cnt: Int = 0;

                            retContext(key) = ganerateValue(value,typ,isInput)
                            while(!checkAssume() && (!assumeRecommendTable.contains(id))){
                                retContext(key) = ganerateValue(value,typ,isInput)
                                cnt = cnt +1;
                                if(cnt>100){
                                    println("Now the rTable is "+assumeRecommendTable.toString)
                                    throw new Error("inifinte Loop for getting value of "+key.toString)
                                }
                            }
                            //random does not work and we have recommend value
                            if(!checkAssume()&assumeRecommendTable.contains(id)){
                                retContext(key) = assumeRecommendTable(id)
                            }
                        }
                    }
                }
                varMap = retContext
            }}
        def cloneObject: ConcreteContext ={
            var clone = new ConcreteContext();
            for((key,value)<-varMap){
                clone.varMap(key) = value.valueClone;
            }
            for((key,value)<-inputMap){
                clone.inputMap(key) = value.valueClone;
            }
            for((key,value)<-outputMap){
                clone.outputMap(key)= value.valueClone;
            }
            clone}

        def removeExtraVar ( vars: List[(Identifier, Type)], oldContext: ConcreteContext) : Unit = {
            for (id <-vars ){
                varMap.-(id._1);
                if(oldContext.varMap.contains(id._1)){
                    varMap += (id._1->oldContext.varMap(id._1))
                }
            }}

        def extendInputVar ( vars: List[(Identifier, Type)]) : Unit= {
            var returnContext = inputMap;
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
            inputMap = returnContext;}

        def parseSetAssume(expr:Expr): Unit = {
            assumeTable += expr;
            //Expermential:
            //Might introducing bugs
            //TODO:
            //better recommend Table for assume
            evaluate_expr(this,expr) match{
                case ConcreteBool(true)=>{}
                case ConcreteBool(false)|ConcreteUndef()=>{
                //if we hit assume evlation with the result
                    expr match {
                        case id:Identifier =>{
                            assumeRecommendTable(id) = ConcreteBool(true)
                            write(id,ConcreteBool(true))
                        }
                        case OperatorApplication(op:Operator, operands:List[Expr])=>{
                            if(operands.size==1){
                                throw new Error("wait for implement")
                            }
                            else{
                                val operand_0 = operands.head;
                                val operand_1 = operands.tail.head
                                op match{
                                    case EqualityOp()=> {
                                        operand_0 match{
                                            case id:Identifier =>{
                                                printDebug("Write "+id+" "+operand_1.toString)
                                                assumeRecommendTable(id) = evaluate_expr(this,operand_1)
                                                write(id,evaluate_expr(this,operand_1))
                                            }
                                            case _ => {
                                                throw new Error("Undefine ? "+operand_0)
                                            }
                                        }    
                                    }
                                    case InequalityOp() => {
                                        throw new Error("Unimplemented")
                                        //ConcreteBool(bool_0 != bool_1)
                                    }
                                    case ConjunctionOp() =>{ 
                                        parseSetAssume(operand_0)
                                        parseSetAssume(operand_1)
                                    }
                                    // case DisjunctionOp() => ConcreteBool(bool_0 || bool_1)
                                    // case IffOp() => ConcreteBool(bool_0 == bool_1)
                                    // case ImplicationOp() => ConcreteBool(!bool_0 || bool_1) 
                                    case _ => {

                                    }    
                                }
                            }
                        }
                        case _ => {
                            throw new Error("Hit unimplemented code part")
                        }
                    }    
                }
                case _ => {
                    throw new Error("Hit unimplemented code part")
                }
            }}

        
        //function gathring value as we want
        def ganerateValue(cValue:ConcreteValue,uclidType:Type,isInput:Boolean): ConcreteValue={        
            cValue match{
                case ConcreteUndef() =>{
                    uclidType match{
                        case IntegerType()      =>  {
                            runtimeMod match{
                                case Fuzzing => ConcreteInt(random.nextInt())
                                case Default => ConcreteInt(0)
                                case _ => ConcreteUndef()
                            }   
                        }
                        case BooleanType()      =>  {
                            runtimeMod match{
                                case Fuzzing => ConcreteBool(random.nextBoolean())
                                case Default => ConcreteBool(false)
                                case _ => ConcreteUndef()
                            }
                        }
                        case BitVectorType(w)   =>  {
                            runtimeMod match{
                                case Fuzzing => ConcreteBV(random.nextInt(pow(2,w).toInt),w)
                                case Default => ConcreteBV(0,w)
                                case _ => ConcreteUndef()
                            }
                        }
                        case _ => throw new NotImplementedError("Does not support type "+uclidType) 
                    }
                }
                case ConcreteBool(b) =>{
                    if(isInput){
                        runtimeMod match{
                            case Fuzzing => ConcreteBool(random.nextBoolean())
                            case Default => ConcreteBool(false)
                            case _ => ConcreteUndef()
                        }
                    }
                    else
                        ConcreteBool(b)
                }
                case ConcreteInt(v) =>  {
                    if(isInput){
                        runtimeMod match{
                            case Fuzzing => ConcreteInt(random.nextInt())
                            case Default => ConcreteInt(0)
                            case _ => ConcreteUndef()
                        }   
                    }
                    else
                        ConcreteInt(v)
                }
                case ConcreteBV(v,w)   =>  {
                    if(isInput){
                         runtimeMod match{
                            case Fuzzing => ConcreteBV(random.nextInt(pow(2,w).toInt),w)
                            case Default => ConcreteBV(0,w)
                            case _ => ConcreteUndef()
                        }
                    }    
                    else
                        ConcreteBV(v,w)
                }
                case ConcreteRecord(members) =>{
                    uclidType match{
                        case RecordType(members)=>{
                            var RecordMap = scala.collection.mutable.Map[Identifier, ConcreteValue]();
                            for((mem_id,mem_typ)<-members){
                                mem_typ match{
                                    case IntegerType() => {
                                        runtimeMod match{
                                            case Fuzzing => RecordMap(mem_id) = ConcreteInt(random.nextInt())
                                            case Default => RecordMap(mem_id) = ConcreteInt(0)
                                            case _ => RecordMap(mem_id) = ConcreteUndef()
                                        }
                                    }
                                    
                                    case BooleanType() => {
                                        runtimeMod match{
                                            case Fuzzing => RecordMap(mem_id) = ConcreteBool(random.nextBoolean())
                                            case Default => RecordMap(mem_id) = ConcreteBool(false)
                                            case _ => RecordMap(mem_id) = ConcreteUndef()
                                        }
                                    }
                                    case BitVectorType(w) => {
                                        runtimeMod match{
                                            case Fuzzing => RecordMap(mem_id) = ConcreteBV(random.nextInt(pow(2,w).toInt),w)
                                            case Default => RecordMap(mem_id) = ConcreteBV(0,w)
                                            case _ => RecordMap(mem_id) = ConcreteUndef()
                                        }
                                    }
                                       
                                    case _ => throw new NotImplementedError("Does not implement support for this type\n")
                                }
                            }
                            ConcreteRecord(RecordMap)
                        }
                        case _ => throw new NotImplementedError("Does not implement support for this type\n")
                    }
                }
                //TODO:
                //assign Variable for Array and enum
                case _ => cValue
            }    
        }
        
        //private Functions
        def updateRecordValue(fields: List[Identifier], value: ConcreteValue, 
            recordValue: ConcreteValue) : ConcreteRecord = {
            if (fields.size == 1) {
                recordValue match {
                    case ConcreteUndef() => ConcreteRecord(Map(fields.head -> value))
                    case ConcreteRecord(map) => {
                        map(fields.head) = value
                        ConcreteRecord(map)
                    }
                    case _ => throw new NotImplementedError(s"UpdateRecord applied to non-Record type")
                }
            } else {
                // now, we have one recordValue and we have not touch the end of the Record
                recordValue match{
                    case ConcreteUndef() => 
                        ConcreteRecord(Map(fields.head->updateRecordValue(fields.tail, value, ConcreteUndef())))
                    case ConcreteRecord(map) => {
                        val newrec = updateRecordValue(fields.tail, value, map(fields.head))
                        map(fields.head) = newrec
                        ConcreteRecord(map)
                    }
                    case _ => throw new NotImplementedError(s"UpdateRecord applied to non-Record type")
                }
            }}
        
        def checkAssume(): Boolean ={
            var ret: Boolean = true;
            for(expr <- assumeTable){
                ret = ret && evaluateBoolExpr(this,expr)
            }
            ret}
        //Debuging Functions
        def printVar (vars: List[(Expr, String)]) : Unit = {
            if (vars.isEmpty) {
                println("\tVarmap:")
                for ((key,value) <- varMap){
                    println(s"${key.toString}: ${value.toString}")
                }
                println("\n")
            }
            for (variable <- vars){
                println(variable._1 + ":  " + ConcreteSimulator.evaluate_expr(this,variable._1).toString)
            }}
        
        def printInput (vars: List[(Expr, String)]) : Unit = {
            printDebug("\tInput map:")
            if(vars.isEmpty){
                for((key,value)<-inputMap){
                    println(key.toString+": "+value.toString)
                }
                if(isPrintDebug)
                    println("\n")
            }
            for (variable <- vars){
                println(variable._1+":  "+ConcreteSimulator.evaluate_expr(this,variable._1).toString)
            }}
    }
    
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

                    if(cmd.args.size==2){
                        var (idArg,exprArg) = cmd.args(1);
                        if(idArg.toString == "\"Default\""){
                            runtimeMod = Default;
                        }
                        // TODO: improve this to random without quotes
                        // ""control { concrete (random) }"" and not ""control { concrete ("random") }""
                        if(idArg.toString == "\"Random\""){
                            runtimeMod = Fuzzing;
                        }
                        if(idArg.toString == "\"Json\""){
                            runtimeMod = Json;
                        }
                    }
                }
                case "print_concrete_trace" =>{
                    needToPrintTrace = true;
                    printTraceCmd = cmd;
                }
                case _ => {}
            }
        }

        val frame = 0
        var concreteContext:ConcreteContext = new ConcreteContext();        
        concreteContext.extendVar(module.vars);
        concreteContext.extendInputVar(module.inputs)
        concreteContext.extendVar(module.outputs)
        
        setAssumes(module.axioms,concreteContext);

        concreteContext.assignUndefVar(module.vars,false)
        concreteContext.assignUndefVar(module.inputs,true)

        module.init match{
            case Some(init) => simulate_stmt(concreteContext,init.body)
            case _ => {}
        }
        
        checkAssumes(module.axioms,concreteContext);
        checkProperties(properties,concreteContext);
        trace(0) = concreteContext.cloneObject;
        
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
                    for (a <- 1 to cntInt) {
                        if (!terminate) {
                            concreteContext.assignUndefVar(module.inputs,true)
                            simulate_stmt(concreteContext, next.body)
                            checkProperties(properties,concreteContext)
                            trace(a) = concreteContext.cloneObject;
                            terminateInt = a;   
                        } 
                        else {
                            if (!terminate_printed) {
                                printDebug(s"Failed on iteration ${a-1}")
                                terminate_printed = true
                            }    
                        }
                    }
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


    def simulate_stmt (context: ConcreteContext, stmt: Statement): Unit = {
        stmt match {
            case AssignStmt(lhss, rhss) => {
                printDebug("Simulate assign Stmt: "+stmt.toString)
                val rhseval = rhss.map(rhs => evaluate_expr(context, rhs))
                for((lhssid,i)<-lhss.view.zipWithIndex){
                    context.updateVar(lhss(i),rhseval(i))
                };
            }
            case BlockStmt(vars, stmts) => {
                val flatVars : List[(Identifier, Type)] = vars.flatMap(v => v.ids.map(id => (id, v.typ)))
                context.extendVar(flatVars)
                val oldContext = context.cloneObject;
                for(s<-stmts){
                    simulate_stmt(context, s)
                }
                context.removeExtraVar(flatVars,oldContext)
                }
            
            case SkipStmt() => {}
            case AssertStmt(e, id) => {
                printDebug("Evaluate AssertStmt "+e.toString)
                if (!evaluateBoolExpr(context, e)){ 
                    failCount = failCount+1;
                    terminate = true;
                    printResult("failed assert statement on:\n "+stmt)
                }else{
                    passCount = passCount+1;
                }}
            case AssumeStmt(e, id) => {
                context.parseSetAssume(e)
            }
            case HavocStmt(havocable) => throw new NotImplementedError(s"HavocStmt not implemented")
            case IfElseStmt(cond, ifblock, elseblock) => {
                if (evaluateBoolExpr(context, cond)) {
                    simulate_stmt(context, ifblock)
                } else {
                    simulate_stmt(context, elseblock)
                }}
            case ForStmt(id, typ, range, body) => {
                var low = evaluate_expr(context, range._1)
                var high = evaluate_expr(context, range._2)
                context.extendVar(List((id,typ)))
                typ match {
                    case IntegerType() => {
                        val low_ = low match {
                            case l: ConcreteInt => l.value
                        }                        
                        val high_ = high match {
                            case h : ConcreteInt => h.value
                        }
                        for(it <- low_ to high_){
                            context.write(id,ConcreteInt(it))
                            simulate_stmt(context,body)
                        }
                    }
                    case BitVectorType(w) => {
                        val low_ = low match{
                            case l: ConcreteBV  => l.value
                        }
                        val high_ = high match{
                            case h: ConcreteBV => h.value
                        }
                        for(it <- low_ to high_){
                            context.write(id,ConcreteBV(it,w))
                            simulate_stmt(context,body)
                        }
                    }
                    case _ => throw new Error("Does not support loop index of type "+ typ.toString)
                }
                context.removeVar(List((id,typ)))}
            case WhileStmt(cond, body, invariants) => {
                while(evaluateBoolExpr(context, cond)){
                    simulate_stmt(context, body)
                }}
            case CaseStmt(body) => throw new NotImplementedError("We have not implemented Case stmt")
            case ProcedureCallStmt(id, callLhss, args, instanceId, moduleId) => {
                throw new NotImplementedError(s"ProcedureCallStmt not implemented")}
            case MacroCallStmt(id) => {
                throw new NotImplementedError(s"MacroCallStmt not implemented")}
            case ModuleCallStmt(id) => {
                throw new NotImplementedError(s"ModuleCallStmt not implemented")}
            case _ => throw new NotImplementedError("We have not implemented Stmt "+ stmt.toString)
        }}
    def evaluateBoolExpr(context: ConcreteContext,
        cond: Expr) : Boolean = {
            printDebug("Evaluate BoolExpr "+cond.toString)
            evaluate_expr(context,cond) match {
                case ConcreteBool(b) => {
                    if (b) {
                        return true
                    } else {
                        return false
                    }
                }
                case ConcreteUndef() => {
                    context.printVar(List())
                    context.printInput(List())
                    throw new Error("When Evaluation Bool value we hit a undefine value "+cond.toString)
                }
            }
        }

    def evaluate_expr (context: ConcreteContext, 
        expr: lang.Expr) : ConcreteValue = {
        printDebug("Evaluate Expr: "+expr.toString)
        expr match {
            case a : Identifier => {
                context.read(a) match {
                    case ConcreteUndef() => {
                        
                        if(isPrintDebug){
                            printDebug("Here we hit a undefine value: "+a.toString)
                            context.printVar(List())
                            context.printInput(List())
                        }
                        ConcreteUndef()
                    }
                    case _ => context.read(a)
                }    
            }
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
                            printDebug("Read Value fomr ConcreteArray: "+valuemap.toString)
                            op match {
                                case ArraySelect(indices) => {
                                    val eval_indices = indices.map(a => evaluate_expr(context,a)) // list of concrete expr
                                    printDebug("\t With indices " + indices)
                                    printDebug("\t With newMap " + eval_indices)
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
                                        throw new NotImplementedError("We hit a undefineValue "+id.toString)
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
                                        case EqualityOp() => ConcreteBool(bool_0 == bool_1)
                                        case InequalityOp() => ConcreteBool(bool_0 != bool_1)
                                        case ConjunctionOp() => ConcreteBool(bool_0 && bool_1)
                                        case DisjunctionOp() => ConcreteBool(bool_0 || bool_1)
                                        case IffOp() => ConcreteBool(bool_0 == bool_1)
                                        case ImplicationOp() => ConcreteBool(!bool_0 || bool_1)
                                        case _ => throw new NotImplementedError("Not implements the Operator for Bool"+op.toString) 
                                    }
                                }
                                case ConcreteUndef() => {
                                    undetCount = undetCount + 1;
                                    ConcreteUndef()
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
                                case ConcreteUndef() => {
                                    undetCount = undetCount + 1;
                                    if(isPrintDebug){
                                        printDebug("Here we hit a undefine value: "+operands.head.toString)
                                        context.printVar(List())
                                        context.printInput(List())
                                    }
                                    ConcreteUndef()
                                }
                                case _ => throw new NotImplementedError("add integer with undefine value of "+ expr.toString) 
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
                                        case EqualityOp() => ConcreteBool(int_0 == int_1)
                                        case InequalityOp() => ConcreteBool(int_0 != int_1)
                                        case _ => throw new NotImplementedError("Not implements the Operator for BV"+op.toString) 
                                    }
                                }
                                case ConcreteUndef() => {
                                    undetCount = undetCount + 1;
                                    printDebug("Here we hit a undefine value: "+operands.tail.head.toString)
                                    context.printVar(List())
                                    context.printInput(List())
                                    throw new NotImplementedError("Runtime Panic on variable "+operands.tail.head.toString)
                                }
                                case _ => {
                                    //printVar(context,List());
                                    throw new NotImplementedError("Operand_1 is "+operands.tail.head.toString)
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
                                case ConcreteUndef() => {
                                    undetCount = undetCount + 1;
                                    if(isPrintDebug){
                                        printDebug("Here we hit a undefine value: "+operands.head.toString)
                                        context.printVar(List())
                                        context.printInput(List())
                                    }
                                    ConcreteUndef()
                                }
                            }
                        }
                        case ConcreteUndef() => {
                            undetCount = undetCount + 1;
                            ConcreteUndef()
                        }
                        case _ => {
                            throw new NotImplementedError("Does not support operation on this type yet")
                        }
                    }
                }
                
            }
            case _ => throw new NotImplementedError(s"Expression evaluation for ${expr}")
        }}
        
    def checkAssumes(assumes: List[AxiomDecl],context:ConcreteContext){
        for(assume<-assumes){
            if (!evaluateBoolExpr(context, assume.expr)){ 
                    failCount = failCount+1;
                    terminate = true
                    printResult("failed assume statement")
                    printResult("failed on "+assume.toString)
                    context.printVar(List())
                    context.printInput(List())
                    throw new Error("We should not make fail assume")
                    
                }else{
                    passCount = passCount+1;
                }
        }}
    def setAssumes(assumes: List[AxiomDecl],context:ConcreteContext): Unit ={
        for(assume<-assumes){
            //we need to reparse the exper;
            //We assume user use conjunctive normal form(CNF)
            //transform any logic experssion into 
            context.parseSetAssume(assume.expr)
        }
    }

    def checkProperties(properties: List[SpecDecl],context:ConcreteContext){
        for(property <- properties){
            printDebug("Check Property "+property.toString)
            //printVar(context,List())
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
    def printConcretetTrace(trace:Map[BigInt,ConcreteContext],exprs : List[(Expr, String)], arg : Option[Identifier]){
        UclidMain.printStatus("Generated Trace of length " + (terminateInt).toString())
        UclidMain.printStatus("=================================")
        printDebug("The terminateInt is "+terminateInt.toString)
        printDebug("The trace's size is "+trace.size)
        for (a <- 0 to terminateInt) {
            if(a<=terminateInt){
                UclidMain.printStatus("=================================")
                UclidMain.printStatus("Step # "+a.toString)
                trace(a).printVar(exprs)
                UclidMain.printStatus("=================================")
            }
        }}
}
