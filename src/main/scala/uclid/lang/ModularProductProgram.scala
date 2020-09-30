package uclid
package lang


import scala.collection.immutable.Map
import com.typesafe.scalalogging.Logger
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.annotation.tailrec

class ModularProductHelper {

    /* Data Structures Required for the translation of each Procedure */
    var mapOfRenamedVariables = mutable.Map[(Identifier, Type), Array[Identifier]]()
    var mapOfActivationVariables = mutable.Map[Int, Array[(Identifier)]]()
    var mapOfNewVariables = mutable.Map[Int, Array[(Identifier)]]()
    var mapOfRenamedVarDecls = mutable.Map[Int, ListBuffer[BlockVarsDecl]]()
    var maxScope = 0        //Keeps track of scope of Activation Variables Created
    var maxVarScope = 0     //Keeps track of Scope of New Variables Created 

    def addToRenameVariableMap(k:Int, paramlist: List[(Identifier, Type)]): Unit = {
        if(!paramlist.isEmpty) {
            val variable = paramlist.head
            val keyArray = new Array[Identifier](k)
            for( i <- 0 until k)
                keyArray(i) = Identifier(variable._1.toString + "." + (i+1).toString)
            mapOfRenamedVariables +=(variable -> keyArray)
            addToRenameVariableMap(k, paramlist.tail)
        }
    }   
}

class ModularProductProgramPass extends RewritePass {

    lazy val log = Logger(classOf[ModularProductProgram])

    var newDecls = ListBuffer[ProcedureDecl]()                          //list of procedure translations for each procedure 
    var newModuleDecls = ListBuffer[Decl]()                             //new module with translated procedures and control block
    var procedureMap = Map[ProcedureDecl, Array[ProcedureDecl]]()       //Map : old procedure -> new procedures
    var procWithRelSpec = Map[ProcedureDecl, (Boolean, Array[Int])]()   //Map : old proc -> (hasHyperSelect, Array of copy values)
    var procWithRelSpecUtil = Map[Identifier, (Boolean, Array[Int])]()  //Map: old proc id -> (hasHyperSelect, Array of copy values)

    /*
        This checks if the operands use Trace Select Operation and returns the corresponding trace value if yes else 1
        For eg. for the expression (variable.1 == (variable.2 + variable.3)) , it returns 3 
    */
    def checkHyperSelectOp(op: Operator, operands: List[Expr], copies: Int): Int = op match {
            case HyperSelect(i) => 
                if (i==0) 
                    throw new Utils.ParserError("Trace Value cannot be zero", Some(op.pos), op.filename)
                i
            
            case _ => 
                val maxCopyList: List[Int] = operands.map {
                    case OperatorApplication(op_, operands_) => checkHyperSelectOp(op_, operands_, copies)
                    case _ => 1
                }
                (maxCopyList foldLeft 1)(Math.max)
    }

    def modularProduct(k:Int, proc : ProcedureDecl, helperObj: ModularProductHelper, ctxx: Scope): ProcedureDecl = {

        val newVarDeclarations = ListBuffer[BlockVarsDecl]()    //contains activationDecarations in proc body
        val newRequiresList = ListBuffer[Expr]()                //contains modified preconditions     
        val newEnsuresList = ListBuffer[Expr]()                 //contains modified postconditions
        val newModifiesList = Set[ModifiableEntity]()                 //unused now. Can be used later if module variables are supported
        

        def createActivationVariables(k: Int, actVariableMap: mutable.Map[Int, Array[Identifier]], level: Int): BlockVarsDecl = {
            val keyArray = new Array[Identifier](k) //0 to k-1
    
            /* Activation Variables are named in this manner 
                actVari_j --> where i corresponds to level/scope and j corresponds to the jth copy of execution
            */
            val listOfIdentifiers = new ListBuffer[Identifier]()
            val datatype: Type = BooleanType()
            for ( i <- 0 until k)
            {
                val idDecl = Identifier("actVar" + level + "$" + (i+1).toString)
                listOfIdentifiers += idDecl
                keyArray(i) = idDecl
            }
            val activationVarsDecl = BlockVarsDecl(listOfIdentifiers.toList, datatype)
            actVariableMap+=(level -> keyArray )
            activationVarsDecl
        }

        def createReturnVariables(k: Int, actVariableMap: mutable.Map[Int, Array[Identifier]], level: Int, typ: Type): BlockVarsDecl = {
            val keyArray = new Array[Identifier](k) //0 to k-1

            /* New Variables are named in this manner 
                newVari_j --> where i corresponds to level/scope and j corresponds to the jth copy of execution
            */

            val listOfIdentifiers = ListBuffer[Identifier]()
            val datatype = typ
            for ( i <- 0 until k)
            {
                val idDecl = Identifier("newVar" + level + "$" + (i+1).toString)
                listOfIdentifiers += idDecl
                keyArray(i) = idDecl
            }
            val activationVarsDecl = BlockVarsDecl(listOfIdentifiers.toList, datatype)
            actVariableMap+=(level -> keyArray )
            activationVarsDecl
        }

        /*
            This method goes through the procedure body and checks all the activation variables that will be
            required in total, adds them to activation variable map.
        */

        def findRequiredActivationVariables(stmts: List[Statement], currentScope: Int, context: Scope): Unit = {
            if(!stmts.isEmpty) {
                stmts.head match {
                    case BlockStmt(vars, blockstmts) =>
                        findRequiredActivationVariables(blockstmts, currentScope, context + vars)
                    case IfElseStmt(_, ifblock, elseblock) => 
                        val activationVarsDecl1 = createActivationVariables(k,helperObj.mapOfActivationVariables,helperObj.maxScope+1)
                        val activationVarsDecl2 = createActivationVariables(k,helperObj.mapOfActivationVariables,helperObj.maxScope+2)
                        if(!ifblock.asInstanceOf[BlockStmt].stmts.isEmpty)
                        {
                            ASTNode.introducePos(true, true, activationVarsDecl1, ifblock.asInstanceOf[BlockStmt].stmts.head.position)
                            ASTNode.introducePos(true, true, activationVarsDecl2, ifblock.asInstanceOf[BlockStmt].stmts.head.position)
                        }
                        if(!elseblock.asInstanceOf[BlockStmt].stmts.isEmpty)
                            ASTNode.introducePos(true, true, activationVarsDecl2, elseblock.asInstanceOf[BlockStmt].stmts.head.position)
                        val ifScope = helperObj.maxScope + 1
                        val elseScope = helperObj.maxScope + 2
                        helperObj.maxScope += 2
                        newVarDeclarations ++= List(activationVarsDecl1, activationVarsDecl2)
                        findRequiredActivationVariables(ifblock.asInstanceOf[BlockStmt].stmts, ifScope, context + ifblock.asInstanceOf[BlockStmt].vars)
                        findRequiredActivationVariables(elseblock.asInstanceOf[BlockStmt].stmts, elseScope, context + elseblock.asInstanceOf[BlockStmt].vars)
                    
                    case WhileStmt(_, body, _) => 
                        val activationVarsDecl = createActivationVariables(k,helperObj.mapOfActivationVariables,helperObj.maxScope+1)
                        if(!body.asInstanceOf[BlockStmt].stmts.isEmpty)
                            ASTNode.introducePos(true, true, activationVarsDecl, body.asInstanceOf[BlockStmt].stmts.head.position)
                        val nextScope = helperObj.maxScope + 1
                        helperObj.maxScope+=1
                        newVarDeclarations += activationVarsDecl
                        findRequiredActivationVariables(body.asInstanceOf[BlockStmt].stmts, nextScope, context + body.asInstanceOf[BlockStmt].vars)
                    
                    case ProcedureCallStmt(_, callLhss, args, _, _) =>                 
                        def getType(exp: Expr): Type = exp match {
                            case FuncApplication(e, _) => 
                                val typeOfIdentifier = ctxx.get(e.asInstanceOf[Identifier])
                                typeOfIdentifier match {
                                    case Some(value) => value.typ.asInstanceOf[MapType].outType
                                    case None =>    
                                        val msg = "Function used inside Procedure Call Statement doesn't have a return type: %s".format(e.toString)
                                        throw new Utils.TypeError(msg, Some(e.pos), e.filename)
                                }
                            case _ =>
                                val typechecker = new ExpressionTypeCheckerPass
                                typechecker.typeOf(exp, context)
                        }
                        
                        def createArgsCopy(args: List[Expr]):Unit= {
                            if(!args.isEmpty) {
                                val expr = args.head
                                val typ = getType(expr)
                                val activationVarsDecl = createReturnVariables(k, helperObj.mapOfNewVariables, helperObj.maxVarScope+1, typ)
                                newVarDeclarations += activationVarsDecl
                                helperObj.maxVarScope+=1
                                createArgsCopy(args.tail)
                            }

                        }

                        def createReturnVariablesCopy(callLhss: List[Lhs]):Unit = {
                            if(!callLhss.isEmpty) {
                                val lhs = callLhss.head
                                val typ = getType(lhs.ident.asInstanceOf[Expr])
                                val activationVarsDecl = createReturnVariables(k, helperObj.mapOfNewVariables, helperObj.maxVarScope+1, typ)
                                newVarDeclarations += activationVarsDecl
                                helperObj.maxVarScope +=1
                                createReturnVariablesCopy(callLhss.tail)
                            }
                        }

                        
                        createArgsCopy(args)  //create k copies for each procedure call argument
                        createReturnVariablesCopy(callLhss) //create k copies of each return value

                    case _ => 
                }
                findRequiredActivationVariables(stmts.tail, currentScope, context)
            }
        }

        /*
            This method goes through the body and gets all the local variables. 
            It adds their renamed versions to mapOfRenamedVariables
            For eg, an entry for copy = 3 will be (a -> a1,a2,a3)
        */
        def collectRenamedVariables(block: BlockStmt):Unit = {

            //This goes through the Procedure Block Vars and adds their renamed versions to map
            @tailrec
            def collectRenamedVariablesFromBlockVars(vars: List[BlockVarsDecl]):Unit = {
                if(!vars.isEmpty)
                {
                    val variables = vars.head
                    for( variable <- variables.ids)
                    {
                        val keyArray = new Array[Identifier](k)
                        for( i <- 0 until k)
                            keyArray(i) = Identifier(variable.toString + "." + (i+1).toString)

                        helperObj.mapOfRenamedVariables+=((variable,variables.typ) -> keyArray)
                    }
                    collectRenamedVariablesFromBlockVars(vars.tail)
                }
            }

            //This goes through the Procedure Block Body and adds their renamed versions to map
            def collectRenamedVariablesFromBlockBody(stmts: List[Statement]): Unit = {
                if(!stmts.isEmpty)
                {
                    stmts.head match
                    {
                        case IfElseStmt(_, ifblock, elseblock) => 
                            collectRenamedVariablesFromBlockVars(ifblock.asInstanceOf[BlockStmt].vars)
                            collectRenamedVariablesFromBlockBody(ifblock.asInstanceOf[BlockStmt].stmts)
                            collectRenamedVariablesFromBlockVars(elseblock.asInstanceOf[BlockStmt].vars)
                            collectRenamedVariablesFromBlockBody(elseblock.asInstanceOf[BlockStmt].stmts)
                        case WhileStmt(_, body, _) => 
                            collectRenamedVariablesFromBlockVars(body.asInstanceOf[BlockStmt].vars)
                            collectRenamedVariablesFromBlockBody(body.asInstanceOf[BlockStmt].stmts)
                        case BlockStmt(vars, blockstmts) =>
                            collectRenamedVariablesFromBlockVars(vars)
                            collectRenamedVariablesFromBlockBody(blockstmts)
                        case _ =>   
                    }
                    collectRenamedVariablesFromBlockBody(stmts.tail)
                }
            }

            collectRenamedVariablesFromBlockVars(block.vars)
            collectRenamedVariablesFromBlockBody(block.stmts)
        }

        /* It takes a BlockVarsDecl to create a new BlockVarsDecl with renamed versions of variables */
        def getLocalVarDeclarations(oldVars: List[BlockVarsDecl]): List[BlockVarsDecl] = {
            val blockdecls = ListBuffer[BlockVarsDecl]()
            var context = Scope.empty
            context += oldVars
            oldVars.foreach{ x => x match {
                case dec : BlockVarsDecl => val oldVariables = dec.ids 
                                            val varType = dec.typ
                                            val newIdentifiers = ListBuffer[Identifier]()
                                            oldVariables.foreach{
                                                variable => variable match {
                                                    case v : Identifier =>  
                                                        for( i <- 0 until k) {
                                                            val newIdentifier = getRenamedExpr(v, context, i)
                                                            newIdentifiers += newIdentifier.asInstanceOf[Identifier]
                                                        }   
                                                    }  
                                            }
                                            val newBlockDeclaration = BlockVarsDecl(newIdentifiers.toList, varType)
                                            blockdecls += newBlockDeclaration
                }
            }

            blockdecls.toList
        }

        def collectInsideBlockVars(block: BlockStmt): Unit = {
            
            var maxblock = 0
            def addDeclarationsToMap(blocknum: Int, blockVars:  List[BlockVarsDecl]) = {
                if(!blockVars.isEmpty) {
                    val context = Scope.empty + blockVars
                    val newdeclList = ListBuffer[BlockVarsDecl]()
                    blockVars.foreach{ x => x match {
                        case decl : BlockVarsDecl =>
                            val idBuffer = new ListBuffer[Identifier]()
                            for( variable <- decl.ids)
                                for( i <- 0 until k)
                                    idBuffer += getRenamedExpr(variable, context, i).asInstanceOf[Identifier]
                            val newdecl = BlockVarsDecl(idBuffer.toList, decl.typ)
                            ASTNode.introducePos(true, true, newdecl, decl.position)
                            newdeclList += newdecl
                        }
                    }
                    helperObj.mapOfRenamedVarDecls += (blocknum -> newdeclList)
                }
            }
            def collectInsideBlockVarsUtil(stmts: List[Statement]): Unit = {
                if(!stmts.isEmpty)
                {
                    stmts.head match
                    {
                        case IfElseStmt(_, ifblock, elseblock) => 
                            
                            maxblock += 1
                            addDeclarationsToMap(maxblock, ifblock.asInstanceOf[BlockStmt].vars)
                            collectInsideBlockVarsUtil(ifblock.asInstanceOf[BlockStmt].stmts)
                            
                            maxblock += 1
                            addDeclarationsToMap(maxblock, elseblock.asInstanceOf[BlockStmt].vars)
                            collectInsideBlockVarsUtil(elseblock.asInstanceOf[BlockStmt].stmts)
                        
                        case WhileStmt(_, body, _) => 

                            maxblock += 1
                            addDeclarationsToMap(maxblock, body.asInstanceOf[BlockStmt].vars)
                            collectInsideBlockVarsUtil(body.asInstanceOf[BlockStmt].stmts)

                        case BlockStmt(vars, blockstmts) =>
                            
                            maxblock += 1
                            addDeclarationsToMap(maxblock, vars)
                            collectInsideBlockVarsUtil(blockstmts)

                        case _ =>   
                    }
                    collectInsideBlockVarsUtil(stmts.tail)
                }
            }

            collectInsideBlockVarsUtil(block.stmts)

        }

        def modifyProcSignature(): ProcedureSig = 
        {
            @tailrec
            def modifyInputParams(inParams: List[(Identifier,Type)], inputParameters: ListBuffer[(Identifier,Type)]): Unit = {
                if(!inParams.isEmpty)
                {
                    val inpVariable = inParams.head
                    val renamedVarArray = helperObj.mapOfRenamedVariables(inpVariable)
                    renamedVarArray.foreach{
                        case renamedVar : Identifier => 
                            val tup = (renamedVar, inpVariable._2)
                            inputParameters  += tup
                    }  
                    modifyInputParams(inParams.tail, inputParameters)
                }
                
            }

            def modifyOutputParams(outParams: List[(Identifier,Type)], 
                outputParameters : ListBuffer[(Identifier,Type)]) = modifyInputParams(outParams, outputParameters)

            val inputParameters = ListBuffer[(Identifier,Type)]()
            val outputParameters = ListBuffer[(Identifier,Type)]()
            modifyInputParams(proc.sig.inParams, inputParameters)
            modifyOutputParams(proc.sig.outParams, outputParameters)           

            val activationVariableArray = helperObj.mapOfActivationVariables(0)
            val datatype: Type = BooleanType()
            activationVariableArray.foreach{
                actVar =>   val tup = (actVar, datatype)
                            inputParameters += tup
            }
                
            ProcedureSig(inputParameters.toList, outputParameters.toList)
        }

        def modifyProcConditions(): Unit = {

            val actVarArray = helperObj.mapOfActivationVariables(0)
            var actVarCond = Operator.and(actVarArray(0), actVarArray(1))
            for( i <- 2 until k)
                actVarCond = Operator.and(actVarCond, actVarArray(i))

            //transformation of requires expr r will be ------
                // (actVar== true && ...) -> r
            @tailrec
            def modifyRequires(requiresList: List[Expr], newRequiresList: ListBuffer[Expr]): Unit = {
                if(!requiresList.isEmpty) {
                    val exp = requiresList.head
                    exp match {
                        case OperatorApplication(op, operands) => 
                            val containsHyperProperty = checkHyperSelectOp(op,operands,1)
                            var context = Scope.empty
                            context += proc
                            if(containsHyperProperty > 1) {
                                    val renamedHyperExpression = getRenamedExpr(exp, context, k)
                                    val newRequiresExpr = Operator.imply(actVarCond, renamedHyperExpression)
                                    ASTNode.introducePos[Expr](true, true, newRequiresExpr, requiresList.head.position)
                                    newRequiresList += newRequiresExpr
                            }
                            else {
                                    val activationVariableArray = helperObj.mapOfActivationVariables(0)
                                    for(i <- 0 until k ) {
                                        val activationVariable = activationVariableArray(i)
                                        val renamedHyperExpression = getRenamedExpr(exp, context, i)
                                        val newExpression = Operator.imply(activationVariable, renamedHyperExpression)
                                        ASTNode.introducePos[Expr](true, true, newExpression, requiresList.head.position)
                                        newRequiresList += newExpression
                                    }
                            }
                        case _ => newRequiresList += exp
                    }
                    modifyRequires(requiresList.tail, newRequiresList)
                }
                
            }

            def modifyEnsures(ensuresList: List[Expr], newEnsuresList: ListBuffer[Expr]) = modifyRequires(ensuresList, newEnsuresList) 

            modifyRequires(proc.requires, newRequiresList)
            modifyEnsures(proc.ensures, newEnsuresList)
            if(proc.modifies.size != 0)
                throw new Utils.UnimplementedException("Procedures with trace select pre/post conditions are not allowed to use/modify module level variables")
            // modifyModifies(proc.modifies)

        }

        def getRenamedExpr(expr: Expr, context: Scope, copy: Int): Expr = {
            expr match 
            {
                case Identifier(_) => 
                    val typeOfIdentifier = context.get(expr.asInstanceOf[Identifier])
                    typeOfIdentifier match {
                        case Some(value) => 
                            val variableType = value.typ                   
                            val renamedVarArray = helperObj.mapOfRenamedVariables((expr.asInstanceOf[Identifier], variableType))
                            val newVariable = renamedVarArray(copy)
                            newVariable
                        case None => 
                            expr
                    }
                case ConstArray(_, _) =>
                    throw new Utils.UnimplementedException("Type ConstArray not supported.")

                case Tuple(values) => Tuple(values.map(getRenamedExpr(_, context, copy)))

                case OperatorApplication(op, operands) =>  op match {
                    case HyperSelect(kselect) => 
                        getRenamedExpr(operands(0), context, kselect-1)
                    case ArraySelect(indices) =>
                        val newOp = ArraySelect(indices.map(getRenamedExpr(_, context, copy)))
                        OperatorApplication(newOp, operands.map(getRenamedExpr(_, context, copy)))
                    case ArrayUpdate(indices, value) => 
                        val newindices = indices.map(getRenamedExpr(_, context, copy))
                        val newVal = getRenamedExpr(value, context, copy)
                        OperatorApplication(ArrayUpdate(newindices,newVal),operands.map(getRenamedExpr(_, context, copy)))
                    case _ => OperatorApplication(op, operands.map(getRenamedExpr(_, context, copy)))
                    }   

                case FuncApplication(e, args) => FuncApplication(e, args.map(getRenamedExpr(_, context, copy)))
                
                case Lambda(_, _) => 
                    throw new Utils.UnimplementedException("Lambdas not supported.")
                    
                case _ => 
                    //External Identifiers, Literals,
                    expr
            }  
        }



        def translateProcedure(): ListBuffer[Statement] = {
            var blocknum = 1

            def translateBody(currentScope: Int, stmts: List[Statement], newbody: ListBuffer[Statement], 
                                context: Scope):Unit = {
                if(!stmts.isEmpty) {
                    stmts.head match {
                        case AssumeStmt(expr, id) => 
                            val activationVariableArray = helperObj.mapOfActivationVariables(currentScope)
                            val emptyVarsList: List[BlockVarsDecl] = List()
                            expr match {
                            case OperatorApplication(op, operands) =>
                                val containsRelationalSpec = checkHyperSelectOp(op, operands, 1)
                                
                                if(containsRelationalSpec > 1) 
                                {
                                    val activationVariable1 = activationVariableArray(0)
                                    val activationVariable2 = activationVariableArray(1)
                                    val checkActVarCondition1 = activationVariable1.asInstanceOf[Expr]
                                    val checkActVarCondition2 = activationVariable2.asInstanceOf[Expr]
                                    var andCondition = Operator.and(checkActVarCondition1 ,checkActVarCondition2)
                                    for(i <- 2 until k) 
                                    {
                                        val currentActVarName = activationVariableArray(i)
                                        val checkActVarCondition = currentActVarName.asInstanceOf[Expr]
                                        andCondition = Operator.and(andCondition, checkActVarCondition)
                                    }
                                    val renamedExpression = getRenamedExpr(expr, context, k)
                                    val newAssumeStatement = AssumeStmt(renamedExpression, id)
                                    ASTNode.introducePos(true, true, newAssumeStatement, stmts.head.position)
                                    val trueBlockStmt = BlockStmt(emptyVarsList,List(newAssumeStatement.asInstanceOf[Statement]))
                                    val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                    val modularStmt = IfElseStmt(andCondition, trueBlockStmt, falseBlockStmt)
                                    newbody += modularStmt
                                }
                                else
                                {
                                    for(i <- 0 until k) 
                                    {
                                        val currentActVarName = activationVariableArray(i)
                                        val checkActVarCondition = currentActVarName.asInstanceOf[Expr]
                                        val renamedExpression = getRenamedExpr(expr, context, i)
                                        val newAssumeStatement = AssumeStmt(renamedExpression, id)
                                        ASTNode.introducePos(true, true, newAssumeStatement, stmts.head.position)
                                        val trueBlockStmt = BlockStmt(emptyVarsList,List(newAssumeStatement.asInstanceOf[Statement]))
                                        val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                        val modularStmt = IfElseStmt(checkActVarCondition, trueBlockStmt, falseBlockStmt)
                                        newbody += modularStmt  
                                    }
                                    
                                }
        
                                case _ => 
                                    for(i <- 0 until k) 
                                    {
                                        val currentActVarName = activationVariableArray(i)
                                        val checkActVarCondition = currentActVarName.asInstanceOf[Expr]
                                        val renamedExpression = getRenamedExpr(expr, context, i)
                                        val newAssumeStatement = AssumeStmt(renamedExpression, id)
                                        ASTNode.introducePos(true, true, newAssumeStatement, stmts.head.position)
                                        val trueBlockStmt = BlockStmt(emptyVarsList,List(newAssumeStatement.asInstanceOf[Statement]))
                                        val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                        val modularStmt = IfElseStmt(checkActVarCondition, trueBlockStmt, falseBlockStmt)
                                        newbody += modularStmt  
                                    }  
                            }

                        case AssertStmt(expr, id) => 
                            val activationVariableArray = helperObj.mapOfActivationVariables(currentScope)
                            val emptyVarsList: List[BlockVarsDecl] = List()
                            expr match {
                            case OperatorApplication(op, operands) =>
                                val containsRelationalSpec = checkHyperSelectOp(op, operands, 1)
                                val activationVariableArray = helperObj.mapOfActivationVariables(currentScope)
                                val emptyVarsList: List[BlockVarsDecl] = List()
                                if(containsRelationalSpec > 1) 
                                {
                                    val activationVariable1 = activationVariableArray(0)
                                    val activationVariable2 = activationVariableArray(1)
                                    val checkActVarCondition1 = activationVariable1.asInstanceOf[Expr]
                                    val checkActVarCondition2 = activationVariable2.asInstanceOf[Expr]
                                    var andCondition = Operator.and(checkActVarCondition1 ,checkActVarCondition2)
                                    for(i <- 2 until k) 
                                    {
                                        val currentActVarName = activationVariableArray(i)
                                        val checkActVarCondition = currentActVarName.asInstanceOf[Expr]
                                        andCondition = Operator.and(andCondition, checkActVarCondition)
                                    }
                                    val renamedExpression = getRenamedExpr(expr, context, k)
                                    val newAssertStatement = AssertStmt(renamedExpression, id)
                                    ASTNode.introducePos(true, true, newAssertStatement, stmts.head.position)
                                    val trueBlockStmt = BlockStmt(emptyVarsList,List(newAssertStatement.asInstanceOf[Statement]))
                                    val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                    val modularStmt = IfElseStmt(andCondition, trueBlockStmt, falseBlockStmt)
                                    newbody += modularStmt
                                }
                                else
                                {
                                    for(i <- 0 until k) 
                                    {
                                        val currentActVarName = activationVariableArray(i)
                                        val checkActVarCondition = currentActVarName.asInstanceOf[Expr]
                                        val renamedExpression = getRenamedExpr(expr, context, i)
                                        val newAssertStatement = AssertStmt(renamedExpression, id)
                                        ASTNode.introducePos(true, true, newAssertStatement, stmts.head.position)
                                        val trueBlockStmt = BlockStmt(emptyVarsList,List(newAssertStatement.asInstanceOf[Statement]))
                                        val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                        val modularStmt = IfElseStmt(checkActVarCondition, trueBlockStmt, falseBlockStmt)
                                        newbody += modularStmt  
                                    }
                                    
                                }
        
                                case _ => 
                                    for(i <- 0 until k) 
                                    {
                                        val currentActVarName = activationVariableArray(i)
                                        val checkActVarCondition = currentActVarName.asInstanceOf[Expr]
                                        val renamedExpression = getRenamedExpr(expr, context, i)
                                        val newAssertStatement = AssertStmt(renamedExpression, id)
                                        ASTNode.introducePos(true, true, newAssertStatement, stmts.head.position)
                                        val trueBlockStmt = BlockStmt(emptyVarsList,List(newAssertStatement.asInstanceOf[Statement]))
                                        val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                        val modularStmt = IfElseStmt(checkActVarCondition, trueBlockStmt, falseBlockStmt)
                                        newbody += modularStmt  
                                    }  
                            }
                            
                        case AssignStmt(lhss, rhss) => 
                            for(i <- 0 until k)
                            {   
                                val newlhss = ListBuffer[Lhs]()
                                for( lhsVar <- lhss)
                                {
                                    lhsVar match {
                                        case LhsId(id) => 
                                            val renamedLhs = getRenamedExpr(id, context, i) 
                                            val lhsId = LhsId(renamedLhs.asInstanceOf[Identifier])
                                            newlhss += lhsId

                                        case LhsNextId(id: Identifier) =>
                                            val renamedLhs = getRenamedExpr(id, context, i)
                                            val lhsId = LhsNextId(renamedLhs.asInstanceOf[Identifier])
                                            newlhss += lhsId

                                        case LhsArraySelect(id: Identifier, indices: List[Expr]) => 
                                            val renamedId = getRenamedExpr(id, context, i)  
                                            val lhsId = LhsArraySelect(renamedId.asInstanceOf[Identifier], 
                                                                    indices.map(getRenamedExpr(_, context, i)))
                                            newlhss += lhsId

                                        case LhsRecordSelect(id: Identifier, fields: List[Identifier]) =>
                                            val renamedLhs = getRenamedExpr(id, context, i) 
                                            val lhsId = LhsRecordSelect(renamedLhs.asInstanceOf[Identifier], fields)
                                            newlhss += lhsId

                                        case LhsSliceSelect(id: Identifier, bitslice : ConstBitVectorSlice) =>
                                            val renamedLhs = getRenamedExpr(id, context, i) 
                                            val lhsId = LhsSliceSelect(renamedLhs.asInstanceOf[Identifier], bitslice)
                                            newlhss += lhsId

                                        case LhsVarSliceSelect(id: Identifier, bitslice: VarBitVectorSlice) =>
                                            val renamedLhs = getRenamedExpr(id, context, i)  
                                            val lhsId = LhsVarSliceSelect(renamedLhs.asInstanceOf[Identifier], bitslice)
                                            newlhss += lhsId
                                    }
                                    
                                }

                                val newAssignStmt = AssignStmt(newlhss.toList, rhss.map(getRenamedExpr(_, context, i)))
                                ASTNode.introducePos(true, true, newAssignStmt, stmts.head.position)
                                val actVarArray = helperObj.mapOfActivationVariables(currentScope)
                                val actVarCond = actVarArray(i)
                                val emptyVarsList: List[BlockVarsDecl] = List()
                                val trueBlockStmt = BlockStmt(emptyVarsList,List(newAssignStmt.asInstanceOf[Statement] ))
                                val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                val modularStmt = IfElseStmt(actVarCond, trueBlockStmt, falseBlockStmt)
                                ASTNode.introducePos(true, true, modularStmt, stmts.head.position)
                                newbody += modularStmt
                            }

                        case HavocStmt(havocable) => havocable match {
                            case HavocableId(id) => 
                                for( i <- 0 until k) {
                                    
                                    val newhavocable = HavocableId(getRenamedExpr(id.asInstanceOf[Expr], context, i).asInstanceOf[Identifier])
                                    val havocstmt = HavocStmt(newhavocable)
                                    ASTNode.introducePos(true, true, havocstmt, stmts.head.position)
                                    val actVarArray = helperObj.mapOfActivationVariables(currentScope)
                                    val actVarCond = actVarArray(i)
                                    val emptyVarsList: List[BlockVarsDecl] = List()
                                    val trueBlockStmt = BlockStmt(emptyVarsList,List(havocstmt.asInstanceOf[Statement] ))
                                    val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                    val modularStmt = IfElseStmt(actVarCond, trueBlockStmt, falseBlockStmt)
                                    ASTNode.introducePos(true, true, modularStmt, stmts.head.position)
                                    newbody += modularStmt
                                }
                            case HavocableNextId(id) => 
                                for( i <- 0 until k) {
                                    val newhavocable = HavocableNextId(getRenamedExpr(id.asInstanceOf[Expr], context, i).asInstanceOf[Identifier])
                                    val havocstmt = HavocStmt(newhavocable)
                                    ASTNode.introducePos(true, true, havocstmt, stmts.head.position)
                                    val actVarArray = helperObj.mapOfActivationVariables(currentScope)
                                    val actVarCond = actVarArray(i)
                                    val emptyVarsList: List[BlockVarsDecl] = List()
                                    val trueBlockStmt = BlockStmt(emptyVarsList,List(havocstmt.asInstanceOf[Statement] ))
                                    val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                    val modularStmt = IfElseStmt(actVarCond, trueBlockStmt, falseBlockStmt)
                                    ASTNode.introducePos(true, true, modularStmt, stmts.head.position)
                                    newbody += modularStmt
                                }
                            case _ =>
                                newbody += stmts.head
                        }
                            
                        
                        case BlockStmt(blockvars, blockstmts) =>
                            val ctx = context + blockvars
                            var newblockvars: List[BlockVarsDecl] = List()
                            helperObj.mapOfRenamedVarDecls get blocknum match {
                                case Some(listOfDecls) =>
                                    newblockvars = listOfDecls.toList
                                case None =>
                            }
                            val newblockstmts = ListBuffer[Statement]()
                            blocknum+=1
                            translateBody(currentScope, blockstmts, newblockstmts, ctx)
                            val newBlock = BlockStmt(newblockvars, newblockstmts.toList)
                            ASTNode.introducePos(true, true, newBlock, stmts.head.position)
                            newbody += newBlock


                        case IfElseStmt(condition, ifblock, elseblock) => 
                            val originalActivationVariableArray = helperObj.mapOfActivationVariables(currentScope)
                            val newActivationVarArray1 = helperObj.mapOfActivationVariables(helperObj.maxScope+1)
                            val newActivationVarArray2 = helperObj.mapOfActivationVariables(helperObj.maxScope+2)
                            for(i <- 0 until k)
                            {
                                val currentActVarName = originalActivationVariableArray(i)
                                val newActVarName1 = newActivationVarArray1(i)
                                val newActVarName2 = newActivationVarArray2(i)
                                val checkActVarCondition = currentActVarName.asInstanceOf[Expr] 
                                val newCondition = getRenamedExpr(condition, context, i)
                                val andStmt1 = Operator.and(checkActVarCondition ,newCondition)
                                val andStmt2 = Operator.and(checkActVarCondition ,Operator.not(newCondition))
                                val newActVarAssignment1 = AssignStmt(List(LhsId(newActVarName1)), List(andStmt1))
                                val newActVarAssignment2 = AssignStmt(List(LhsId(newActVarName2)), List(andStmt2))
                                if (!ifblock.asInstanceOf[BlockStmt].stmts.isEmpty) {
                                    ASTNode.introducePos(true, true, newActVarAssignment1, ifblock.asInstanceOf[BlockStmt].stmts.head.position)
                                    ASTNode.introducePos(true, true, newActVarAssignment2, ifblock.asInstanceOf[BlockStmt].stmts.head.position)
                                }
                                if (!elseblock.asInstanceOf[BlockStmt].stmts.isEmpty) 
                                    ASTNode.introducePos(true, true, newActVarAssignment2, elseblock.asInstanceOf[BlockStmt].stmts.head.position)
                                newbody ++= List(newActVarAssignment1, newActVarAssignment2)
                            }
                            val trueScope = helperObj.maxScope+1
                            val falseScope = helperObj.maxScope+2
                            helperObj.maxScope+=2
                            translateBody(trueScope, List(ifblock), newbody, context)
                            translateBody(falseScope, List(elseblock), newbody, context)
                        
                        case WhileStmt(condition, body, invariants) => 
                            val originalActivationVariableArray = helperObj.mapOfActivationVariables(currentScope)
                            val newActivationVarArray = helperObj.mapOfActivationVariables(helperObj.maxScope+1)
        
                            //create new condition
                            val activationVariableCopy0 = originalActivationVariableArray(0)
                            val renamedconditionCopy0 = getRenamedExpr(condition, context, 0)
                            val andExpr1 = Operator.and(activationVariableCopy0.asInstanceOf[Expr], renamedconditionCopy0)
        
                            val activationVariableCopy1 = originalActivationVariableArray(1)
                            val renamedconditionCopy1 = getRenamedExpr(condition, context, 1)
                            val andExpr2 = Operator.and(activationVariableCopy1.asInstanceOf[Expr], renamedconditionCopy1)
        
                            var orCondition = Operator.or(andExpr1, andExpr2) //new while condition
                            
                            for( i <- 2 until k) {
                                val originalActivationVariable = originalActivationVariableArray(i)
                                val newActivationVariable = newActivationVarArray(i)
                                val andExpr = Operator.and(originalActivationVariable.asInstanceOf[Expr], newActivationVariable)
                                orCondition = Operator.or(orCondition, andExpr)
                            }
        
                            val whilebody = ListBuffer[Statement]()
                            for(i <- 0 until k)
                            {
                                val currentActVarName = originalActivationVariableArray(i)
                                val newActVarName = newActivationVarArray(i)
                                val checkActVarCondition = currentActVarName.asInstanceOf[Expr]  
                                val newCondition = getRenamedExpr(condition, context, i)
                                val andExpr = Operator.and(checkActVarCondition, newCondition)
                                val newActVarAssignment = AssignStmt(List(LhsId(newActVarName)), List(andExpr))
                                ASTNode.introducePos(true, true, newActVarAssignment, condition.position)
                                whilebody += newActVarAssignment
                            }
        
                            var actVarCond = Operator.and(activationVariableCopy0.asInstanceOf[Expr], activationVariableCopy1.asInstanceOf[Expr])
                            for( i <- 2 until k)
                                actVarCond = Operator.and(actVarCond, originalActivationVariableArray(i))
        
        
                            val newinvariants = ListBuffer[Expr]()
                            invariants.foreach{
                                inv => inv match {
                                            case OperatorApplication(op, operands) => 
                                                val containsHyperProperty = checkHyperSelectOp(op,operands,1)
                                                if(containsHyperProperty > 1) {
                                                    
                                                    val renamedHyperInvariant = getRenamedExpr(inv,context,k)
                                                    val newinvariant = Operator.imply(actVarCond, renamedHyperInvariant) 
                                                    ASTNode.introducePos[Expr](true, true, newinvariant, inv.position)
                                                    newinvariants += newinvariant
                                                }
                                                else {
                                                    for(i <- 0 until k ) {
                                                        val currentActVarName = originalActivationVariableArray(i)
                                                        val checkActVarCondition = currentActVarName.asInstanceOf[Expr]  
                                                        val renamedexpr = getRenamedExpr(inv, context, i)
                                                        val newinvariant = Operator.imply(checkActVarCondition, renamedexpr)
                                                        ASTNode.introducePos[Expr](true, true, newinvariant, inv.position)
                                                        newinvariants += newinvariant
                                                    }
                                                }
                                            case _ => newinvariants += inv
        
                                        }
                            }
                            
                            helperObj.maxScope+=1
                            translateBody(helperObj.maxScope, List(body), whilebody, context)
                            val emptyVarsList: List[BlockVarsDecl] = List()
                            val whilebodyblock = BlockStmt(emptyVarsList, whilebody.toList)
                            if(!body.asInstanceOf[BlockStmt].stmts.isEmpty)
                                ASTNode.introducePos(true, true, whilebodyblock, body.asInstanceOf[BlockStmt].stmts.head.position)
                            val newWhileStatement = WhileStmt(orCondition, whilebodyblock, newinvariants.toList)
                            ASTNode.introducePos(true, true, newWhileStatement, stmts.head.position)
                            newbody += newWhileStatement
        
                        case ProcedureCallStmt(id, callLhss, args, instId, _) => 
                            val calledProcedure = id
                            val isCalledProcTranslated = procWithRelSpecUtil(calledProcedure)._1
                            var translationPresent = false
                            if(isCalledProcTranslated)
                            {
                                val calledProcCopyArray = procWithRelSpecUtil(calledProcedure)._2  
                                translationPresent = calledProcCopyArray contains k     
                            }

                            val numberOfParameters = args.size
                            val numberOfReturnParameters = callLhss.size
                            val m = numberOfParameters
                            val n = numberOfReturnParameters

                            if(translationPresent)
                            {
                                val originalActivationVariableArray = helperObj.mapOfActivationVariables(currentScope)
                                val currentActVarName1 = originalActivationVariableArray(0)
                                val currentActVarName2 = originalActivationVariableArray(1)
                                val checkActVarCondition1 = currentActVarName1.asInstanceOf[Expr] 
                                val checkActVarCondition2 = currentActVarName2.asInstanceOf[Expr] 
                                var orCondition = Operator.or(checkActVarCondition1, checkActVarCondition2)
                                for(i <- 2 until k)
                                {
                                    val currentActVarName = originalActivationVariableArray(i)
                                    val checkActVarCondition = currentActVarName.asInstanceOf[Expr] 
                                    orCondition = Operator.or(orCondition, checkActVarCondition) //line 1 
                                }
            
                                //--------Creating Outer If Condition's true Block--------//
            
                                //Creating first if condition 
                                val newIfStatements1 = ListBuffer[Statement]()
                                var newArguments = ListBuffer[Identifier]()
                                for(i <- 0 until k)
                                {   
                                    val currentActVarName = originalActivationVariableArray(i)
                                    newArguments += currentActVarName
                                    val checkActVarCondition = currentActVarName.asInstanceOf[Expr] 
                                    val trueStmtBlock1 = ListBuffer[Statement]()
                                    for(j <- 0 until m)
                                    {
                                        var newlhss: List[Lhs] = List()
                                        var newrhss: List[Expr] = List()
                                        val newActivationVarArray = helperObj.mapOfNewVariables(helperObj.maxVarScope+j) //CHECK
                                        val newActivationVar = newActivationVarArray(i) //as Set - Not activation Variables
                                        val lhsId = LhsId(newActivationVar.asInstanceOf[Identifier])
                                        val rhsId = getRenamedExpr(args(j), context, i)
                                        newlhss = List(lhsId)
                                        newrhss = List(rhsId)
                                        val assignStmt = AssignStmt(newlhss, newrhss)
                                        trueStmtBlock1 += assignStmt.asInstanceOf[Statement]
                                    }
                                    //creatingIfStmt1
                                    val emptyVarsList: List[BlockVarsDecl] = List()
                                    val trueBlockStmt1 = BlockStmt(emptyVarsList,trueStmtBlock1.toList)
                                    val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                    val statement1 = IfElseStmt(checkActVarCondition, trueBlockStmt1, falseBlockStmt)
                                    newIfStatements1 += statement1
                                }
                                val moreArguments = ListBuffer[Identifier]()
                                for(j <- 0 until m)
                                {
                                    for(i<- 0 until k)
                                    {
                                        val newActivationVarArray = helperObj.mapOfNewVariables(helperObj.maxVarScope+j) //WRONG
                                        val newActivationVar = newActivationVarArray(i)
                                        moreArguments += newActivationVar
                                    }
                                }
                                moreArguments ++= newArguments
                                newArguments = moreArguments
                                val newIfStatements2 = ListBuffer[Statement]()
                                val newReturnParameters =  ListBuffer[Lhs]() //to be used for call stmt
                                for(i <- 0 until k)
                                {   
                                    val currentActVarName = originalActivationVariableArray(i)
                                    val checkActVarCondition = currentActVarName.asInstanceOf[Expr] 
                                    val trueStmtBlock2 = ListBuffer[Statement]()
                                    for(j <- 0 until n)
                                    {
                                        var newlhss: List[Lhs] = List()
                                        var newrhss: List[Expr] = List()
                                        val newActivationVarArray = helperObj.mapOfNewVariables(helperObj.maxVarScope+m+j)
                                        val newActivationVar = newActivationVarArray(i)
                                        val newReturnVar = getRenamedExpr(callLhss(j).ident, context, i)
                                        val lhsId = LhsId(newReturnVar.asInstanceOf[Identifier])
                                        val callStmtLhs = LhsId(newActivationVar.asInstanceOf[Identifier])
                                        val rhsId = newActivationVar.asInstanceOf[Expr]
                                        newlhss = List(lhsId)
                                        newrhss = List(rhsId)
                                        newReturnParameters += callStmtLhs
                                        val assignStmt = AssignStmt(newlhss, newrhss)
                                        trueStmtBlock2 += assignStmt.asInstanceOf[Statement]
                                    }
        
        
                                    //creatingIfStmt2
                                    val emptyVarsList: List[BlockVarsDecl] = List()
                                    val trueBlockStmt2 = BlockStmt(emptyVarsList,trueStmtBlock2.toList)
                                    val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                    val statement2 = IfElseStmt(checkActVarCondition, trueBlockStmt2, falseBlockStmt)
                                    newIfStatements2 += statement2
            
                                }
                                //creating new call statement
                                val newProcId = Identifier(id.name + "$" + (k).toString)
                                val procCallStmt = ProcedureCallStmt(newProcId, newReturnParameters.toList, newArguments.toList, instId)
                                val modularStatements = newIfStatements1 
                                modularStatements += procCallStmt
                                modularStatements ++= newIfStatements2
                                val emptyVarsList: List[BlockVarsDecl] = List()
                                val trueBlockStmt = BlockStmt(emptyVarsList,modularStatements.toList)
                                val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                val modularStmt = IfElseStmt(orCondition, trueBlockStmt, falseBlockStmt)
                                newbody += modularStmt
                                helperObj.maxVarScope += (numberOfParameters + numberOfReturnParameters)
                            }

                            else 
                            {
                                val originalActivationVariableArray = helperObj.mapOfActivationVariables(currentScope)
                                for ( i <- 0 until k )
                                {
                                    val emptyVarsList: List[BlockVarsDecl] = List()
                                    val activationVariable = originalActivationVariableArray(i)
                                    val actVarCheckCondition = activationVariable.asInstanceOf[Expr]
                                    val newlhss = callLhss.map(
                                        variable => LhsId(getRenamedExpr(variable.ident.asInstanceOf[Expr], context, i).asInstanceOf[Identifier]))
                                    val newargs = args.map(getRenamedExpr(_, context, i))
                                    val procCallStmt = ProcedureCallStmt(id, newlhss, newargs.toList, instId)
                                    val trueBlockStmt = BlockStmt(emptyVarsList,List(procCallStmt))
                                    val falseBlockStmt = BlockStmt(emptyVarsList, List(SkipStmt()))
                                    val newStmt = IfElseStmt(actVarCheckCondition, trueBlockStmt, falseBlockStmt)
                                    newbody += newStmt
                                }
                                helperObj.maxVarScope += (numberOfParameters + numberOfReturnParameters)
                                
                            }
                        
                        case ModuleCallStmt(_) =>
                            throw new Utils.UnimplementedException("Module Calls are unsupported")

                        case _ => newbody += stmts.head

                    }
                    translateBody(currentScope, stmts.tail, newbody, context)
                }
            }

            var context = Scope.empty
            context += proc
            context += proc.body.asInstanceOf[BlockStmt].vars
            helperObj.maxScope = 0
            helperObj.maxVarScope = 1
            val newbody = ListBuffer[Statement]()
            translateBody(0, proc.body.asInstanceOf[BlockStmt].stmts, newbody, context)
            newbody
        }

        val currentScope = 0
        val context = Scope.empty + proc + proc.body.asInstanceOf[BlockStmt].vars
        var outerActivationDecls = createActivationVariables(k,helperObj.mapOfActivationVariables,currentScope)
        findRequiredActivationVariables(proc.body.asInstanceOf[BlockStmt].stmts, currentScope, context)
        helperObj.addToRenameVariableMap(k, proc.sig.inParams)
        helperObj.addToRenameVariableMap(k, proc.sig.outParams)
        collectRenamedVariables(proc.body.asInstanceOf[BlockStmt])
        collectInsideBlockVars(proc.body.asInstanceOf[BlockStmt])
        val procSignature = modifyProcSignature()
        modifyProcConditions()
        val newdecls = getLocalVarDeclarations(proc.body.asInstanceOf[BlockStmt].vars)
        val procIdentifier = Identifier(proc.id.name + "$" + k.toString())
        val newbody = translateProcedure()
        val procBody = BlockStmt(newVarDeclarations.toList ::: newdecls, newbody.toList)
        ProcedureDecl(procIdentifier, procSignature, procBody, newRequiresList.distinct.toList, newEnsuresList.distinct.toList, newModifiesList, proc.annotations)

    }

    /* 
        It helps in checking the translations required for a procedure.
    */
    def checkForRelationalSpecification(proc: ProcedureDecl): List[Int] = {

        var copySet: Set[Int] = Set()

        def getAllTraceValuesUsed(maxTraceValue: Int, traceValueTracker: Array[Boolean], op: Operator, operands: List[Expr]): Array[Boolean] = op match {
            case HyperSelect(i) => 
                traceValueTracker(i-1) = true
                traceValueTracker
            case _ =>
                var updatedTraceValueTracker = traceValueTracker
                operands.foreach{
                    x => x match {
                        case OperatorApplication(op_, operands_) => 
                            updatedTraceValueTracker = getAllTraceValuesUsed(maxTraceValue, updatedTraceValueTracker, op_, operands_)
                        case _ =>
                    }
                }
                updatedTraceValueTracker            
        }

        @tailrec
        def checkRequires(requireExpr: List[Expr]): Unit = {
            if(!requireExpr.isEmpty) {
                requireExpr.head match {
                    case OperatorApplication(op, operands) => 
                        val maxTraceValue = checkHyperSelectOp(op, operands, 1)
                        if (maxTraceValue > 1) 
                        {
                            val traceValuesUsed = getAllTraceValuesUsed(maxTraceValue, new Array[Boolean](maxTraceValue), op, operands)
                            if (!traceValuesUsed.foldLeft(true)( _ && _))
                                throw new Utils.ParserError("Non sequential trace values are not allowed", Some(requireExpr.head.pos), requireExpr.head.filename)
                            copySet +=  maxTraceValue
                        }
                    case _ => 
                }
                checkRequires(requireExpr.tail)
            }
        }

        def checkEnsures(ensureExpr: List[Expr]): Unit = {
            checkRequires(ensureExpr)
        }

        var copies = List[Int]() 
        checkRequires(proc.requires)
        checkEnsures(proc.ensures)
        copySet.foreach((item: Int) => copies = copies ::: List(item))
        copies
    }

    /*
        It removes all the required hyperselect expressions and statements from the procedure signature and body
    */

    def removeHyperSelectOp(oldProc: ProcedureDecl, traceValToRetain: Int) : ProcedureDecl  = {

        val newRequiresList = new ListBuffer[Expr]()
        val newEnsuresList = new ListBuffer[Expr]()

        def isHyperSelectPresent(op: Operator, operands: List[Expr]): Boolean = op match {
            case HyperSelect(_) => true
            case _ => operands.map {
                case OperatorApplication(op_, operands_) => isHyperSelectPresent(op_, operands_)
                case _ => false
            }.foldLeft(false)(_ || _)
        }

        @tailrec
        def removeFromRequires(requiresList: List[Expr], filter: Boolean, newRequiresList: ListBuffer[Expr]): Unit = {
            if(!requiresList.isEmpty) {
                requiresList.head match {
                    case OperatorApplication(op, operands) => 
                        val hasHyperSelect = isHyperSelectPresent(op, operands)
                        val traceValue = checkHyperSelectOp(op, operands, 1)
                        if(hasHyperSelect && traceValue == 1)
                            throw new Utils.ParserError("Pre/Post Conditions using trace select should use atleast two traces", Some(requiresList.head.pos), requiresList.head.filename)
                        if(filter) {
                            if(traceValue == 1 || traceValue == traceValToRetain)
                                newRequiresList += requiresList.head
                        }
                        else if(traceValue == 1) {
                            newRequiresList += requiresList.head
                        }
                        else 
                            newRequiresList += requiresList.head
                        
                    case _ => newRequiresList += requiresList.head
                }
                removeFromRequires(requiresList.tail, filter, newRequiresList)
            }
        }

        def removeFromEnsures(ensuresList: List[Expr], filter: Boolean, newEnsuresList: ListBuffer[Expr]): Unit = {
            removeFromRequires(ensuresList, filter, newEnsuresList)
        }

        def removeHyperSelectsFromBody(oldstmts: List[Statement], newstmts: ListBuffer[Statement] ): Unit = {
            if(!oldstmts.isEmpty)
            {
                oldstmts.head match
                {
                    case AssumeStmt(expr, _) =>
                        expr match {
                            case OperatorApplication(op, operands) =>
                                val hasHyperSelect = isHyperSelectPresent(op, operands)
                                if (hasHyperSelect) {
                                    val traceValue = checkHyperSelectOp(op, operands, 1)
                                    if(traceValue == traceValToRetain) {
                                        newstmts += oldstmts.head
                                    }
                                }
                                else newstmts += oldstmts.head
                                
                            case _ =>
                                newstmts += oldstmts.head
                        }

                    case AssertStmt(expr, _) =>
                        expr match {
                            case OperatorApplication(op, operands) =>
                                val hasHyperSelect = isHyperSelectPresent(op, operands)
                                if (hasHyperSelect) {
                                    val traceValue = checkHyperSelectOp(op, operands, 1)
                                    if(traceValue == traceValToRetain) {
                                        newstmts += oldstmts.head
                                    }
                                }
                                else newstmts += oldstmts.head
                            case _ =>
                                newstmts += oldstmts.head
                        }

                    case IfElseStmt(cond, ifblock, elseblock) =>
                        val newifblock = ListBuffer[Statement]()
                        val newelseblock = ListBuffer[Statement]()
                        removeHyperSelectsFromBody(ifblock.asInstanceOf[BlockStmt].stmts, newifblock)
                        removeHyperSelectsFromBody(elseblock.asInstanceOf[BlockStmt].stmts, newelseblock)
                        val trueblock = BlockStmt(ifblock.asInstanceOf[BlockStmt].vars, newifblock.toList)
                        val falseblock = BlockStmt(elseblock.asInstanceOf[BlockStmt].vars, newelseblock.toList)
                        val newIfStatement = IfElseStmt(cond, trueblock, falseblock)
                        newstmts += newIfStatement

                    case WhileStmt(cond, body, invariants) =>
                        val newinvariants = ListBuffer[Expr]()
                        for(inv <- invariants) {
                            inv match {
                                case OperatorApplication(op, operands) => 
                                    val hasHyperSelect = isHyperSelectPresent(op, operands)
                                    if (hasHyperSelect) {
                                        val traceValue = checkHyperSelectOp(op, operands, 1)
                                        if(traceValue == traceValToRetain) {
                                            newinvariants += inv
                                        }
                                    }
                                    else newinvariants += inv

                                case _ =>
                                    newinvariants += inv
                                
                            }
                        }
                        val newwhilebody = ListBuffer[Statement]()
                        removeHyperSelectsFromBody(body.asInstanceOf[BlockStmt].stmts, newwhilebody)
                        val newwhilebodyblock = BlockStmt(body.asInstanceOf[BlockStmt].vars, newwhilebody.toList)
                        val newwhilestmt = WhileStmt(cond, newwhilebodyblock, newinvariants.toList)
                        newstmts += newwhilestmt.asInstanceOf[Statement]

                    case _ =>   
                        newstmts += oldstmts.head
                       
                }
                removeHyperSelectsFromBody(oldstmts.tail, newstmts) 
            }
        }

        removeFromRequires(oldProc.requires, true, newRequiresList)
        removeFromEnsures(oldProc.ensures, true, newEnsuresList)
        val newbody = ListBuffer[Statement]()
        removeHyperSelectsFromBody(oldProc.body.asInstanceOf[BlockStmt].stmts, newbody)
        val newbodyblock = BlockStmt(oldProc.body.asInstanceOf[BlockStmt].vars, newbody.toList)
        new ProcedureDecl(oldProc.id, oldProc.sig, newbodyblock , newRequiresList.distinct.toList, newEnsuresList.distinct.toList, oldProc.modifies, oldProc.annotations )

    }

    /* 
        It goes through all the procedures in the module and checks which ones require translations
        to verify hyperproperties and for how many copies. Accordingly, it populates necessary data structurea

    */
    @tailrec
    private def findTranslatableProcedures(moduleInDecls: List[Decl]): Unit = {
        if(!moduleInDecls.isEmpty) {
            moduleInDecls.head match {
                case _ : ProcedureDecl =>
                    val proc = moduleInDecls.head.asInstanceOf[ProcedureDecl]
                    val traceValueList = checkForRelationalSpecification(proc)
                    val isProcRelevant = if (traceValueList.size > 0) true else false
                    if(isProcRelevant) {  //if procedure tries to check a hyper property
                        val copyArray = traceValueList.toArray
                        val tuple = (true, copyArray)  // true indicates that proc requires translation
                        procWithRelSpec += ( proc -> tuple)
                        procWithRelSpecUtil += ( proc.id -> tuple)
                    }
                    else {  

                        procWithRelSpec += ( proc -> (false, Array.empty[Int]))
                        procWithRelSpecUtil += ( proc.id -> (false, Array.empty[Int]))
                    }
                case _ => 
            }
            findTranslatableProcedures(moduleInDecls.tail)
        }
    }

    /* 
        It goes through each procedure, does the required translation, adds it to the new module.

    */
    @tailrec
    private def translateProcedures(moduleInDecls: List[Decl], ctxx: Scope): Unit = {
        if(!moduleInDecls.isEmpty) {
            moduleInDecls.head match {
                case proc : ProcedureDecl =>
                    val isProcRelevant = procWithRelSpec(proc)._1
                    if(isProcRelevant) {
                        val oldProcedure = removeHyperSelectOp(proc, 0)
                        newModuleDecls += oldProcedure
                        val traceValuesArray = procWithRelSpec(proc)._2
                        val procArray = new Array[ProcedureDecl](traceValuesArray.size + 1)
                        procArray(0) = oldProcedure
                        var index = 1
                        traceValuesArray.foreach { 
                            k => 
                                val helperObj = new ModularProductHelper()
                                val specificProcedure = removeHyperSelectOp(proc, k) //filter out trace selects that aren't required
                                val modularProcedure = modularProduct(k, specificProcedure, helperObj, ctxx)
                                newModuleDecls += modularProcedure
                                procArray(index) = modularProcedure
                                index += 1
                        }
                        procedureMap +=(proc -> procArray )
                    }
                    else {
                        newModuleDecls += proc
                        val procArray = new Array[ProcedureDecl](1)
                        procArray(0) = proc
                        procedureMap +=(proc -> procArray )
                    }

                case _ => 
                    newModuleDecls += moduleInDecls.head
            }
            translateProcedures(moduleInDecls.tail, ctxx)
        } 
    }


    def modifyControlBlock(oldCmds: List[GenericProofCommand], procedures: List[ProcedureDecl]): List[GenericProofCommand] = {

        val newCommands = ListBuffer[GenericProofCommand]()
        var mapOfResultVars = Map[Identifier, (Boolean, ProcedureDecl)]()  //variables holding proof results

        def modifyControlBlockUtil(oldCmds: List[GenericProofCommand]): Unit = {
            if(!oldCmds.isEmpty) {
                val command = oldCmds.head
                if(command.isVerify) {
                    val args = command.args
                    val exp = args(0)._1

                    for ( p <- procedures if p.id == exp.asInstanceOf[Identifier]) {
                        val isProcRelevant = procWithRelSpec(p)._1
                        if(isProcRelevant) {
                            val copyArray = procWithRelSpec(p)._2
                            val procArray = procedureMap(p)
                            var index = 0
                            for(k <- copyArray)
                            {
                                val modularProcedure = procArray(index+1)
                                var newResultVar = command.resultVar
                                command.resultVar match {
                                    case Some(value) => 
                                        newResultVar = Some(Identifier(value.name + "$" + k.toString()))
                                        mapOfResultVars += (value -> (true, p))
                                        index+=1
                                        
                                    case None => newResultVar = command.resultVar
                                } 
                                val newArgs = ListBuffer[(Expr, String)]()
                                val tup = (modularProcedure.id.asInstanceOf[Expr], modularProcedure.id.name)
                                newArgs += tup
                                val newCommand = GenericProofCommand(command.name, command.params, newArgs.toList, newResultVar, command.argObj)
                                ASTNode.introducePos(true, true, newCommand, command.position)
                                newCommands  += newCommand

                            }
                        }
                    }

                    newCommands += command
                }
                else if(command.name.toString() == "print_cex") {
                    command.argObj match {
                        case Some(varName) => 
                            val mapValue = mapOfResultVars.get(varName)
                            mapValue match {
                                case Some((isRelevant, proc)) => 
                                    if(isRelevant) {
                                        val copyArray = procWithRelSpec(proc)._2
                                        for(k <- copyArray) {
                                            val newArgs = ListBuffer[(Expr, String)]()
                                            val newArgObj = Some(Identifier(varName.toString + "$" + k.toString))
                                            for(arg <- command.args) {
                                                val ident = arg._1
                                                for(i <- 0 until k) {
                                                    val variable = Identifier(ident.toString + "." + (i+1).toString)
                                                    val newtuple = (variable, ident.toString + "." + (i+1).toString)
                                                    newArgs += newtuple
                                                }
                                            }
                                            val newCommand = GenericProofCommand(command.name, command.params, newArgs.toList, command.resultVar, newArgObj)
                                            ASTNode.introducePos(true, true, newCommand, command.position)
                                            newCommands += newCommand
                                        }
                                    }
                                    newCommands += command 
                                case None => 
                                    newCommands += command 
                                }
                            case None => 
                                newCommands += command 
                            } 
                }
                else 
                    newCommands += command 
                               
                modifyControlBlockUtil(oldCmds.tail)
            }
        }

        modifyControlBlockUtil(oldCmds)
        newCommands.toList
    }

    def cleanup: Unit = {
        newModuleDecls.clear()
        newDecls.clear()
    }



    override def rewriteModule(moduleIn : Module, ctx : Scope) : Option[Module] = {

        findTranslatableProcedures(moduleIn.decls)
        translateProcedures(moduleIn.decls, ctx + moduleIn)
        val controlCommands = modifyControlBlock(moduleIn.cmds, moduleIn.procedures)
        val finalModule = Module(moduleIn.id, newModuleDecls.toList, controlCommands, moduleIn.notes)
        cleanup
        // log.debug(finalModule.toString())
        Some(finalModule)
    }

}


class ModularProductProgram extends ASTRewriter(
    "ModularProductProgram", new ModularProductProgramPass())
