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
case class ConcreteInt (value: List[Int]) extends ConcreteValue 
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
        List[assn]
        List[Commands]
    Output:
        List[assn]

    */ 
    def execute (module: Module, config: UclidMain.Config) : List[CheckResult] = {
        // End goal
        UclidMain.printVerbose("HELLO IN EXECUTE")
        
        // create a new variable for ConcreteBool with a value and then try to print that

        // var - mutable, open to reassignment
        // val - immutable, cannot reassign
        // val test_bool = ConcreteBool(false)

        // val test_int = ConcreteInt(3)
        
        println("helloo")

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

        println("postinit")
        pretty_print(postinit)

        val next_stmt = module.next match {
            case Some(next) => simulate_stmt(postinit, next.body)
        }

        println("after statement")
        pretty_print(next_stmt)
        // check that none of the values are ConcreteUndef

        println("Simulate next block")
        println(module.next.get.getClass)
        
        // val assn : scala.collection.mutable.Map[Identifier, ConcreteValue] = Map.empty
        // println("preinit")
        // pretty_print(preinit)
        // println("postinit")
        // pretty_print(postinit)
        // initialize(assn)
        
        // need to access the variables in the 
        // 

        // Define initial assignment
        // val init_assignment = initialize()

        // // Simulate
        // simulate_helper(init_assignment, stmt)
        return List()
    }

    def initialize (assn: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        stmt: Statement) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        simulate_stmt(assn, stmt)
    }

    def simulate_stmt (assn: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        stmt: Statement) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {
        
        stmt match {
            case AssignStmt(lhss, rhss) => {
                val rhseval = rhss.map(rhs => evaluate_expr(assn, rhs))
                if (rhseval.size == 1) {
                    lhss.foldLeft(assn)((a, l) => update_lhs(a, l, rhseval(0)))
                } else {
                    throw new NotImplementedError(s"RHS must be singleton")
                }
            }

            // TODO: NOT YET FULLY IMPLEMENTED (LEIQI)
            case BlockStmt(vars, stmts) => {
                stmts.foldLeft(assn)((a, stmt) => simulate_stmt(a, stmt))
            }
            
            case SkipStmt() => {
                throw new NotImplementedError(s"SkipStmt not implemented")
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
            case IfElseStmt(cond, ifblock) => {
                throw new NotImplementedError(s"IfElseStmt not implemented")
            }
            case ForStmt(id, typ, range, body) => {
                throw new NotImplementedError(s"ForStmt not implemented")
            }
            case WhileStmt(cond, body, invariants) => {
                throw new NotImplementedError(s"WhileStmt not implemented")
            }
            case CaseStmt(body) => {
                throw new NotImplementedError(s"CaseStmt not implemented")
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

    def update_lhs (assn: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        lhs: Lhs, v: ConcreteValue) : scala.collection.mutable.Map[Identifier, ConcreteValue] = {  
        // TODO: More updates to LHS (Adwait)
        lhs match {
            case LhsId(id) => {
                assn(id) = v
                assn
            }
            case _ => throw new NotImplementedError(s"LHS Update for ${lhs}")
        }
    }


    def evaluate_expr (assn: scala.collection.mutable.Map[Identifier, ConcreteValue], 
        expr: lang.Expr) : ConcreteValue = {
        
        expr match {
            case a : Identifier => assn(a)
            case BoolLit(b) => ConcreteBool(b)
            // TODO
            // case class ConcreteInt 
            // case class ConcreteBV 
            // case class ConcreteArray 
            // additiion / subtract  (Look at OperatorApplication)
            // case class OperatorApplication(op: Operator, operands: List[Expr])
                // do a case match on the op
            case _ => throw new NotImplementedError(s"Expression evaluation for ${expr}")
        }
    }

    def pretty_print(assn: scala.collection.mutable.Map[Identifier, ConcreteValue]) : Unit = {
        for (a <- assn) {
            println(a)
        }   
    }

    // assn(Id("n")) = ConcreteInt(assn(Id("n")).value + 1)

    /**
    executeOneStep is responsible for taking in a current assignment and a command to find out the next assignment for the variables

    Input:
        assn
        stmt
    Output:
        assn
    */ 
    // def executeOneStep (assn: ConcreteAssignment, stmt: Statement) : Assignment = {}
            // check the type of assignment
            
            // execute statement
            // assn(Id("n")) = ConcreteInt(assn(Id("n")).value + 1)


    //     return Assignment

}