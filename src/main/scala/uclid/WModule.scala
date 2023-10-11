package uclid

import scala.collection.mutable.MutableList
import _root_.uclid.lang._


case class WStmt(stmt: List[Statement])

case class WExpr (expr: Expr) {
    def + (that: WExpr) : WExpr = WExpr(OperatorApplication(AddOp(), List(this.expr, that.expr)))
    def - (that: WExpr) : WExpr = WExpr(OperatorApplication(SubOp(), List(this.expr, that.expr)))
    def * (that: WExpr) : WExpr = WExpr(OperatorApplication(MulOp(), List(this.expr, that.expr)))
    def / (that: WExpr) : WExpr = WExpr(OperatorApplication(DivOp(), List(this.expr, that.expr)))
    def < (that: WExpr) : WExpr = WExpr(OperatorApplication(LTOp(), List(this.expr, that.expr)))
    def <= (that: WExpr) : WExpr = WExpr(OperatorApplication(LEOp(), List(this.expr, that.expr)))
    def > (that: WExpr) : WExpr = WExpr(OperatorApplication(GTOp(), List(this.expr, that.expr)))
    def >= (that: WExpr) : WExpr = WExpr(OperatorApplication(GEOp(), List(this.expr, that.expr)))
    def === (that: WExpr) : WExpr = WExpr(OperatorApplication(EqualityOp(), List(this.expr, that.expr)))
    def !== (that: WExpr) : WExpr = WExpr(OperatorApplication(InequalityOp(), List(this.expr, that.expr)))
    def && (that: WExpr) : WExpr = WExpr(OperatorApplication(ConjunctionOp(), List(this.expr, that.expr)))
    def || (that: WExpr) : WExpr = WExpr(OperatorApplication(DisjunctionOp(), List(this.expr, that.expr)))
    def unary_! : WExpr = WExpr(OperatorApplication(NegationOp(), List(this.expr)))
    def unary_- : WExpr = WExpr(OperatorApplication(UnaryMinusOp(), List(this.expr)))
    def unary_~ : WExpr = WExpr(OperatorApplication(BVNotOp(0), List(this.expr)))
    def << (i: Int) : WExpr = WExpr(OperatorApplication(BVLeftShiftBVOp(i), List(this.expr)))
    def >> (i: Int) : WExpr = WExpr(OperatorApplication(BVLRightShiftBVOp(i), List(this.expr)))
    def >>> (i: Int) : WExpr = WExpr(OperatorApplication(BVARightShiftBVOp(i), List(this.expr)))
    def & (that: WExpr) : WExpr = WExpr(OperatorApplication(BVAndOp(0), List(this.expr, that.expr)))
    def | (that: WExpr) : WExpr = WExpr(OperatorApplication(BVOrOp(0), List(this.expr, that.expr)))
    def ^ (that: WExpr) : WExpr = WExpr(OperatorApplication(BVXorOp(0), List(this.expr, that.expr)))

    def apply (that: WExpr) : WExpr = WExpr(OperatorApplication(ArraySelect(List(that.expr)), List(this.expr)))

    def __ (that: WExpr) : WExpr = {
        that.expr match {
            case id: Identifier => WExpr(OperatorApplication(RecordSelect(id), List(this.expr)))
            case _ => throw new IllegalArgumentException("Record select must be applied to an identifier")
        }
    }

    def p () : WExpr = WExpr(OperatorApplication(GetNextValueOp(), List(this.expr)))

    def getAsLHS () : Lhs = {
        this.expr match {
            case id: Identifier => LhsId(id)
            case appl: OperatorApplication => {
                appl.op match {
                    case arrsel: ArraySelect => appl.operands(0) match {
                        case id: Identifier => LhsArraySelect(id, arrsel.indices)
                        case _ => throw new IllegalArgumentException("LHS of assignment must be an identifier")
                    }
                    case recsel: RecordSelect => appl.operands(0) match {
                        case id: Identifier => LhsRecordSelect(id, List(recsel.id))
                        case _ => throw new IllegalArgumentException("LHS of assignment must be an identifier")
                    }
                    case nextop: GetNextValueOp => appl.operands(0) match {
                        case id: Identifier => LhsNextId(id)
                        case _ => throw new IllegalArgumentException("LHS of assignment must be an identifier")
                    }
                    case _ => throw new IllegalArgumentException("LHS of assignment must be an identifier")
                }
            }
            case _ => throw new IllegalArgumentException("LHS of assignment must be an identifier")
        }
    }

    def := (that: WExpr) : WStmt = WStmt(List(AssignStmt(List(this.getAsLHS()), List(that.expr))))
}


abstract class WModule {
    val name : String
    def name_ : Identifier = Identifier(name)

    var types : MutableList[TypeDecl] = MutableList()

    var variables : MutableList[StateVarsDecl] = MutableList()

    val init : WStmt

    val next : WStmt

    def mkVar(name: String, typ: Type) : WExpr = {
        val newvar = StateVarsDecl(List(Identifier(name)), typ)
        variables.+=(newvar)
        WExpr(Identifier(name))
    }
    
    def mkSynonymType(name: String, typ: Type) : Type = {
        val newtype = TypeDecl(Identifier(name), typ)
        types.+=(newtype)
        SynonymType(Identifier(name))
    }

    def mkRecordType(name: String, fields: List[(String, Type)]) : Tuple2[Type, List[WExpr]] = {
        val newtype = TypeDecl(Identifier(name), RecordType(fields.map(x => (Identifier(x._1), x._2))))
        types.+=(newtype)
        (SynonymType(Identifier(name)), fields.map(x => WExpr(Identifier(x._1))))
    }


    var control : List[GenericProofCommand] = List()

    def WExprToExpr (wexpr: WExpr) : Expr = wexpr.expr

    def WStmtToStmt (wstmt: WStmt) : Statement = BlockStmt(List(), wstmt.stmt)
    

    def buildModule () : Module = {
        val initblock = InitDecl(BlockStmt(List(), init.stmt))
        val nextblock = NextDecl(BlockStmt(List(), next.stmt))
        
        val decls = (types 
            ++ variables
            ++ List(initblock, nextblock))

        Module(Identifier(name), decls.toList, control, List())
    }

}

object WModule {
    def apply () : WModule = {
        new WModule {
            val name = "main"
            val init = WStmt(List())
            val next = WStmt(List())
        }
    }

    val intType = _root_.uclid.lang.IntegerType()

    val boolType = _root_.uclid.lang.BooleanType()
    
    def bvType (i : Int) = _root_.uclid.lang.BitVectorType(i)

    def arrayType (index : Type, value : Type) = _root_.uclid.lang.ArrayType(List(index), value)

    def block (stmts: List[WStmt]) : WStmt = WStmt(stmts.flatMap(_.stmt))

    def bmc (k: Int) : GenericProofCommand = GenericProofCommand(Identifier("bmc"), List.empty, List((IntLit(k), k.toString())), None, None, None)
    def check : GenericProofCommand = GenericProofCommand(Identifier("check"), List.empty, List.empty, None, None, None)
    def print_result : GenericProofCommand = GenericProofCommand(Identifier("print_result"), List.empty, List.empty, None, None, None)
}