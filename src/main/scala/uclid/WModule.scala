package uclid

import scala.language.implicitConversions

import scala.collection.mutable.MutableList
import lang._


trait AGContract {
    val assume: WExpr
    val guarantee: WExpr
}

case class WStmt(stmt: List[Statement])

sealed abstract class WExpr {
    def expr : Expr = this match {
        case wopexpr: WOpExpr => wopexpr.opexpr
        case wlit: WLit => wlit.lit
        case wid: WId => wid.id
    }

    def + (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(AddOp(), List(this.expr, that.expr)))
    def - (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(SubOp(), List(this.expr, that.expr)))
    def * (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(MulOp(), List(this.expr, that.expr)))
    def / (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(DivOp(), List(this.expr, that.expr)))
    def < (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(LTOp(), List(this.expr, that.expr)))
    def <= (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(LEOp(), List(this.expr, that.expr)))
    def > (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(GTOp(), List(this.expr, that.expr)))
    def >= (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(GEOp(), List(this.expr, that.expr)))
    def === (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(EqualityOp(), List(this.expr, that.expr)))
    def !== (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(InequalityOp(), List(this.expr, that.expr)))
    def && (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(ConjunctionOp(), List(this.expr, that.expr)))
    def || (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(DisjunctionOp(), List(this.expr, that.expr)))
    def unary_! : WOpExpr = WOpExpr(OperatorApplication(NegationOp(), List(this.expr)))
    def unary_- : WOpExpr = WOpExpr(OperatorApplication(UnaryMinusOp(), List(this.expr)))
    def unary_~ : WOpExpr = WOpExpr(OperatorApplication(BVNotOp(0), List(this.expr)))
    def << (i: Int) : WOpExpr = WOpExpr(OperatorApplication(BVLeftShiftBVOp(i), List(this.expr)))
    def >> (i: Int) : WOpExpr = WOpExpr(OperatorApplication(BVLRightShiftBVOp(i), List(this.expr)))
    def >>> (i: Int) : WOpExpr = WOpExpr(OperatorApplication(BVARightShiftBVOp(i), List(this.expr)))
    def & (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(BVAndOp(0), List(this.expr, that.expr)))
    def | (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(BVOrOp(0), List(this.expr, that.expr)))
    def ^ (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(BVXorOp(0), List(this.expr, that.expr)))

}

object WExpr {
    implicit def intToWLit (i: Int) : WExpr = WLit(IntLit(BigInt(i)))
}

case class WOpExpr (opexpr: Expr) extends WExpr {

    def apply (that: WExpr) : WOpExpr = WOpExpr(OperatorApplication(ArraySelect(List(that.expr)), List(this.expr)))

    def __ (that: WExpr) : WOpExpr = {
        that.expr match {
            case id: Identifier => WOpExpr(OperatorApplication(RecordSelect(id), List(this.expr)))
            case _ => throw new IllegalArgumentException("Record select must be applied to an identifier")
        }
    }


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


// Wrapped identifier
case class WId (id: Identifier) extends WExpr {
    def p () : WOpExpr = WOpExpr(OperatorApplication(GetNextValueOp(), List(this.id)))

    def getAsLHS () : Lhs = LhsId(id)

    def := (that: WExpr) : WStmt = WStmt(List(AssignStmt(List(this.getAsLHS()), List(that.expr))))
}
// Wrapped literal
case class WLit (lit: Literal) extends WExpr
// Named expressions
case class WSpec(name: String, expr: WExpr)
// Named axioms
case class WAxiom(name: String, expr: WExpr)

abstract class WModule {
    val name : String
    def name_ : Identifier = Identifier(name)

    var types : MutableList[TypeDecl] = MutableList()

    var variables : MutableList[StateVarsDecl] = MutableList()
    var inputs : MutableList[InputVarsDecl] = MutableList()
    var outputs : MutableList[OutputVarsDecl] = MutableList()

    var specs : MutableList[SpecDecl] = MutableList()
    var axioms : MutableList[AxiomDecl] = MutableList()

    var instances : MutableList[InstanceDecl] = MutableList()

    var _init : WStmt = WStmt(List())
    def init (stmt: WStmt) = (this._init = stmt)

    var _next : WStmt = WStmt(List())    
    def next (stmt: WStmt) = (this._next = stmt)

    var _control : List[GenericProofCommand] = List()
    def control (cmds: GenericProofCommand*) = (_control = cmds.toList)

    def WExprToExpr (wexpr: WExpr) : Expr = wexpr match {
        case wopexpr: WOpExpr => wopexpr.expr
        case wlit: WLit => wlit.lit
        case wid: WId => wid.id
    }

    def WStmtToStmt (wstmt: WStmt) : Statement = BlockStmt(List(), wstmt.stmt)

    def mkVar(name: String, typ: Type) : WId = {
        val newvar = StateVarsDecl(List(Identifier(name)), typ)
        variables.+=(newvar)
        WId(Identifier(name))
    }

    def mkInput (name: String, typ: Type) : WId = {
        val newvar = InputVarsDecl(List(Identifier(name)), typ)
        inputs.+=(newvar)
        WId(Identifier(name))
    }

    def mkOutput (name: String, typ: Type) : WId = {
        val newvar = OutputVarsDecl(List(Identifier(name)), typ)
        outputs.+=(newvar)
        WId(Identifier(name))
    }
    
    def mkSynonymType(name: String, typ: Type) : Type = {
        val newtype = TypeDecl(Identifier(name), typ)
        types.+=(newtype)
        SynonymType(Identifier(name))
    }

    def mkRecordType(name: String, fields: List[(String, Type)]) : Tuple2[Type, List[WExpr]] = {
        val newtype = TypeDecl(Identifier(name), RecordType(fields.map(x => (Identifier(x._1), x._2))))
        types.+=(newtype)
        (SynonymType(Identifier(name)), fields.map(x => WId(Identifier(x._1))))
    }
    
    def mkProperty (name: String, expr: WExpr) : WSpec = {
        val newspec = SpecDecl(Identifier(name), WExprToExpr(expr), List.empty)
        specs.+=(newspec)
        WSpec(name, expr)
    }

    def mkAxiom (name: String, expr: WExpr) : WAxiom = {
        val newaxiom = AxiomDecl(Some(Identifier(name)), WExprToExpr(expr), List.empty)
        axioms.+=(newaxiom)
        WAxiom(name, expr)
    }

    def mkInstance (name: String, module: WModule, connections: List[(WId, WExpr)]) : InstanceDecl = {
        val inst = InstanceDecl(Identifier(name), Identifier(module.name), 
            connections.map(x => (x._1.id, Some(WExprToExpr(x._2)))), None, None)
        instances.+=(inst)
        inst
    }

    def buildModule () : Module = {
        val initblock = InitDecl(BlockStmt(List(), _init.stmt))
        val nextblock = NextDecl(BlockStmt(List(), _next.stmt))
        
        val decls = (types 
            ++ variables ++ inputs ++ outputs
            ++ instances
            ++ List(initblock, nextblock)
            ++ specs ++ axioms
        )

        Module(Identifier(name), decls.toList, _control, Annotation.default)
    }

    def detestbenchify () : Unit = {
        this._control = List()
        this.specs = MutableList()
    }

    def <==> (mod2 : WModule) : WModule = {
        WModule.mkEquivalenceProofModule(name + "_" + mod2.name + "_equiv", this, mod2)
    }

}

object WModule {
    def apply () : WModule = {
        new WModule {
            val name = "main"
        }
    }

    // Literal sugaring
    def Int (i: Integer) : WLit = WLit(IntLit(BigInt(i)))
    def True () : WLit = WLit(BoolLit(true))
    def False () : WLit = WLit(BoolLit(false))
    def BV (i: BigInt, width: Int) : WLit = WLit(BitVectorLit(i, width))

    // Type sugaring
    val intType = lang.IntegerType()
    val boolType = lang.BooleanType()
    def bvType (i : Int) = lang.BitVectorType(i)
    def arrayType (index : Type, value : Type) = lang.ArrayType(List(index), value)

    def ite (ifexpr: WExpr, thenexpr: WExpr, elseexpr: WExpr) : WExpr = 
        WOpExpr(OperatorApplication(ITEOp(), List(ifexpr.expr, thenexpr.expr, elseexpr.expr)))
    def block (stmts: WStmt*) : WStmt = WStmt(stmts.flatMap(_.stmt).toList)

    def bmc (k: Int) : GenericProofCommand = GenericProofCommand(Identifier("bmc"), List.empty, List((IntLit(k), k.toString())), None, None, None)
    def check : GenericProofCommand = GenericProofCommand(Identifier("check"), List.empty, List.empty, None, None, None)
    def print_result : GenericProofCommand = GenericProofCommand(Identifier("print_results"), List.empty, List.empty, None, None, None)

    def next (mod: InstanceDecl) : WStmt =  WStmt(List(ModuleCallStmt(mod.instanceId)))


    def mkEncapsulation (parentname : String, childs: List[(WModule, Int)]) : WModule = {
        val parent = new WModule () {
            val name = parentname
        }

        childs.foreach(x => {
            val child = x._1
            val count = x._2
            for (i <- 0 until count) {
                val i_name = child.name + count.toString + "_" + i
                parent.mkInstance(i_name, child, 
                    child.inputs.flatMap(x => x.ids.map(y => (WId(y), parent.mkVar(y.name + "_in_" + i_name, x.typ)))).toList
                    ++ child.outputs.flatMap(x => x.ids.map(y => (WId(y), parent.mkVar(y.name + "_out_" + i_name, x.typ)))).toList
                )
            }
        })

        parent
    }

    def mkEncapsulationSingle (parentname : String, child: WModule) : WModule = 
        mkEncapsulation(parentname, List((child, 1)))

    def mkEquivalenceProofModule (parentname: String, child1_ : WModule, child2_ : WModule) : WModule = {

        val child1 = child1_
        child1.detestbenchify()        
        val child2 = child2_
        child2.detestbenchify()

        val parent = new WModule () {
            val name = parentname
        }

        // Check equivalence of inputs and outputs
        val child1_ins = child1.inputs.flatMap(x => x.ids.map(y => (y, x.typ))).toSet
        val child2_ins = child2.inputs.flatMap(x => x.ids.map(y => (y, x.typ))).toSet
        val child1_outs = child1.outputs.flatMap(x => x.ids.map(y => (y, x.typ))).toSet
        val child2_outs = child2.outputs.flatMap(x => x.ids.map(y => (y, x.typ))).toSet
        // Check if inputs and outputs are the same
        if (child1_ins != child2_ins) {
            UclidMain.printWarning("Inputs of child1 and child2 are not the same in equivalence proof")
        }
        if (child1_outs != child2_outs) {
            UclidMain.printError("Outputs of child1 and child2 are not the same in equivalence proof")
        }

        val inputs = child1_ins.union(child2_ins).map(
            x => (x._1, parent.mkVar(x._1.name + "_in", x._2))).toMap
        val outputs1 = child1_outs.map(
            x => (x._1, parent.mkVar(x._1.name + "_out_1", x._2))).toMap
        val outputs2 = child2_outs.map(
            x => (x._1, parent.mkVar(x._1.name + "_out_2", x._2))).toMap


        val child1_name = child1.name + "_1"
        val i1 = parent.mkInstance(child1_name, child1, 
            child1.inputs.flatMap(x => x.ids.map(y => (WId(y), inputs(y)))).toList
            ++ child1.outputs.flatMap(x => x.ids.map(y => (WId(y), outputs1(y)))).toList
        )
        val child2_name = child2.name + "_2"
        val i2 = parent.mkInstance(child2_name, child2, 
            child2.inputs.flatMap(x => x.ids.map(y => (WId(y), inputs(y)))).toList
            ++ child2.outputs.flatMap(x => x.ids.map(y => (WId(y), outputs2(y)))).toList
        )

        parent.next {
            block(
                next(i1), next(i2)
            )
        }
        
        val equiv_spec = parent.mkProperty("equiv", 
            child1_outs.map(x => outputs1(x._1) === outputs2(x._1)).reduce((x, y) => x && y)
        )
        parent
    }


    def mkPrePostModule (mod: WModule with AGContract) : WModule = {
        val prepostmodule = mod
        val axiom = prepostmodule.mkAxiom("assumption", prepostmodule.assume)
        val spec = prepostmodule.mkProperty("guarantee", prepostmodule.guarantee)
        prepostmodule
    }

    def mkAGModule (parentname: String, g_mod: WModule with AGContract, a_mod: WModule with AGContract) : WModule = {
        val parent = new WModule () {
            val name = parentname
        }

        // Check that the outputs of G match the inputs of A
        val g_outs = g_mod.outputs.flatMap(x => x.ids.map(y => (y, x.typ))).toSet
        val a_ins = a_mod.inputs.flatMap(x => x.ids.map(y => (y, x.typ))).toSet
        if (g_outs != a_ins) {
            UclidMain.printError(s"Outputs of G = ${g_mod.name} and inputs of A = ${a_mod.name} are not the same in AG proof")
        }
        g_mod.outputs.flatMap(x => x.ids.map(y => (WId(y), parent.mkVar(y.name, x.typ))))        
        parent.mkAxiom("guarantees", g_mod.guarantee)
        parent.mkProperty("assumes", a_mod.assume)
        parent
    }

}