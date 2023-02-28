package uclid

import lang._

object UclidProceduralTest {

    def main (args: Array[String]) : Unit = {


        val vara = StateVarsDecl(List(Identifier("a")), IntegerType())

        val initdecl = InitDecl(
            BlockStmt(
                List(),
                List(AssignStmt(List(LhsId(Identifier("a"))), List(IntLit(0))))
            )
        )
        val nextdecl = NextDecl (
            BlockStmt(
                List(),
                List(ProcedureCallStmt(Identifier("myProc"), List(), List(), None, None), SkipStmt())
            )
        )

        val toyProc = ProcedureDecl(
            Identifier("myProc"),
            ProcedureSig(List(), List()),
            BlockStmt(
                List(),
                List(AssignStmt(List(LhsId(Identifier("a"))), List(OperatorApplication(AddOp(), List(Identifier("a"), IntLit(1))))))
            ),
            List(),
            List(),
            Set(ModifiableId(Identifier("a"))),
            ProcedureAnnotations(Set())
        )

        val spec = SpecDecl(Identifier("simplespec"), OperatorApplication(LTOp(), List(Identifier("a"), IntLit(4))), List())

        val cmds = GenericProofCommand(Identifier("unroll"), List.empty, List((IntLit(5), "5")), None, None, None)

        val procConfig = UclidProceduralMain.ProceduralConfig("mainProc", List(), smtFileGeneration = "", "cex", false, true, false, 1)

        UclidProceduralMain.solveProcedural(procConfig, List(initdecl, nextdecl, spec, toyProc, vara), List(cmds))
    }

}

