package uclid

import lang._

object UclidProceduralTest {

    def main (args: Array[String]) : Unit = {


        val vara = StateVarsDecl(List(Identifier("a")), IntegerType())

        val toyProc = ProcedureDecl(
            Identifier("myProc"),
            ProcedureSig(List(), List()),
            AssignStmt(List(LhsId(Identifier("a"))), List(OperatorApplication(AddOp(), List(Identifier("a"), IntLit(1))))),
            List(),
            List(),
            Set(ModifiableId(Identifier("a"))),
            ProcedureAnnotations(Set())
        )

        val cmds = GenericProofCommand(Identifier("unroll"), List.empty, List((IntLit(5), "5")), None, None, None)

        val procConfig = UclidProceduralMain.ProceduralConfig("mainProc", List(), smtFileGeneration = "temp.smt2", "cex", false, true, false, 1)

        UclidProceduralMain.solveProcedural(procConfig, List(toyProc, vara), List(cmds))
    }

}

