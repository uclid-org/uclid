package uclid


import WModule._

object ProofStrategies {
    
    def performBMCProof (mod: WModule, bound : Int = 4) : String = {
        mod.control (bmc(bound), check, print_result)

        UclidMain.printDetailedStats("BMC module building successful!")
        UclidMain.printDetailedStats(mod.buildModule().toString())
        val pconfig = UclidAPI.APIConfig(List(mod), 
            mod.name, smtSolver=List("z3", "-in"))
        UclidAPI.solveProcedural(pconfig)
    }


    def performEquivalenceProof (mod1: WModule, mod2: WModule) : String = {

        val composition = (mod1 <==> mod2)

        composition.control (bmc(4),check,print_result)

        UclidMain.printStatus("Equivalence proof module building successful!")
        UclidMain.printDetailedStats(composition.buildModule().toString())

        val pconfig = UclidAPI.APIConfig(Set(mod1, mod2).toList ++ List(composition), 
            composition.name, smtSolver=List("z3", "-in"))
        
        UclidAPI.solveProcedural(pconfig)
    }


    def performAGProof (mod1: WModule with AGContract, mod2: WModule with AGContract) : String = {

        if (mod1 == mod2) {
            UclidMain.printError("Modules are the same in AG proof!")
        }

        // Mod1 guarantees Mod2 environment
        val mod1_g_mod2_a = mkAGModule("mod1_g_mod2_a", mod1, mod2)
        mod1_g_mod2_a.control (bmc(1), check, print_result)
        val pconfig1 = UclidAPI.APIConfig(List(mod1_g_mod2_a), 
            mod1_g_mod2_a.name, smtSolver=List("z3", "-in"))
        val res1 = "module1 guarantees module2\n" + UclidAPI.solveProcedural(pconfig1)

        // Mod2 guarantees Mod1 environment
        val mod2_g_mod1_a = mkAGModule("mod2_g_mod1_a", mod2, mod1)
        mod2_g_mod1_a.control (bmc(1), check, print_result)
        val pconfig2 = UclidAPI.APIConfig(List(mod2_g_mod1_a), 
            mod2_g_mod1_a.name, smtSolver=List("z3", "-in"))
        val res2 = "module2 guarantees module1\n" + UclidAPI.solveProcedural(pconfig2)

        // Mod1 pre-post are valid
        val mod1_local = mkPrePostModule(mod1)
        mod1_local.control (bmc(4), check, print_result)

        UclidMain.printDetailedStats("Prepost module building successful!")
        UclidMain.printDetailedStats(mod1_local.buildModule().toString())
        
        val pconfig3 = UclidAPI.APIConfig(List(mod1_local), 
            mod1_local.name, smtSolver=List("z3", "-in"))
        val res3 = "module1 pre-post hold!\n" + UclidAPI.solveProcedural(pconfig3)

        // Mod2 pre-post are valid
        val mod2_local = mkPrePostModule(mod2)
        mod2_local.control (bmc(4), check, print_result)

        UclidMain.printDetailedStats("Prepost module building successful!")
        UclidMain.printDetailedStats(mod2_local.buildModule().toString())
        val pconfig4 = UclidAPI.APIConfig(List(mod2_local), 
            mod2_local.name, smtSolver=List("z3", "-in"))
        val res4 = "module2 pre-post hold\n" + UclidAPI.solveProcedural(pconfig4)


        val res = res1 + "\n" + res2 + "\n" + res3 + "\n" + res4
        res
    }



}