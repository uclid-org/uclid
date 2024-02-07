
package uclid
package test

import lang._
import WModule._

import org.scalatest.flatspec.AnyFlatSpec

object SimpleModule extends WModule {

    val name: String = "temp"

    val a = mkOutput("a", intType)
    val b = mkVar("b", intType)

    init {block(
        a := 0,
        b := 0
    )}

    next {block(
        a.p() := a + 1
    )}

    val prop1 = mkProperty (
        "prop1", a === 0
    )
}


object PlantA extends WModule with AGContract {
    val name: String = "plant1"
    val a = mkInput ("a", intType)
    val b = mkOutput ("b", intType)
    init {block(
        b := 2
    )}
    next {block(
        b.p() := a + a
    )}
    val assume: WExpr = a > 0
    val guarantee: WExpr = b > 0
}

object PlantB extends WModule with AGContract {
    val name: String = "plant2"
    val a = mkOutput ("a", intType)
    val b = mkInput ("b", intType)

    init {block (
        a := 1
    )}
    next {block (
        a.p() := ite(b > 0, b + 1, 0)
    )}
    val assume: WExpr = b > 0
    val guarantee: WExpr = a > 0
}

class APISpec extends AnyFlatSpec {
    
    "test-UclidAPI-0" should "pass successfully." in {
        val check_result = ProofStrategies.performBMCProof(SimpleModule, 4)
        println(check_result)
        assert (check_result.contains("Successfully instantiated 1 module(s)."))
        assert (check_result.contains("Finished execution for module: temp."))
    }

    "test-equivalence-proof" should "perform successful equivalence proof!" in {
        val check_result = ProofStrategies.performEquivalenceProof(SimpleModule, SimpleModule)
        println(check_result)
        assert(check_result.contains("assertions passed."))
    }

    "test-AG-proof" should "perform successful AG proof!" in {
        val check_result = ProofStrategies.performAGProof(PlantA, PlantB)
        println(check_result)
        assert(check_result.contains("assertions passed."))
        
    }
}


/**
  * 
  * pre post synthesis with a grammar
  * mod1, mod2 are partially specified (no pre-post)
  * def synthesis (mod1, mod2) = {
  * 
  * while (true) {
  *   check = AG(mod1, mod2)
  * 
  *   if (!check) {
  *     get and use CEX
  *     enumerate pre, post from grammar
  *     mod1 +: pre
  *     mod2 +: post
  *   } else break
  * }
  * 
  * return mod1, mod2
  * 
  * }
  * 
  */
