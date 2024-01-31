
package uclid
package test

import lang._
import WModule._

import com.typesafe.scalalogging.Logger

import org.scalatest.flatspec.AnyFlatSpec
import scala.compat.Platform

object SimpleModule extends WModule {

    val name: String = "temp"

    val a = mkOutput("a", intType)
    val b = mkVar("b", intType)

    var init = block(List(
        a := Int(0),
        b := Int(0)
    ))

    var next = block(List(
        a.p() := a + Int(1)
    ))

    val prop1 = mkProperty (
        "prop1", a === Int(0)
    )

    control = List(
        bmc(4),
        check,
        print_result
    )
}


object PlantA extends WModule with AGContract {
    val name: String = "plant1"
    val a = mkInput ("a", intType)
    val b = mkOutput ("b", intType)
    var init = block(List(
        b := Int(2)
    ))
    var next = block(List(
        b.p() := a + a
    ))
    val assume: WExpr = a > Int(0)
    val guarantee: WExpr = b > Int(0)
}

object PlantB extends WModule with AGContract {
    val name: String = "plant2"
    val a = mkOutput ("a", intType)
    val b = mkInput ("b", intType)

    var init = block(List(
        a := Int(1)
    ))
    var next = block(List(
        a.p() := ite(b > Int(0), b + Int(1), Int(0))
    ))
    val assume: WExpr = b > Int(0)
    val guarantee: WExpr = a > Int(0)
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
