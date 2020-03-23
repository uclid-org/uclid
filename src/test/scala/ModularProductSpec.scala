/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Authors: Norman Mu, Pramod Subramanyan
 *
 * UCLID ModularProduct tests.
 *
 */

package uclid
package test

import org.scalatest.FlatSpec
import uclid.{lang => l}
import java.io.File

object ModularProductHelperSpec {
    def expectedFails(filename: String, nFail : Int) : String = {
        UclidMain.enableStringOutput()
        UclidMain.clearStringOutput()
        val config = UclidMain.Config() 
        val modules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"), true)
        val mainModule = UclidMain.instantiate(config, modules, l.Identifier("main"), false)
        assert (mainModule.isDefined)
        val results = UclidMain.execute(mainModule.get, config)
        val outputString = UclidMain.stringOutput.toString()
        assert (results.count((e) => e.result.isFalse) == nFail)
        assert (results.count((e) => e.result.isUndefined) == 0)
        outputString
    }
}

class ModularProductSpec extends FlatSpec {

    "test-modularproduct-1.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-1.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-2-fails.ucl" should "not parse successfully." in {
        try {
        val filename = "test/test-modularproduct-2-fails.ucl"
        val fileModules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"))
        assert (fileModules.size == 1)
        }
        catch {
        case p : Utils.ParserError =>
            assert(p.getMessage() == "Pre/Post Conditions using trace select should use atleast two traces")       
        }
    }

    "test-modularproduct-3.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-3.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-4.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-4.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-5.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-5.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-6.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-6.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-7.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-7.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-8.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-8.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-9.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-9.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-10.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-10.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-11-fails.ucl" should "not parse successfully." in {
        try {
        val filename = "test/test-modularproduct-11-fails.ucl"
        val fileModules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"))
        assert (fileModules.size == 1)
        }
        catch {
        case p : Utils.UnimplementedException =>
            assert(p.getMessage() == "Procedures with trace select pre/post conditions are not allowed to use/modify module level variables")       
        }
    }

    "test-modularproduct-12.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-12.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-13.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-13.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-14.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-14.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-15.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-15.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-16.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-16.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }

    "test-modularproduct-17.ucl" should "parse successfully." in {
        val fileModules = UclidMain.compile(List(new File("test/test-modularproduct-17.ucl")), lang.Identifier("main"))
        val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
        assert (instantiatedModules.size == 1);
    }
   
    "test-modularproduct-18-fails.ucl" should "fail to verify 2 assertions" in {
        ModularProductHelperSpec.expectedFails("./test/test-modularproduct-18-fails.ucl", 1)
    }

    "test-modularproduct-19-fails.ucl" should "fail to verify 1 assertion out of 9" in {
        ModularProductHelperSpec.expectedFails("./test/test-modularproduct-19-fails.ucl", 1)
    }

    "test-modularproduct-20.ucl" should "verify successfully" in {
        ModularProductHelperSpec.expectedFails("./test/test-modularproduct-20.ucl", 0)
    }

    "test-modularproduct-21-fails.ucl" should "not parse successfully" in {
        try {
        val filename = "test/test-modularproduct-21-fails.ucl"
        val fileModules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"))
        assert (fileModules.size == 1)
        }
        catch {
        case p : Utils.ParserError =>
            assert(p.getMessage() == "Trace Value cannot be zero")       
        }
    }

    "test-modularproduct-22-fails.ucl" should "not parse successfully" in {
        try {
        val filename = "test/test-modularproduct-22-fails.ucl"
        val fileModules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"))
        assert (fileModules.size == 1)
        }
        catch {
        case p : Utils.ParserError =>
            assert(p.getMessage() == "Non sequential trace values are not allowed")       
        }
    }


}
