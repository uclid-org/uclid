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
 * UCLID Parser/Typechecker tests.
 *
 */

package uclid
package test

import org.scalatest.flatspec.AnyFlatSpec
import uclid.{lang => l}
import java.io.File

class ParserSpec extends AnyFlatSpec {
  "test-adt-5-reusingdatatypename.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-adt-5-reusingdatatypename.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
    }
  }
  "test-adt-6-reusingselectorname.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-adt-6-reusingselectorname.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
    }
  }
  "test-adt-9-badconstructing.ucl" should "not typecheck." in {
    try {
      val filename = "test/test-adt-9-badconstructing.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
    }
  }
  "test-adt-10-badconstructing.ucl" should "not typecheck." in {
    try {
      val filename = "test/test-adt-10-badconstructing.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
    }
  }
  "test-adt-11-badconstructing.ucl" should "not typecheck." in {
    try {
      val filename = "test/test-adt-11-badconstructing.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size > 0)
    }
  }
  "test-adt-12-badselecting.ucl" should "not typecheck." in {
    try {
      val filename = "test/test-adt-12-badselecting.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size > 0)
    }
  }
  "test-adt-13-badselecting.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-adt-13-badselecting.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
    }
  }
  "test-adt-15-multiplemodules.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-adt-15-multiplemodules.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size > 0)
    }
  }
  "test-adt-20.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-adt-20.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserError =>
        assert (p.getMessage().contains("Function redeclaration error in module"))
    }
  }
  "test-adt-21.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-adt-21.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserError =>
        assert (p.getMessage().contains("Function redeclaration error in module"))
    }
  }
  "test-adt-22.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-adt-22.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size > 0)
    }
  }
  "test-adt-23.ucl" should "parse successfully" in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-adt-23.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-type1.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-type1.ucl"
      val fileModules = UclidMain.compile(ConfigCons.createConfig(filename), lang.Identifier("main"))
      assert (fileModules.size == 1)
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0)._1.contains("Redeclaration of identifier 'test'."))
    }
  }
  "test-typechecker-0.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-0.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 8)
    }
  }
  "test-typechecker-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-1.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        val msg : String = p.errors(0)._1
        assert (msg.contains("Unknown identifier in havoc statement"))
    }
  }
  "test-module-errors.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-module-errors.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 5)
    }
  }
  "test-typechecker-6.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-6.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
    }
  }
  "test-typechecker-3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-3.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
    }
  }
  "test-typechecker-4.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-4.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
    }
  }
  "test-recursion.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-recursion.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0)._1.contains("Recursion"))
    }
  }
  "test-recursion-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-recursion-2.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0)._1.contains("Recursion"))
    }
  }
  "test-procedure-types-errors.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-procedure-types-errors.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
        assert (p.errors.forall(p => p._1.contains("Parameter r expected")))
    }
  }
  "test-procedure-invocation-errors.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-procedure-invocation-errors.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0).getMessage().contains("Cannot apply foo, which is of type procedure"))
    }
  }
  "test-syntax-errors-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-syntax-errors-1.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 3)
        assert (p.errors.forall(e => e.getMessage().contains("Argument to select operator must be of type record or instance")))
    }
  }
  "test-typechecker-5.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-5.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeError =>
        assert (p.getMessage().contains("Recursively defined synonym type"))
    }
  }
  "test-modules-2.ucl" should "not parse successfully." in {
    try {
     val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-modules-2.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 4)
    }
  }
  "test-procedure-checker-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-procedure-checker-1.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.exists(p => p._1.contains("Identifier was not declared modifiable: x")))
        assert (p.errors.exists(p => p._1.contains("Identifier cannot be declared modifiable: z")))
    }
  }
  "test-concat-modules-dup-decl.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-concat-modules-dup-decl.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.exists(p => p._1.contains("Redeclaration of identifier 'x'.")))
    }
  }
  "test-concat-modules.ucl" should "parse successfully" in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-concat-modules.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-concat-modules-w-init-1.ucl" should "parse successfully" in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-concat-modules-w-init-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-concat-modules-w-init-2-fab.ucl" should "parse successfully" in {
    val fileModules = UclidMain.compile(UclidMain.Config(files=List(
      new File("test/test-concat-modules-w-init-2-fa.ucl"), new File("test/test-concat-modules-w-init-2-fb.ucl"))
    ), lang.Identifier("main"))
    assert (fileModules.size == 2)
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-concat-modules-w-init-2-fba.ucl" should "parse successfully" in {
    val fileModules = UclidMain.compile(UclidMain.Config(files=List(
      new File("test/test-concat-modules-w-init-2-fb.ucl"), new File("test/test-concat-modules-w-init-2-fa.ucl"))
    ), lang.Identifier("main"))
    assert (fileModules.size == 2)
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-mod-set-analysis-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-0.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-mod-set-analysis-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-mod-set-analysis-2.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-2.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-mod-set-analysis-3.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-3.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-mod-set-analysis-6.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfigWithMSA("test/test-mod-set-analysis-6.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-mutual-recursion-error.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-mutual-recursion-error.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
        assert (p.errors.exists(p => p._1.contains("Recursion involving procedure(s)")))
    }
  }
  "test-parsing-history-op-error.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-parsing-history-op-error.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Operator can only be used in a verification expression")))
    }
  }
  "test-synthesis-grammar-0.ucl" should "parse successfully." in {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-synthesis-grammar-0.ucl"), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-synthesis-grammar-1.ucl" should "parse successfully." in {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-synthesis-grammar-1.ucl"), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-synthesis-grammar-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-synthesis-grammar-2.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      case r : Utils.RuntimeError => 
        assert (r.getMessage().contains("Could not find non terminal"));
    }
  }
  "test-synthesis-grammar-3.ucl" should "parse successfully." in {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-synthesis-grammar-3.ucl"), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-synthesis-grammar-4.ucl" should "parse successfully." in {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-synthesis-grammar-4.ucl"), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-synthesis-grammar-5.ucl" should "parse successfully." in {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-synthesis-grammar-5.ucl"), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-typechecker-7.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-7.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p.msg.contains("Arguments to operator '+' must be of the same type")))
    }
  }
  "test-typechecker-8.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-typechecker-8.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Return type and expression type do not match")))
    }
  }
  "test-module-import-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-module-import-1.ucl"), lang.Identifier("main"))
      // should never get here.
      // assert (false);
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0)._1.contains("Redeclaration of identifier 'bar'."))
    }
  }
  "test-module-import-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-module-import-2.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserError =>
        assert (p.getMessage().contains("Module module1 not found. Failed to import into main"))
    }
  }
  "test-types-import-redecl.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-types-import-redecl.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Redeclaration of identifier 'pc_t'")))
        assert (p.errors.exists(p => 
          (p._2.filename == Some("test/test-types-import-redecl.ucl") ||
           p._2.filename == Some("test\\test-types-import-redecl.ucl")) && p._2.pos.line == 32))
    }
  }
  "test-define-expand.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-define-expand.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-procedure-inline-bv.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-procedure-inline-bv.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-procedure-postcondition-2.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-procedure-postcondition-2.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-define-recursive.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-define-recursive.ucl"), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 3)
        assert (p.errors.exists(p => p._1.contains("Recursion involving define declarations")))
    }
  }
  "nested_instances.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/nested_instances.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-nested-modules-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-nested-modules-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-nested-modules-2.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-nested-modules-2.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-block-var-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-block-var-0.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-modules-7.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-modules-7.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-block-var-renaming-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-block-var-renaming-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-multiple-writes.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-multiple-writes.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.forall(p => p._1.contains("Multiple updates to identifier(s)")))
    }
  }
  "test-cyclic-deps.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-cyclic-deps.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.forall(p => p._1.contains("Cyclical dependency involving variable(s)")))
    }
  }
  "test-procedure-next.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-procedure-next.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.forall(p => p._1.contains("Multiple updates to identifier(s): v")))
    }
  }
  "test-modules-3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-modules-3.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.forall(p => p._1.contains("Invalid module output")))
    }
  }
  "test-modules-4.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-modules-4.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.exists(p => p._1.contains("Primed assignments are not allowed in procedural code")))
        assert (p.errors.exists(p => p._1.contains("Parallel construct next cannot be used in procedural code")))
    }
  }
  "test-primed-variables-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-primed-variables-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Primed variables can't be referenced inside procedures")))
    }
  }
  "test-forloop-error-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-forloop-error-1.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Invalid for loop range")))
    }
  }
  "test-string-0.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-string-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("expected type 'integer' but received type 'string'")))
    }
  }
  "test-string-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-string-1.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError =>
        assert (p.msg.contains("'print' command expects a string literal as an argument"))
    }
  }
  "test-parser-nested-next-block.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-parser-nested-next-block.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Nested block statements are not allowed in a sequential environment"))
    }
  }
  "array-update-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/array-update-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("'rom' is a readonly entity and cannot be assigned to"))
    }
  }
  "test-string-2.ucl" should "parse successfully." in {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-string-2.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    val results = UclidMain.execute(instantiatedModules(0), UclidMain.Config())
    val stringOutput = UclidMain.stringOutput.toString().trim()
    assert (instantiatedModules.size == 1)
    assert (stringOutput == "hello, world!")
  }

  "test-hyperproperty-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-hyperproperty-0.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "longcomment.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/longcomment.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-array-record.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-array-record.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-array-record-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-array-record-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-record-update-op-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-record-update-op-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0).getMessage().contains("Invalid field-name in record update operator"))
      case _ : Throwable => assert(false);
    }
  }
  "test-record-update-op-3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-3.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0).getMessage().contains("Expected a record here"))
      case _ : Throwable => assert(false);
    }
  }
  "test-record-update-op-4.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-4.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0).getMessage().contains("Invalid value-type in record update operator"))
      case _ : Throwable => assert(false);
    }
  }
  "test-record-update-op-5.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-5.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-record-update-op-8.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-8.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-record-update-op-10.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-10.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-record-update-op-11.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-record-update-op-11.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-const-record-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-const-record-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-const-record-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-const-record-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
        case p : Utils.ParserErrorList =>
          assert (p.errors.size == 1)
          assert (p.errors(0)._1.contains("expected type 'record {_rec_valid : boolean, _rec_value : integer}' but received type 'record {_rec_value : integer, _rec_valid : boolean}'"))
        case _ : Throwable => assert(false);
    }
  }
  "test-const-record-4.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-const-record-4.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-const-record-5.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-const-record-5.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0).getMessage().contains("Duplicate field-names in ConstRecord"))
      case _ : Throwable => assert(false);
    }
  }

  "recorderror.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/recorderror.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "inputerror.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/inputerror.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-hyperproperty-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-hyperproperty-1.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Trace select can only be used in a module-level expression"))
    }
  }

  /* This Test has been updated to not throw an error as trace selects are allowed inside procedural contexts. */

  // "test-hyperproperty-2.ucl" should "not parse successfully." in {
  //   try {
  //     val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-hyperproperty-2.ucl"), lang.Identifier("main"))
  //     assert (false)
  //   } catch {
  //     case p : Utils.ParserErrorList =>
  //       assert (p.errors(0)._1.contains("Trace select can only be used in a verification expression"))
  //   }
  // }
  "test-modify-instance.ucl" should "should parse successfully." in {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-modify-instance.ucl"), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-hyperproperty-2.ucl" should "should parse successfully." in {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-hyperproperty-2.ucl"), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-hyperproperty-3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-hyperproperty-3.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Trace select can only be used in a verification expression"))
    }
  }

  "proc_requires_3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/proc_requires_3.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.forall(e => e._1.contains("Old operator can't be used in a requires expression")))
    }
  }
  "test-expression-suffix-function.ucl" should "parse successfully" in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-expression-suffix-function.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1);
  }

  "test-unsigned-comparators-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-unsigned-comparators-0.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1);
  }

  "test-extid-axiom.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-extid-axiom.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1);
  }

  "test-hyperproperty-5.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-hyperproperty-5.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Trace select can only be applied on an identifier"))
    }
  }

  "syntax-error-input-assign-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/syntax-error-input-assign-1.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("is a readonly entity and cannot be assigned to"))
    }
  }

  "syntax-error-input-assign-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/syntax-error-input-assign-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("is a readonly entity and cannot be assigned to"))
    }
  }
  
  "test-func-import-5.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-func-import-5.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case e : Utils.ParserError => assert(e.msg.contains("Redeclaration error"))
    }
  }

  "test-func-import-6.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-func-import-6.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case e : Utils.ParserError  => assert(e.msg.contains("Trying to import from a module that does not"))
    }
  }

  "test-func-import-7.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-func-import-7.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
        case e : Utils.ParserError => assert(e.msg.contains("Trying to import from the same module"))
    }
  }

  "test-const-import-5.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-const-import-5.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case e : Utils.ParserError => assert(e.msg.contains("Trying to import from a module that does not"))
    }
  }

  "test-const-import-6.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-const-import-6.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case e : Utils.ParserError => assert(e.msg.contains("Trying to import from the same module"))
    }
  }

  "test-def-import-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-def-import-0.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-def-import-1.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-def-import-1.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.exists(p => p._1.contains("Redeclaration")))
    }
  }

  "test-def-import-2.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-def-import-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case e : Utils.ParserError => assert(e.msg.contains("Trying to import from a module that does not"))
    }
  }

  "test-instance-procedure-call-6.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-instance-procedure-call-6.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.exists(p => p._1.contains("does not exist in the context. Double check")))
    }
  }

  "test-instance-procedure-call-2.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-instance-procedure-call-2.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "issue-187a.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfig("test/issue-187a.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-invalid-cmd-param.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-invalid-cmd-param.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError => assert (true)
      case _ : Throwable => assert (false)
    }
  }

  "test-invalid-cmd-param-2.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-invalid-cmd-param-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError => assert (true)
      case _: Throwable => assert (false)
    }
  }

  "test-invalid-verif-var.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-invalid-verif-var.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "test-oracle-function-2.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-oracle-function-2.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "test-oracle-function-3.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-oracle-function-3.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "test-oracle-function-4.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-oracle-function-4.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "test-macro-5-fails.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-macro-5-fails.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.exists(p => p._1.contains("Macro does not exist")))
    }
  }
  "test-macro-6-fails.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-macro-6-fails.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.exists(p => p._1.contains("Primed assignments are not allowed in procedural code")))
    }
  }
  "test-macro-7-fails.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-macro-7-fails.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.exists(p => p._1.contains("Macro calls are not allowed in macro declarations")))
    }
  }
  "test-macro-8-fails.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-macro-8-fails.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.exists(p => p._1.contains("Macro calls are not allowed in the next block")))
    }
  }
  "test-group-parse-0.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-group-parse-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "test-group-parse-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfigWithMSA("test/test-group-parse-1.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-no-control-block.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(ConfigCons.createConfigWithMSA("test/test-no-control-block.ucl"), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "parser_error_1.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-group-parse-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "parser_error_2.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-group-parse-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "parser_error_3.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-group-parse-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "parser_error_4.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-group-parse-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "parser_error_5.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-group-parse-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList => assert (true)
      case _: Throwable => assert (false)
    }
  }
  "parser_error_6.ucl" should "not parse successfully" in {
    try {
      val fileModules = UclidMain.compile(ConfigCons.createConfig("test/test-group-parse-0.ucl"), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.TypeErrorList => assert (true)
      case _: Throwable => assert (false)
    }
  }
}
