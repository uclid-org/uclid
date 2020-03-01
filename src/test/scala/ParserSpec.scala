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

import org.scalatest.FlatSpec
import uclid.{lang => l}
import java.io.File

class ParserSpec extends FlatSpec {
  "test-type1.ucl" should "not parse successfully." in {
    try {
      val filename = "test/test-type1.ucl"
      val fileModules = UclidMain.compile(List(new File(filename)), lang.Identifier("main"))
      assert (fileModules.size == 2)
    }
    catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors(0)._1.contains("Redeclaration of identifier 'test'."))
    }
  }
  "test-typechecker-0.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-0.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-1.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-module-errors.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-6.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-3.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-4.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-recursion.ucl")), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
    }
  }
  "test-procedure-types-errors.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-procedure-types-errors.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-procedure-invocation-errors.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-syntax-errors-1.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-5.ucl")), lang.Identifier("main"))
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
     val fileModules = UclidMain.compile(List(new File("test/test-modules-2.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-procedure-checker-1.ucl")), lang.Identifier("main"))
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
  "test-mutual-recursion-error.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-mutual-recursion-error.ucl")), lang.Identifier("main"))
      // should never get here.
      assert (false);
    }
    catch {
      // this list has all the errors from parsing
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Recursion involving procedures")))
    }
  }
  "test-parsing-history-op-error.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-parsing-history-op-error.ucl")), lang.Identifier("main"))
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
  "test-typechecker-7.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-7.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-typechecker-8.ucl")), lang.Identifier("main"))
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
  "test-types-import-redecl.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-types-import-redecl.ucl")), lang.Identifier("main"))
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
    val fileModules = UclidMain.compile(List(new File("test/test-define-expand.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-procedure-inline-bv.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-procedure-inline-bv.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-procedure-postcondition-2.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-procedure-postcondition-2.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-define-recursive.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-define-recursive.ucl")), lang.Identifier("main"))
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
    val fileModules = UclidMain.compile(List(new File("test/nested_instances.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-nested-modules-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-nested-modules-1.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-nested-modules-2.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-nested-modules-2.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-block-var-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-block-var-0.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-modules-7.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-modules-7.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-block-var-renaming-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-block-var-renaming-1.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "test-multiple-writes.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-multiple-writes.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.forall(p => p._1.contains("Multiple updates to identifier(s)")))
    }
  }
  "test-cyclic-deps.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-cyclic-deps.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.forall(p => p._1.contains("Cyclical dependency involving variable(s)")))
    }
  }
  "test-procedure-next.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-procedure-next.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.forall(p => p._1.contains("Multiple updates to identifier(s): v")))
    }
  }
  "test-modules-3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-modules-3.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.forall(p => p._1.contains("Invalid module output")))
    }
  }
  "test-modules-4.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-modules-4.ucl")), lang.Identifier("main"))
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
      val fileModules = UclidMain.compile(List(new File("test/test-primed-variables-2.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Primed variables can't be referenced inside procedures")))
    }
  }
  "test-forloop-error-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-forloop-error-1.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("Invalid for loop range")))
    }
  }
  "test-string-0.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-string-0.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 1)
        assert (p.errors.exists(p => p._1.contains("expected type 'integer' but received type 'string'")))
    }
  }
  "test-string-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-string-1.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserError =>
        assert (p.msg.contains("'print' command expects a string literal as an argument"))
    }
  }
  "test-parser-nested-next-block.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-parser-nested-next-block.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Nested block statements are not allowed in a sequential environment"))
    }
  }
  "array-update-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/array-update-2.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("'rom' is a readonly entity and cannot be assigned to"))
    }
  }
  "test-string-2.ucl" should "parse successfully." in {
    UclidMain.enableStringOutput()
    UclidMain.clearStringOutput()
    val fileModules = UclidMain.compile(List(new File("test/test-string-2.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    val results = UclidMain.execute(instantiatedModules(0), UclidMain.Config())
    val stringOutput = UclidMain.stringOutput.toString().trim()
    assert (instantiatedModules.size == 1)
    assert (stringOutput == "hello, world!")
  }

  "test-hyperproperty-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-hyperproperty-0.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "longcomment.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/longcomment.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-array-record.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-array-record.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-array-record-1.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-array-record-1.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "recorderror.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/recorderror.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }
  "inputerror.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/inputerror.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1)
  }

  "test-hyperproperty-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-hyperproperty-1.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Trace select can only be used in a module-level expression"))
    }
  }

  /* This Test has been updated to not throw an error as trace selects are allowed inside procedural contexts. */

  // "test-hyperproperty-2.ucl" should "not parse successfully." in {
  //   try {
  //     val fileModules = UclidMain.compile(List(new File("test/test-hyperproperty-2.ucl")), lang.Identifier("main"))
  //     assert (false)
  //   } catch {
  //     case p : Utils.ParserErrorList =>
  //       assert (p.errors(0)._1.contains("Trace select can only be used in a verification expression"))
  //   }
  // }
  
  "test-hyperproperty-2.ucl" should "should parse successfully." in {
      val fileModules = UclidMain.compile(List(new File("test/test-hyperproperty-2.ucl")), lang.Identifier("main"))
      val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
      assert (instantiatedModules.size == 1)
  }
  "test-hyperproperty-3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-hyperproperty-3.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Trace select can only be used in a verification expression"))
    }
  }

  "proc_requires_3.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/proc_requires_3.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors.size == 2)
        assert (p.errors.forall(e => e._1.contains("Old operator can't be used in a requires expression")))
    }
  }
  "test-expression-suffix-function.ucl" should "parse successfully" in {
    val fileModules = UclidMain.compile(List(new File("test/test-expression-suffix-function.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1);
  }

  "test-unsigned-comparators-0.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-unsigned-comparators-0.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1);
  }

  "test-extid-axiom.ucl" should "parse successfully." in {
    val fileModules = UclidMain.compile(List(new File("test/test-extid-axiom.ucl")), lang.Identifier("main"))
    val instantiatedModules = UclidMain.instantiateModules(UclidMain.Config(), fileModules, lang.Identifier("main"))
    assert (instantiatedModules.size == 1);
  }

  "test-hyperproperty-5.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/test-hyperproperty-5.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("Trace select can only be applied on an identifier"))
    }
  }

  "syntax-error-input-assign-1.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/syntax-error-input-assign-1.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("is a readonly entity and cannot be assigned to"))
    }
  }

  "syntax-error-input-assign-2.ucl" should "not parse successfully." in {
    try {
      val fileModules = UclidMain.compile(List(new File("test/syntax-error-input-assign-2.ucl")), lang.Identifier("main"))
      assert (false)
    } catch {
      case p : Utils.ParserErrorList =>
        assert (p.errors(0)._1.contains("is a readonly entity and cannot be assigned to"))
    }
  }
}
