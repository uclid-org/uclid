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
 * Author: Pramod Subramanyan
 *
 * UCLID Parser/Typechecker tests.
 *
 */

package uclid
package test

import org.scalatest.FlatSpec

class InteractiveProcessSpec extends FlatSpec {
  behavior of "InteractiveProcess"

  ignore should "pass the sanity check" in {
    val formula = List(
      "(declare-fun x () Int)\n",
      "(declare-fun y () Int)\n",
      "(assert (and (distinct x 0) true))\n",
      "(assert (and (distinct y 0) true))\n",
      "(assert (and (distinct y 1) true))\n",
      "(assert (and (distinct x 1) true))\n",
      "(assert (= (+ x y) (* x y)))\n",
      "(check-sat)\n"
    )

    val interactive = new InteractiveProcess("/usr/bin/z3", List("-in", "-smt2"))
    formula.foreach(l => interactive.writeInput(l))
    val satResult = interactive.readOutput()
    assert (satResult == Some("sat\n"))
    interactive.writeInput("(get-model)\n")
    val modelResult = interactive.readOutput()
    assert (modelResult.isDefined)
    interactive.finishInput()
    val finalOutput = interactive.readOutput()
    assert (finalOutput.isEmpty)
  }
}
