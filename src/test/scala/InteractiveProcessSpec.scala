/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017. The Regents of the University of California (Regents).
 * All Rights Reserved.
 *
 * Permission to use, copy, modify, and distribute this software
 * and its documentation for educational, research, and not-for-profit purposes,
 * without fee and without a signed licensing agreement, is hereby granted,
 * provided that the above copyright notice, this paragraph and the following two
 * paragraphs appear in all copies, modifications, and distributions.
 *
 * Contact The Office of Technology Licensing, UC Berkeley, 2150 Shattuck Avenue,
 * Suite 510, Berkeley, CA 94720-1620, (510) 643-7201, otl@berkeley.edu,
 * http://ipira.berkeley.edu/industry-info for commercial licensing opportunities.
 *
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
 * INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING OUT OF
 * THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS
 * PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
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
  
  it should "pass the sanity check" in {
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