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
 * Interactively run a process.
 *
 */

package uclid

import scala.concurrent.Channel
import scala.collection.JavaConverters._

class InteractiveProcess(cmd: String, args: List[String]) {
  abstract sealed class ProcessInput
  case object ProcessInputDone extends ProcessInput
  case class ProcessInputString(str: String) extends ProcessInput

  abstract sealed class ProcessOutput
  case class ProcessStdOut(str: String) extends ProcessOutput
  case class ProcessStdErr(std: String) extends ProcessOutput
  case object ProcessStdOutClose extends ProcessOutput
  case object ProcessStdErrClose extends ProcessOutput

  val inputChannel = new Channel[ProcessInput]()
  val outputChannel = new Channel[ProcessOutput]()

}

object InteractiveProcess
{
  def isAlive(process : Process) : Boolean = {
    try {
      process.exitValue()
      return false
    } catch {
      case e : IllegalThreadStateException =>
        return true
    }
  }

  val formula = List(
    "(declare-fun x () Int)",
    "(declare-fun y () Int)",
    "(assert (and (distinct x 0) true))",
    "(assert (and (distinct y 0) true))",
    "(assert (and (distinct y 1) true))",
    "(assert (and (distinct x 1) true))",
    "(assert (= (+ x y) (* x y)))",
    "(check-sat)"
  )

  def stringToBytes(str: String) = {
    str.map(_.toChar).toCharArray().map(_.toByte)
  }
  def test()
  {
    val builder = new ProcessBuilder("/usr/bin/z3", "-in", "-smt2")
    builder.redirectErrorStream(true)
    val process = builder.start()
    val out = process.getInputStream()
    val in = process.getOutputStream()

    formula.foreach{ (l) => {
      in.write(stringToBytes(l + "\n"))
    }}
    in.flush()
    while (isAlive(process)) {
      val numAvail = out.available()
      if (numAvail > 0) {
        val bytes = Array.ofDim[Byte](numAvail)
        out.read(bytes, 0, numAvail)
        val string = new String(bytes)
        print(string)
        if (string == "sat\n") {
          in.write(stringToBytes("(get-model)\n"))
          in.flush()
          in.close()
        }
      } else {
        Thread.sleep(0)
      }
    }
  }
}