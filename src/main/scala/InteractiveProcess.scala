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
import scala.sys.process._
import java.io.{InputStream, OutputStream, PrintWriter}
import scala.io.Source

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
  var outputStreamsDone : Int = 0
  var finished = false
  val commandLine = cmd :: args
  val process = commandLine.run(
                  new ProcessIO(inputWriter, 
                                out => outputReader(out, false), 
                                out => outputReader(out, true)))



  def inputWriter(in: OutputStream) {
    val writer = new PrintWriter(in)
    var done = false
    while (!done) {
      val input = inputChannel.read
      input match {
        case ProcessInputString(str) =>
          writer.print(str)
          writer.flush()
        case ProcessInputDone =>
          done = true
      }
    }
    in.close()
  }

  def outputReader(out: InputStream, stderr : Boolean) {
    while (!finished) {
      val numBytes = out.available()
      if (numBytes > 0) {
        val bytes = Array.ofDim[Byte](numBytes)
        out.read(bytes)
        val string = (bytes.map(_.toChar)).mkString
        println(string)
      }
    }
  }

  def writeInput(str: String) {
    inputChannel.write(ProcessInputString(str))
  }
  
  def finishInput() {
    inputChannel.write(ProcessInputDone)
  }

  def getOutputLine() : Option[String] = {
    if (outputStreamsDone > 2) {
      None
    } else {
      val msg = outputChannel.read
      msg match {
        case ProcessStdOut(str) => Some(str)
        case ProcessStdErr(str) => Some(str)
        case ProcessStdOutClose | ProcessStdErrClose =>
          outputStreamsDone += 1
          getOutputLine()
      }
    }
  }
}

object InteractiveProcess
{
  def test()
  {
    val process = new InteractiveProcess("python", List.empty)
    process.writeInput("2+2\n")
  }
}