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

  def writeInput(str: String) {
    println("writing: " + str)
    inputChannel.write(ProcessInputString(str))
  }
  
  def finishInput() {
    println("finishing")
    inputChannel.write(ProcessInputDone)
  }

  val cmdLine = cmd::args
  val builder = new java.lang.ProcessBuilder(cmdLine.asJava)
  val process = builder.start()
  val stdin = process.getOutputStream()
  val stdout = process.getInputStream()

  val writerThread = new Thread(new Runnable {
    def run() {
      var done = false
      while (!done) {
        val msg = inputChannel.read
        msg match {
          case ProcessInputString(str) =>
            stdin.write(str.getBytes())
            stdin.flush()
          case ProcessInputDone =>
            stdin.close()
            done = true
        }
      }
    }
  })
  
  val readerThread = new Thread(new Runnable {
    def run() {
      val done = false
      while (!done) {
        val bytesAvailable = stdout.available()
        if (bytesAvailable > 0) {
          val bytes = Array.ofDim[Byte](bytesAvailable)
          stdout.read(bytes)
          val string = bytes.map(_.toChar).mkString
          print(string)
        }
      }
    }
  })
  
  def start() { 
    writerThread.start()
    readerThread.start()
  }
}

object InteractiveProcess
{
  def test()
  {
    val process = new InteractiveProcess("python", List.empty)
    process.start()
    process.writeInput("2+2\n")
    process.finishInput()
    while(process.writerThread.isAlive() && process.readerThread.isAlive()) {}
  }
}