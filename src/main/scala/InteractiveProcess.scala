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

import scala.concurrent.SyncChannel
import scala.collection.JavaConverters._

class InteractiveProcess(cmd: String, args: List[String]) {
  // create the process.
  val cmdLine = (cmd :: args).asJava
  val builder = new ProcessBuilder(cmdLine)
  builder.redirectErrorStream(true)
  val process = builder.start() 
  val out = process.getInputStream()
  val in = process.getOutputStream()
  var exitValue : Option[Int] = None

  // channels for input and output.
  val inputChannel = new SyncChannel[Option[String]]()
  val outputChannel = new SyncChannel[Option[String]]()

  // Is this the best way of telling if a process is alive?
  def isAlive() : Boolean = {
    try {
      exitValue = Some(process.exitValue())
      return false
    } catch {
      case e : IllegalThreadStateException =>
        return true
    }
  }

  // Some helper functions.
  def stringToBytes(str: String) = {
    str.map(_.toChar).toCharArray().map(_.toByte)
  }
  def bytesToString(bytes: Array[Byte]) = new String(bytes)

  
  // Write to the process's input stream. 
  def writeInput(str: String) {
    in.write(stringToBytes(str))
    in.flush()
  }
  // Close stdin, this may cause the process to exit.
  def finishInput() {
    in.flush()
    in.close()
  }
  // Read from the process's output stream.
  def readOutput() : Option[String] = {
    var done = false
    while (!done) {
      if (!isAlive()) {
        done = true
      } else {
        Thread.sleep(5)
        val numAvail = out.available()
        if (numAvail == 0) {
          Thread.sleep(5)
        } else {
          val bytes = Array.ofDim[Byte](numAvail)
          val numRead = out.read(bytes, 0, numAvail)
          val string = bytesToString ({ 
            if (numRead == numAvail) {
              bytes              
            } else {
              bytes.slice(0, numRead)
            }
          })
          return Some(string)
        }
      }
    }
    return None
  }
  // Kill the process.
  def kill() {
    process.destroy()
  }
}