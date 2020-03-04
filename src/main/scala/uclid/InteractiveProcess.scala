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
 * Interactively run a process.
 *
 */

package uclid

import scala.concurrent.SyncChannel
import scala.collection.JavaConverters._
import com.typesafe.scalalogging.Logger

class InteractiveProcess(args: List[String], saveInput: Boolean=false) {
  val logger = Logger(classOf[InteractiveProcess])

  // create the process.
  val cmdLine = (args).asJava
  val builder = new ProcessBuilder(cmdLine)
  builder.redirectErrorStream(true)
  val process = builder.start()
  val out = process.getInputStream()
  val in = process.getOutputStream()
  var exitValue : Option[Int] = None

  // stores what we've written to the interactive process so far
  var inputString = ""
  override def toString() = inputString

  // channels for input and output.
  val inputChannel = new SyncChannel[Option[String]]()
  val outputChannel = new SyncChannel[Option[String]]()

  // Is this the best way of telling if a process is alive?
  def isAlive() : Boolean = {
    process.isAlive()
  }

  // Some helper functions.
  def stringToBytes(str: String) = {
    str.map(_.toChar).toCharArray().map(_.toByte)
  }
  def bytesToString(bytes: Array[Byte]) = new String(bytes)


  // Write to the process's input stream.
  def writeInput(str: String) {
    logger.debug("-> {}", str)
    in.write(stringToBytes(str))
    if (saveInput) inputString += str + "\n"
  }
  // Close stdin, this may cause the process to exit.
  def finishInput() {
    in.flush()
    inputString = ""
    in.close()
  }
  // Read from the process's output stream.
  def readOutput() : Option[String] = {
    inputString = ""
    in.flush()
    var done = false
    while (!done) {
      if (!isAlive()) {
        done = true
        logger.debug("Process dead.")
      } else {
        Thread.sleep(15)
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
          logger.debug("<- {}", string)

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
