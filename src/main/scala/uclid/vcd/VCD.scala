// Adapted from github.com/ucb-bar/treadle
// Redistributed with modifications per original license, reproduced below

/*

Chisel3 license terms

Copyright (c) 2014 - 2016 The Regents of the University of
California (Regents). All Rights Reserved.  Redistribution and use in
source and binary forms, with or without modification, are permitted
provided that the following conditions are met:
    * Redistributions of source code must retain the above
copyright notice, this list of conditions and the following
two paragraphs of disclaimer.
  * Redistributions in binary form must reproduce the above
copyright notice, this list of conditions and the following
two paragraphs of disclaimer in the documentation and/or other materials
provided with the distribution.
  * Neither the name of the Regents nor the names of its contributors
may be used to endorse or promote products derived from this
software without specific prior written permission.
  IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF
  REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
    REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF
    ANY, PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION
TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
MODIFICATIONS.

*/

package uclid.vcd

import com.typesafe.scalalogging.LazyLogging

import java.io.PrintWriter
import java.text.SimpleDateFormat

import collection._
import java.util.{Date, TimeZone}

import scala.collection.mutable.ArrayBuffer
import scala.util.matching.Regex

object VCD extends LazyLogging {
  val Version = "0.2"

  val DateDeclaration: String = "$date"
  val VersionDeclaration: String = "$version"
  val CommentDeclaration: String = "$comment"
  val TimeScaleDeclaration: String = "$timescale"
  val ScopeDeclaration: String = "$scope"
  val VarDeclaration: String = "$var"
  val UpScopeDeclaration: String = "$upscope"
  val EndDefinitionsDeclaration: String = "$enddefinitions"
  val DumpVarsDeclaration: String = "$dumpvars"
  val End: String = "$end"

  val idChars: Seq[String] = (33 to 126).map { asciiValue => asciiValue.toChar.toString }
  val numberOfIdChars: Int = idChars.length

  // A number of regular expressions to parse vcd lines
  val SectionHeader: Regex = """^\$([^\$]+) *$""".r
  val EndSection: Regex = """^\$end *$""".r

  val ScopedModule: Regex = """\s*(?i)(\S+)\s+(\S+)\s*""".r
  val JustScoped: Regex = """\s*(\S+)\s*""".r

  val VarSpec: Regex = """\s*(\w+)\s+(\d+)\s+(\S+)\s+([\S ]+)\s*""".r
  val ValueChangeScalar: Regex = """\s*(\d+)(\S+)\s*""".r
  val ValueChangeVector: Regex = """\s*([rbh])([0-9\.]+)\s*""".r
  val ValueChangeVectorX: Regex = """\s*([rbh]).*x.*\s*""".r
  val TimeStamp: Regex = """\s*#(\d+)\s*""".r

  def apply(
      moduleName: String,
      timeScale: String = "1ns",
      comment: String = "",
      showUnderscoredNames: Boolean = false
  ): VCD = {

    val tz = TimeZone.getTimeZone("UTC")
    val df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mmZ")
    df.setTimeZone(tz)
    val nowAsISO = df.format(new Date())

    new VCD(
      nowAsISO,
      VCD.Version,
      comment,
      timeScale,
      moduleName,
      ignoreUnderscoredNames = ! showUnderscoredNames
    )
  }

  class WordIterator(fileName: String) extends Iterator[String] {
    val lines: Iterator[String] = io.Source.fromFile(fileName).getLines()
    var currentLineNumber = 0
    var currentLine: Iterator[String] = Iterator.empty
    var _hasNext = false
    def hasNext: Boolean = _hasNext
    var nextWord = ""

    override def next(): String = {
      val lastWord = nextWord
      loadNextWord()
      lastWord
    }

    loadNextWord()

    def loadNextWord(): Unit = {
      if(currentLine.hasNext) {
        nextWord = currentLine.next()
        if(nextWord.isEmpty) {
          loadNextWord()
        }
        else {
          _hasNext = true
        }
      }
      else {
        if(lines.hasNext) {
          currentLineNumber += 1
          currentLine = lines.next().trim.split("""\s+""").iterator
          loadNextWord()
        }
        else {
          _hasNext = false
          nextWord = ""
        }
      }
    }
  }

}

/**
  * Accumulates changes to wires in a running circuit.  If a wire is changed that it doesn't know about it
  * will add it to the list.  Only actual changed values will be seen in final output.  This version only supports
  * a single top level scope because right now that is what the firrtl-engine supports.  It probably is not too
  * too hard to add, all wires are initialized to 'x' in this version.
 *
  * @param date date file was created
  * @param version this software version, but I suppose this could be a DUT version
  * @param comment could be a comment
  * @param timeScale seems to be more text (I like to work in picoseconds)
  * @param scope Not really used here except as the name of the top level module
  */
case class VCD(
           date: String,
           version: String,
           comment: String,
           timeScale: String,
           scope: String,
           ignoreUnderscoredNames: Boolean
         ) extends LazyLogging {
  var currentIdNumber = 0
  var timeStamp = 0L
  val lastValues = new mutable.HashMap[String, Change]
  val valuesAtTime = new mutable.HashMap[Long, mutable.HashSet[Change]]
  val initialValues = new mutable.HashSet[Change]
  var scopeRoot = Scope(scope)
  val wires = new mutable.HashMap[String, Wire]
  var aliasedWires: mutable.HashMap[String, mutable.HashSet[Wire]] =
    new mutable.HashMap[String, mutable.HashSet[Wire]] {
    override def default(key: String): mutable.HashSet[Wire] = {
      this(key) = new mutable.HashSet[Wire]
      this(key)
    }
  }
  val wiresToIgnore = new mutable.HashSet[String]

  def events: Array[Long] = valuesAtTime.keys.toArray.sorted

  def info: String = {
    val infoLines = Seq(
      "vcd" -> version,
      "timescale" -> timeScale,
      "comment" -> comment,
      "date" -> date,
      "unique wires" -> wires.size.toString,
      "events" -> valuesAtTime.size.toString
    )
    val maxLabel: Int = infoLines.filter(_._2.trim.nonEmpty).map(_._1.length).max
    infoLines.flatMap { case (label, value) =>
      if(value.trim.nonEmpty) {
        Some(label + ":" + (" " * (4 + maxLabel - label.length)) + value)
      }
      else {
        None
      }
    }.mkString("\n")
  }

  def getIdString(value: Int = currentIdNumber, currentString: String = ""): String = {
    val index = value % VCD.numberOfIdChars
    val newValue = value / VCD.numberOfIdChars

    if(newValue <= 0) {
      VCD.idChars(index) + currentString
    }
    else {
      getIdString(newValue, VCD.idChars(index) + currentString)
    }
  }

  def addWire(wireName: String, width: Int): Unit = {
    def addWireToScope(wire: Wire, scope: Scope): Unit = {
      if(!scope.wires.contains(wire)) scope.wires += wire
    }

    def findScope(currentScope: Scope, scopeList: List[String]): Option[Scope] = {
      scopeList match {
        case name :: tail =>
          currentScope.subScopes.find(_.name == name) match {
            case Some(subScope) =>
              findScope(subScope, tail)
            case None =>
              val newScope = Scope(name)
              currentScope.subScopes += newScope
              findScope(newScope, tail)
          }
        case Nil =>
          Some(currentScope)
      }
    }

    wireName.split("""\.""").reverse.toList match {
      case name :: reversedScopes =>
        findScope(scopeRoot, reversedScopes.reverse) match {
          case Some(subScope) =>
            if(! wires.contains(wireName)) {
              val newWire = Wire(name, getIdString(), width)
              incrementId()
              addWireToScope(newWire, subScope)
              wires(wireName) = newWire
            }
          case None =>
            logger.error(s"Could not find scope for $wireName")
        }
      case Nil =>
        logger.error(s"Can not parse found wire $wireName")
    }
  }

  /**
    * reports whether value is a change from the last recorded value for wireName
    * @param wireName name of wire
    * @param value    value of wire
    * @return
    */
  def isNewValue(wireName: String, value: BigInt): Boolean = {
    lastValues.get(wireName) match {
      case Some(lastValue) =>
        if(lastValue.value != value) {
          true
        } else {
          false
        }
      case _ =>
        true
    }
  }

  def isTempWire(wireName: String): Boolean = {
    wireName.split("""\.""").last.startsWith("_T_") || wireName.contains("/")
  }

  /**
    * Change wire value if it is different that its the last recorded value
    * @param wireName name of wire
    * @param value    value of wire
    * @param width    width of wire (needed for header info)
    * @return         false if the value is not different
    */
  def wireChanged(wireName: String, value: BigInt, width: Int = 1): Boolean = {
    if(wiresToIgnore.contains(wireName)) return false
    if(ignoreUnderscoredNames && isTempWire(wireName)) {
      wiresToIgnore += wireName
      return false
    }

    def updateInfo(): Unit = {
      val wire = wires(wireName)
      val change = Change(wire, value)
      lastValues(wireName) = change

      if(timeStamp < 0) {
        initialValues += change
      }
      else {
        val changeSet = valuesAtTime.getOrElseUpdate(timeStamp, new mutable.HashSet[Change])
        changeSet += change
      }
    }

    // logger.info(f"vcd-change time $timeStamp%6d value $value%6d wire $wireName")
    if(! wires.contains(wireName)) {
      addWire(wireName, width: Int)
    }
    if(isNewValue(wireName, value)) {
      updateInfo()
      true
    }
    else {
      false
    }
  }

  def incrementTime(increment: Long = 1L): Unit = {
    timeStamp += increment
  }

  def setTime(time: Long): Unit = {
    timeStamp = time
  }

  def wiresFor(change: Change): Set[Wire] = {
    aliasedWires(change.wire.id) + change.wire
  }

  def incrementId(): Unit = currentIdNumber += 1

  def serializeChanges: String = {
    val s = new StringBuilder

    valuesAtTime.keys.toList.sorted.foreach { time =>
      valuesAtTime.get(time).foreach { changeSet =>
        s.append(s"#$time\n")
        changeSet.foreach { change =>
          s.append(change.serialize + "\n")
        }
      }
    }
    s.toString()
  }

  def serializeStartup: String = {
    initialValues.map { _.serialize }.mkString("\n")
  }

  def serialize: String = {
    val buffer = new StringBuilder

    buffer.append(VCD.DateDeclaration + "\n")
    buffer.append(date + "\n")
    buffer.append(VCD.End + "\n")
    buffer.append(VCD.VersionDeclaration + "\n")
    buffer.append(version + "\n")
    buffer.append(VCD.End + "\n")
    buffer.append(VCD.CommentDeclaration + "\n")
    buffer.append(comment + "\n")
    buffer.append(VCD.End + "\n")
    buffer.append(s"${VCD.TimeScaleDeclaration} $timeScale  ${VCD.End}\n")

    def doScope(scope: Scope, depth: Int = 0): Unit = {
      def indent(inc: Int = 0): String = " " * ( depth + inc )
      buffer.append(s"${indent()}${VCD.ScopeDeclaration} module ${scope.name} ${VCD.End}\n")
      scope.wires.foreach { wire => buffer.append(indent(1) + wire.toString + "\n") }
      scope.subScopes.foreach { subScope => doScope(subScope, depth + 2) }
      buffer.append(s"${indent()}${VCD.UpScopeDeclaration} ${VCD.End}\n")
    }

    doScope(scopeRoot)
    buffer.append(s"${VCD.EndDefinitionsDeclaration} ${VCD.End}\n")
    if(initialValues.nonEmpty) {
      buffer.append(s"${VCD.DumpVarsDeclaration}\n")
      buffer.append(serializeStartup + s"\n${VCD.End}\n")
    }
    buffer.append(serializeChanges)
    buffer.toString()
  }


  def write(fileName: String): Unit = {
    val writer = new PrintWriter(fileName)
    writer.write(serialize)
    writer.close()
  }
}

case class Wire(name: String, id: String, width: Int, path: Array[String] = Array.empty) {
  def fullName: String = (path ++ Seq(name)).mkString(".")
  override def toString: String = {
    s"${VCD.VarDeclaration} wire $width $id $name ${VCD.End}"
  }
}

/**
  * holds the information about
 *
  * @param wire wire who's status is being monitored
  * @param value the value this wire now has
  */
case class Change(wire: Wire, value: BigInt) {
  def serialize: String = {
    if(wire.width == 1) {
      s"${if(value == 0) 0 else 1}${wire.id}"
    }
    else {
      "b" +
        (wire.width - 1 to 0 by -1).map { index => if (value.testBit(index)) "1" else "0" }.mkString("") +
        s" ${wire.id}"
    }
  }
  def serializeUninitialized: String = {
    s"b${"x" * wire.width} ${wire.id}"
  }
}

case class Scope(name: String, parent: Option[Scope] = None) {
  val subScopes = new ArrayBuffer[Scope]()
  val wires = new ArrayBuffer[Wire]()
  def addScope(subScopeName: String): Unit = {
    subScopes += Scope(subScopeName)
  }
}
