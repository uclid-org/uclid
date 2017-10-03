
/**
 * @author rohitsinha
 * @author pramod
 * 
 * Utility functions for uclid.
 */
package uclid

import scala.util.parsing.input.Position

object Utils {
  def assert(b: Boolean, err: String) : Unit = {
    if (!b) { throw new AssertionError(err) }
  }
  def raiseParsingError(err: String, pos : Position, fileName : Option[String]) : Unit = {
    throw new ParserError(err, Some(pos), fileName)
  }
  def checkParsingError(b : Boolean, err: String, pos : Position, fileName : Option[String]) : Unit = {
    if (!b) { raiseParsingError(err, pos, fileName) }
  }
  def checkError(b : Boolean, err: String) : Unit = {
    if (!b) { throw new ParserError(err, None, None) }
  }
  class UnimplementedException (msg:String=null, cause:Throwable=null) extends java.lang.UnsupportedOperationException (msg, cause) {}
  class RuntimeError (msg:String = null, cause: Throwable=null) extends java.lang.RuntimeException(msg, cause) {}
  class AssertionError(msg:String = null, cause: Throwable=null) extends java.lang.RuntimeException(msg, cause) {}
  class ParserError(msg:String, val pos : Option[Position], val filename: Option[String], cause:Throwable=null) extends java.lang.RuntimeException(msg, cause) {}
  
  def existsOnce(a: List[lang.Identifier], b: lang.Identifier) : Boolean = existsNTimes(a,b,1)
  def existsNone(a: List[lang.Identifier], b: lang.Identifier) : Boolean = existsNTimes(a,b,0)
  def existsNTimes(a: List[lang.Identifier], b: lang.Identifier, n: Int) : Boolean = 
    a.count { x => x.name == b.name } == n
  
  def allUnique(a: List[lang.Identifier]) : Boolean = a.distinct.size == a.size
  
  def join(things: List[String], sep: String) = {
    things match {
      case Nil => ""
      case head :: tail => head + tail.foldLeft(""){(acc,i) => acc + sep + i} 
    }
  }
}

class Memo[I, O](f : I => O) {
  var memoHashMap = new scala.collection.mutable.HashMap[I, O]
  val fun = f
  def apply(key : I) : O = {
    memoHashMap.get(key) match {
      case Some(v) => v
      case None    => {
        val item = fun(key)
        memoHashMap.put(key, item)
        item
      }
    }
  }
}
