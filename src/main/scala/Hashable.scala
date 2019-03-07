package uclid

import scala.util.hashing.{MurmurHash3 => MH}
import java.security.{MessageDigest => MD}
import java.nio.ByteBuffer

trait Hashable {
  /** These are unique ids for each abstract base class that are used
   *  to start off the hashing.
   */
  val hashBaseId : Int
  val hashId : Int
  val md5hashCode : Array[Byte]

  def md5 : MD = MD.getInstance("MD5")

  def intToBytes(i : Int) : Array[Byte] = {
    ByteBuffer.allocate(4).putInt(i).array()
  }

  def computeMD5Hash() : Array[Byte] = computeMD5Hash(List.empty[Any])
  def computeMD5Hash(args : Any*) : Array[Byte] = {
    md5.reset()
    md5.update(intToBytes(hashBaseId))
    md5.update(intToBytes(hashId))
    def computeMD5HashR(a : Any) : Unit = {
      a match {
        case integer : Int => md5.update(intToBytes(integer))
        case str     : String => md5.update(str.getBytes("UTF-8"))
        case bigint  : BigInt => md5.update(bigint.toByteArray)
        case bool    : Boolean => md5.update(if (bool) intToBytes(1) else intToBytes(0))
        case tuple2  : (Any, Any) => { computeMD5HashR(tuple2._1); computeMD5HashR(tuple2._2); }
        case tuple3  : (Any, Any, Any) => { computeMD5HashR(tuple3._1); computeMD5HashR(tuple3._2); computeMD5HashR(tuple3._3) }
        case lista   : List[Any] => lista.foreach(e => computeMD5HashR(e))
        case hash    : Hashable => md5.update(hash.md5hashCode)
        case _ => throw new Utils.RuntimeError("Should not get here; Missing case!")
      }
    }
    args.foreach(arg => computeMD5HashR(arg))
    md5.digest()
  }

  def mix(a : Int, b : Int) = MH.mix(a, b)
  def mix(a : Int, bs : List[Any]) : Int = bs.foldLeft(a)((acc, h) => mix(acc, h.hashCode))
  def mix2(a : Int, bs : List[(Any, Any)]) : Int = bs.foldLeft(mix(hashBaseValue, a.hashCode))((acc, b) => mix(acc, mix(b._1.hashCode, b._2.hashCode)))
  def finalize(h : Int, l : Int) : Int = MH.finalizeHash(h, l)
  def hashBaseValue = mix(hashBaseId, hashId)

  def computeHash = finalize(hashBaseValue, 1)
  def computeHash(args : Any*) : Int = {
    val start = hashBaseValue

    def computeHashR(acc : Int, a : Any) : Int = {
      a match {
        case integer : Int => mix(acc, integer)
        case str : String => mix(acc, str.hashCode())
        case bigint : BigInt => mix(acc, bigint.toInt)
        case bool : Boolean => mix(acc, (if (bool) 1 else 0))
        case tuplea : (Any, Any) => computeHashR(computeHashR(acc, tuplea._1), tuplea._2)
        case tupleb : (Any, Any, Any) => computeHashR(computeHashR(computeHashR(acc, tupleb._1), tupleb._2), tupleb._3)
        case lista : List[Any] => lista.foldLeft(acc)((acc2, h) => computeHashR(acc2, h))
        case hash : Hashable => mix(acc, hash.hashCode())
        case any : Any => { UclidMain.println("test" + any.toString()); mix(acc, any.hashCode()) }
      }
    }

    val endHash = args.foldLeft(start)((acc, a) => computeHashR(acc, a))
    finalize(endHash, args.size)
  }

  override def equals(that : Any) : Boolean = { hashCode == that.hashCode && md5hashCode.sameElements(that.asInstanceOf[Hashable].md5hashCode) }
}