package uclid.lang

import scala.annotation.tailrec
import scala.collection.JavaConverters.asScalaSetConverter

/** This file was copied from a the firrtl source code.
 */
class NodeCount private (node: ASTNode) {

  // Counts the number of unique objects in a UCLID graph
  // There is no IdentityHashSet
  private val identityMap = new java.util.IdentityHashMap[Any, Boolean]()
  // This is a strict subset of the keys of identityMap
  private val regularSet = new collection.mutable.HashSet[Any]

  @tailrec
  private final def rec(xs: List[Any]): Unit =
    if (xs.isEmpty) {} else {
      val node = xs.head
      require(
        node.isInstanceOf[Product] || !node.isInstanceOf[ASTNode],
        "Unexpected ASTNode that does not implement Product!"
      )
      val moreToVisit =
        if (identityMap.containsKey(node)) List.empty
        else { // Haven't seen yet
          identityMap.put(node, true)
          regularSet += node
          node match { // FirrtlNodes are Products
            case p: Product       => p.productIterator
            case i: Iterable[Any] => i
            case _ => List.empty
          }
        }
      rec(moreToVisit ++: xs.tail)
    }
  rec(List(node))

  /** Number of nodes that are referentially unique
   *
   * !(a eq b)
   */
  def unique: Long = identityMap.size

  /** Number of nodes that are different
   *
   * !(a == b)
   */
  def nonequivalent: Long = regularSet.size

  /** Number of nodes in this NodeCount that are NOT present in that NodeCount */
  def uniqueFrom(that: NodeCount): Long =
    this.identityMap.keySet.asScala.count(!that.identityMap.containsKey(_))
}

object NodeCount {
  def apply(node: ASTNode) = new NodeCount(node)
}