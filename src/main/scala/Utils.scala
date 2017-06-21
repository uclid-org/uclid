
/**
 * @author rohitsinha
 */
package uclid {
  
  object Utils {
      def assert(b: Boolean, err: String) : Unit = {
        if (!b) { println("ERROR: " + err); System.exit(0); } //throw new Exception(err); }
      }
      
      class UnimplementedException (msg:String=null, cause:Throwable=null) extends java.lang.UnsupportedOperationException (msg, cause) {}
      class RuntimeError (msg:String = null, cause: Throwable=null) extends java.lang.RuntimeException(msg, cause) {}
      
      def existsOnce(a: List[lang.Identifier], b: lang.Identifier) : Boolean = existsNTimes(a,b,1)
      def existsNone(a: List[lang.Identifier], b: lang.Identifier) : Boolean = existsNTimes(a,b,0)
      def existsNTimes(a: List[lang.Identifier], b: lang.Identifier, n: Int) : Boolean = 
        a.count { x => x.value == b.value } == n
      
      def allUnique(a: List[lang.Identifier]) : Boolean = a.distinct.size == a.size
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
}