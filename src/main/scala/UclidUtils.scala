
/**
 * @author rohitsinha
 */
object UclidUtils {
    def assert(b: Boolean, err: String) : Unit = {
      if (!b) { println("ERROR: " + err); System.exit(0); } //throw new Exception(err); }
    }
    
    def existsOnce(a: List[UclIdentifier], b: UclIdentifier) : Boolean = 
      a.count { x => x.value == b.value } == 1
    
    def hasDuplicates(a: List[UclIdentifier]) : Boolean = a.distinct.size == a.size
}