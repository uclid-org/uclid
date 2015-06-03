
/**
 * @author rohitsinha
 */
object UclidUtils {
    def assert(b: Boolean, err: String) : Unit = {
      if (!b) { println("ERROR: " + err); System.exit(0); } //throw new Exception(err); }
  }
}