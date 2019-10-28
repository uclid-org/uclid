package uclid.lang.modelcounts

object UMCMain {
  def checkModel(f: java.io.File) {
    val module = UMCParser.parseUMCModel(f)
    println(module.toString())
  }
}