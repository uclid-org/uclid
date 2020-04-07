package uclid.lang.modelcounts

import uclid.UclidMain
import uclid.{lang => l}

object UMCMain {
  def checkModel(f: java.io.File, config: UclidMain.Config) {
    val module = UMCParser.parseUMCModel(f)
    println("Managed to parse module: " + module.id.toString())
  }
}
