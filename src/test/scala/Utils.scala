package uclid
package test

import java.io.File

package object ConfigCons {
  /** Helper that returns a Config with the given filename.
   *
   *  @param filename The name of the file being tested in the Config.
   */
  def createConfig(filename: String): UclidMain.Config = {
    UclidMain.Config(files=List(new File(filename)))
  }

  /** Helper that returns a Config with the given filename 
   *  and with modSetAnalysis option on.
   *
   *  @param filename The name of the file being tested in the Config.
   */
  def createConfigWithMSA(filename: String): UclidMain.Config = {
  	UclidMain.Config(files=List(new File(filename)), modSetAnalysis=true)
  }
}