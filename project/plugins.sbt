name := "uclid"
version := "1.0"
scalaVersion := "2.12.0"
 
// this adds the native packager.
addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.3.1")
// this helps create eclipse projects.
addSbtPlugin("com.typesafe.sbteclipse" % "sbteclipse-plugin" % "5.2.3")
// this is for scalatest
addSbtPlugin("com.artima.supersafe" % "sbtplugin" % "1.1.2")
