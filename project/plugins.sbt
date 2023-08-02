// this adds the native packager.
addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.3.25")
// this helps create eclipse projects.
addSbtPlugin("com.typesafe.sbteclipse" % "sbteclipse-plugin" % "5.2.4")
// this helps with code coverage
addSbtPlugin("org.scoverage" % "sbt-scoverage" % "1.6.1")
// adds the "assembly" command to build a fat JAR
addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.10")

