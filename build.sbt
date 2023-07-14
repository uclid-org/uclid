name := "uclid"
version := "0.9.5"
maintainer := "spramod@cse.iitk.ac.in"
scalaVersion := "2.12.11"
 
scalacOptions += "-feature"
scalacOptions += "-unchecked"
scalacOptions += "-deprecation"

libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2" % "provided"
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3" % "provided"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2" withSources()
libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.2"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % "test"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.1"
libraryDependencies += "org.json4s" %% "json4s-jackson" % "4.0.3"

// do not require tests before building a fat JAR
test in assembly := {}


assemblyMergeStrategy in assembly := {
 case PathList("META-INF", _*) => MergeStrategy.discard
 case _                        => MergeStrategy.first
}
assemblyJarName in assembly := "uclid-fatjar-0.9.5.jar"
enablePlugins(JavaAppPackaging)
