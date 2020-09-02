name := "uclid"
version := "0.9.5"
maintainer := "spramod@cse.iitk.ac.in"
scalaVersion := "2.13.3"
 
scalacOptions += "-feature"
scalacOptions += "-unchecked"
scalacOptions += "-deprecation"

libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2"
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2" withSources()
libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.2"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % "test"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.1"

enablePlugins(JavaAppPackaging)
