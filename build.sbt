name := "uclid"
version := "0.9.1"
scalaVersion := "2.12.0"
 
scalacOptions += "-feature"
scalacOptions += "-unchecked"
scalacOptions += "-deprecation"

resolvers += "Artima Maven Repository" at "http://repo.artima.com/releases"

libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.8.0"
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6" withSources()
libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.0"

enablePlugins(JavaAppPackaging)
