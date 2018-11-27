name := "uclid"
version := "0.9.5"
scalaVersion := "2.12.7"
 
scalacOptions += "-feature"
scalacOptions += "-unchecked"
scalacOptions += "-deprecation"

resolvers += "Artima Maven Repository" at "http://repo.artima.com/releases"

libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0"
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1" withSources()
libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.5"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.0"

enablePlugins(JavaAppPackaging)
