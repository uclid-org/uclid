name := "uclid"
version := "0.9.5"
maintainer := "spramod@cse.iitk.ac.in"
scalaVersion := "2.12.11"
 
scalacOptions += "-feature"
scalacOptions += "-unchecked"
scalacOptions += "-deprecation"

libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2"
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2" withSources()
libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.2"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % "test"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.1"
libraryDependencies += "org.json4s" %% "json4s-jackson" % "4.0.3"

// Fork the JVM for run/test so that javaOptions take effect. The java.library.path
// setting is needed for Z3 JNI native library loading (libz3java). While the setup
// scripts (setup-z3-linux.sh, etc.) set LD_LIBRARY_PATH for shell use, java.library.path
// must be set at JVM startup to locate native libraries when running via sbt.
fork in run := true
javaOptions in run += s"-Djava.library.path=${baseDirectory.value}/z3/bin"

fork in Test := true
javaOptions in Test += s"-Djava.library.path=${baseDirectory.value}/z3/bin"

// do not require tests before building a fat JAR
test in assembly := {}

enablePlugins(JavaAppPackaging)
