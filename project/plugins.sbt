name := "uclid"
version := "1.0"
scalaVersion := "2.11.1"
 
libraryDependencies ++= Seq(
 "org.scalatest" % "scalatest_2.11" % "2.2.0" % "test" withSources(),
 "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.1" withSources()
)
