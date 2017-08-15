name := "uclid"
version := "1.0"
scalaVersion := "2.11.1"
 
libraryDependencies ++= Seq(
 "org.scalatest" % "scalatest_2.11" % "2.2.0" % "test" withSources(),
 "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.1" withSources()
)


// addSbtPlugin("com.artima.supersafe" %% "supersafe" % "1.1.2")
// http://repo.artima.com/releases/com/artima/supersafe/supersafe_2.11_0.13/1.1.2/supersafe-1.1.2.pom
// http://repo.artima.com/releases/com/artima/supersafe/supersafe_2.11.1/1.1.2/supersafe_2.11.1-1.1.2.pom