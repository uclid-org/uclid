scalacOptions += "-feature"
scalacOptions += "-unchecked"
scalacOptions += "-deprecation"

resolvers += "Artima Maven Repository" at "http://repo.artima.com/releases"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6" withSources()
libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"


enablePlugins(JavaAppPackaging)

