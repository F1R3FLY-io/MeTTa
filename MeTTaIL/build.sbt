ThisBuild / name         := "MeTTaIL"
ThisBuild / version      := "0.1"
ThisBuild / scalaVersion := "3.4.1"

Global / excludeLintKeys += ThisBuild / name

// Add the fat jar (mettailparser.jar) from the target directory as an unmanaged dependency.
Compile / unmanagedJars += baseDirectory.value / "../target/mettailparser.jar"

// ScalaTest for unit testing
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.15" % Test

// sbt-assembly settings:
import sbtassembly.AssemblyPlugin.autoImport._

assembly / assemblyJarName := "mettail_assembly.jar"

assembly / assemblyMergeStrategy := {
  case "META-INF/MANIFEST.MF" => sbtassembly.MergeStrategy.discard
  case x                      => sbtassembly.MergeStrategy.first
}
