package io.f1r3fly.mettail

import java.io.File
import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

object Main {
  def main(args: Array[String]): Unit = {
    if (args.isEmpty) sys.error("Usage: Main <path-to-module> [--hypercube]")

    // Detect --hypercube flag anywhere in the arguments
    val hypercubeEnabled = args.contains("--hypercube")

    // Extract the module path (first non-flag argument)
    val moduleArgs = args.filterNot(_.startsWith("--"))
    if (moduleArgs.isEmpty) sys.error("Usage: Main <path-to-module> [--hypercube]")
    val entryPath = new File(moduleArgs(0)).getCanonicalPath

    // Build the pipeline sequence, optionally inserting HypercubePass
    val basePasses = Seq(
      LoadModules,
      DumpASTs,
      DumpLinear,
      FindFinalInst,
      // SK: TODOAddChecksHere,
      Interpret,
      DesugarBinders
    )

    val allPasses =
      if (hypercubeEnabled) {
        println("Enabling hypercube pass.")
        basePasses :+ HypercubePass :+ GenerateBNFC

      } else {
        basePasses :+ GenerateBNFC
      }

    val pipeline = new Pipeline[Context](allPasses)

    // Execute
    pipeline.execute(Context(entryPath))
  }
}
