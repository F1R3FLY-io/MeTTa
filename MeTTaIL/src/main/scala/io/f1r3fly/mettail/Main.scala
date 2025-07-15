package io.f1r3fly.mettail

import java.io.File
import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

object Main {
  def main(args: Array[String]): Unit = {
    if (args.isEmpty) sys.error("Usage: Main <path-to-module>")
    val entry = new File(args(0)).getCanonicalPath

    val pipeline = new Pipeline[Context](Seq(
      LoadModules,
      DumpASTs,
      DumpLinear,
      FindFinalInst,
      Interpret,
      GenerateBNFC
    ))

    val entryFile = new File(args(0))
    val entryPath = entryFile.getCanonicalPath
    pipeline.execute(Context(entryPath))
  }
}
