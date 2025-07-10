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

// object Main {
//   def main(args: Array[String]): Unit = {
//     if (args.isEmpty) {
//       System.err.println("Usage: Main <path-to-module>")
//       System.exit(1)
//     }
// 
//     val entryFile = new File(args(0))
//     val entryPath = entryFile.getCanonicalPath
//     println(s"Entry module: $entryPath")
// 
//     val moduleProcessor = ModuleProcessor.default
//     val resolvedModules: Map[String, Module] = moduleProcessor.resolveModules(entryPath)
// 
//     println("\n[Abstract Syntax Trees]\n")
//     resolvedModules.foreach { case (path, module) =>
//       println(s"Module: $path")
//       println(PrettyPrinter.show(module))
//       println()
//     }
// 
//     println("\n[Linearized Trees]\n")
//     resolvedModules.foreach { case (path, module) =>
//       println(s"Module: $path")
//       println(PrettyPrinter.print(module))
//       println()
//     }
// 
//     resolvedModules.get(entryPath) match {
//       case Some(mainMod: ModuleImpl) =>
//         val maybeTheoryInst = mainMod.listprog_.asScala.toList.reverse.collectFirst {
//           case prgThInst: ProgTheoryInst => prgThInst.theoryinst_
//         }
//         maybeTheoryInst match {
//           case Some(inst) =>
//             println("\n[Final Inst from Main Module]\n")
//             println(PrettyPrinter.print(inst))
//             // Interpret the final theory instance.
//             val interpreter = new InstInterpreter(resolvedModules, entryPath, moduleProcessor)
//             interpreter.interpret(List.empty, inst) match {
//               case Right(basePres) =>
//                 println("\n[Interpreted Presentation]\n")
//                 println(PrettyPrinter.print(basePres))
//                 // Generate BNFC from basePres
//                 println("\n[Generated BNFC]\n")
//                 println(PrettyPrinter.print(BNFCRenderer.render(basePres)))
//               case Left(error) =>
//                 println(s"\nError during interpretation: $error")
//             }
//           case None =>
//             println(s"No TheoryInst found in the main module of ${entryPath}.")
//         }
//       case Some(_) =>
//         println(s"Main module ${entryPath} is not a ModuleImpl.")
//       case None =>
//         println(s"Main module ${entryPath} not found in resolved modules.")
//     }
//   }
// }
