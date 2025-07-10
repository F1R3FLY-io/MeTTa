package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

trait Pass[C] {
  def name: String
  def run(ctx: C): C
}

class Pipeline[C](passes: Seq[Pass[C]]) {
  def execute(initial: C): C =
    passes.foldLeft(initial) { (ctx, pass) =>
      println(s"=== Running pass: ${pass.name} ===")
      pass.run(ctx)
    }
}

case class Context(
  entryPath:   String,
  modules:     Map[String, Module]           = Map.empty,
  asts:        Seq[(String, Module)]         = Nil,
  linearized:  Seq[(String, String)]         = Nil,
  finalInst:   Option[TheoryInst]            = None,
  presentation: Option[BasePres]             = None,
  bnfcGrammar: Option[Grammar]               = None
)

object LoadModules extends Pass[Context] {
  val name = "Load modules"
  def run(ctx: Context) = {
    val proc = ModuleProcessor.default
    val mods = proc.resolveModules(ctx.entryPath)
    ctx.copy(modules = mods)
  }
}

object DumpASTs extends Pass[Context] {
  val name = "Dump ASTs"
  def run(ctx: Context) = {
    println("\n[Abstract Syntax Trees]\n")
    ctx.modules.toSeq.foreach { case (path, m) =>
      println(s"Module: $path")
      println(PrettyPrinter.show(m))
      println()
    }
    ctx.copy(asts = ctx.modules.toSeq)
  }
}

object DumpLinear extends Pass[Context] {
  val name = "Dump linearized trees"
  def run(ctx: Context) = {
    println("\n[Linearized Trees]\n")
    ctx.modules.toSeq.map { case (p,m) =>
      p -> PrettyPrinter.print(m)
    }.foreach { case (p, s) =>
      println(s"Module: $p\n$s\n")
    }
    ctx.copy(linearized = ctx.modules.toSeq.map { case (p,m) => p -> PrettyPrinter.print(m) })
  }
}

object FindFinalInst extends Pass[Context] {
  val name = "Extract final TheoryInst"
  def run(ctx: Context) = {
    val inst = ctx.modules(ctx.entryPath).asInstanceOf[ModuleImpl]
      .listprog_.asScala.toList.reverse
      .collectFirst { case p: ProgTheoryInst => p.theoryinst_ }
    ctx.copy(finalInst = inst)
  }
}

object Interpret extends Pass[Context] {
  val name = "Interpret"
  def run(ctx: Context) = {
    ctx.finalInst match {
      case Some(inst) =>
        val interp = new InstInterpreter(ctx.modules, ctx.entryPath, ModuleProcessor.default)
        interp.interpret(Nil, inst) match {
          case Right(pres) =>
            println("\n[Interpreted Presentation]\n")
            println(PrettyPrinter.print(pres))
            ctx.copy(presentation = Some(pres))
          case Left(err) =>
            sys.error(s"Interpretation failed: $err")
        }
      case None => sys.error("No TheoryInst found")
    }
  }
}

object GenerateBNFC extends Pass[Context] {
  val name = "Generate BNFC"
  def run(ctx: Context) = {
    val grammar = ctx.presentation.map(BNFCRenderer.render)
                        .getOrElse(sys.error("No presentation"))
    println("\n[Generated BNFC]\n")
    println(PrettyPrinter.print(grammar))
    ctx.copy(bnfcGrammar = Some(grammar))
  }
}
