package io.f1r3fly.mettail

import java.io.{File, FileReader, InputStreamReader, Reader}
import metta_venus.{MettaVenusLexer, MettaVenusParser, PrettyPrinter}
import metta_venus.Absyn._
import org.antlr.v4.runtime.{ANTLRInputStream, CommonTokenStream, ANTLRErrorListener, RecognitionException, Recognizer, Parser}
import java.util.BitSet
import scala.collection.mutable
import scala.jdk.CollectionConverters._

class TestError(msg: String, val line: Int, val column: Int) extends RuntimeException(msg)

class BNFCErrorListener extends ANTLRErrorListener {
  override def syntaxError(recognizer: Recognizer[?, ?],
                           offendingSymbol: Object,
                           line: Int,
                           charPositionInLine: Int,
                           msg: String,
                           e: RecognitionException): Unit = {
    throw new TestError(msg, line, charPositionInLine)
  }

  override def reportAmbiguity(parser: Parser,
                               dfa: org.antlr.v4.runtime.dfa.DFA,
                               startIndex: Int,
                               stopIndex: Int,
                               exact: Boolean,
                               ambigAlts: BitSet,
                               configs: org.antlr.v4.runtime.atn.ATNConfigSet): Unit = {
    throw new TestError("Ambiguity at", startIndex, stopIndex)
  }

  override def reportAttemptingFullContext(parser: Parser,
                                           dfa: org.antlr.v4.runtime.dfa.DFA,
                                           startIndex: Int,
                                           stopIndex: Int,
                                           conflictingAlts: BitSet,
                                           configs: org.antlr.v4.runtime.atn.ATNConfigSet): Unit = {}

  override def reportContextSensitivity(parser: Parser,
                                        dfa: org.antlr.v4.runtime.dfa.DFA,
                                        startIndex: Int,
                                        stopIndex: Int,
                                        prediction: Int,
                                        configs: org.antlr.v4.runtime.atn.ATNConfigSet): Unit = {}
}

object Main {
  private val loadedModules = mutable.Set[String]()
  private val asts = mutable.ListBuffer[Module]()
  private var mainModuleInstOpt: Option[Inst] = None

  def main(args: Array[String]): Unit = {
    try {
      val entryFileOpt = if (args.isEmpty) None else Some(new File(args(0)))
      val input: Reader = entryFileOpt match {
        case Some(file) => new FileReader(file)
        case None       => new InputStreamReader(System.in)
      }
      val entryDir = entryFileOpt.map(_.getParentFile.getCanonicalFile).getOrElse(new File(".").getCanonicalFile)
      val entryPath = entryFileOpt.map(_.getCanonicalPath).getOrElse("<stdin>")
      parseModule(input, entryPath, entryDir, isMainModule = true)

      println("\nParse Successful!\n")
      println("[Abstract Syntax Trees]\n")
      asts.foreach(ast => println(PrettyPrinter.show(ast)))
      println("\n[Linearized Trees]\n")
      asts.foreach(ast => println(PrettyPrinter.print(ast)))

      mainModuleInstOpt.foreach { inst =>
        println("\n[Final Inst from Main Module]\n")
        println(PrettyPrinter.print(inst))
        println("\n[Module Environment]\n")
        // Combine environments from all parsed modules.
        val modEnv: ModEnv = asts.toList.foldLeft(ModEnv(Map.empty)) { (acc, m) =>
          ModEnv.merge(acc, ModEnv.build(m))
        }
        println(ModEnv.prettyPrint(modEnv))
        println("\n[Interpretation of Final Inst]\n")
        val interpreter = new InstInterpreter()
        val interpretation = interpreter.interpret(modEnv, List.empty, inst)
        println(interpretation.fold(err => s"Error: $err", pres => Presentation.pretty(pres)))
      }

    } catch {
      case e: TestError =>
        System.err.println(s"At line ${e.line}, column ${e.column} :")
        System.err.println("     " + e.getMessage)
        System.exit(1)
      case e: Exception =>
        e.printStackTrace()
        System.exit(1)
    }
  }

  def parseModule(input: Reader, path: String, currentDir: File, isMainModule: Boolean = false): Unit = {
    if (loadedModules.contains(path)) return
    loadedModules += path

    val lexer = new MettaVenusLexer(new ANTLRInputStream(input))
    lexer.addErrorListener(new BNFCErrorListener)
    val tokens = new CommonTokenStream(lexer)
    val parser = new MettaVenusParser(tokens)
    parser.addErrorListener(new BNFCErrorListener)
    val pc = parser.start_Module()
    val ast = pc.result.asInstanceOf[Module]
    asts += ast

    ast match {
      case m: ModuleImpl =>
        if (isMainModule) {
          mainModuleInstOpt = m.listprog_.iterator.asScala.toList.reverse.collectFirst {
            case progInst: ProgInst => progInst.inst_
          }
        }
        m.listimport_.iterator.asScala.toList.foreach { imp =>
          val importPath: String = imp match {
            case i: ImportModule     => i.string_
            case i: ImportModuleAs   => i.string_
            case i: ImportFromModule => i.string_
          }
          val resolvedFile = {
            val f = new File(importPath)
            if (f.isAbsolute) f else new File(currentDir, importPath)
          }
          val canonicalPath = resolvedFile.getCanonicalPath
          val reader = new FileReader(resolvedFile)
          val nextDir = resolvedFile.getParentFile.getCanonicalFile
          parseModule(reader, canonicalPath, nextDir)
        }
      case _ =>
    }
  }
}
