package io.f1r3fly.mettail

import java.io.{FileReader, InputStreamReader, Reader}
import metta_venus.{MettaVenusLexer, MettaVenusParser, PrettyPrinter}
import org.antlr.v4.runtime.{ANTLRInputStream, CommonTokenStream, ANTLRErrorListener, RecognitionException, Recognizer, Parser}
import java.util.BitSet

// Define a Scala version of TestError.
class TestError(msg: String, val line: Int, val column: Int) extends RuntimeException(msg)

// Define a Scala BNFC error listener.
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
  def main(args: Array[String]): Unit = {
    try {
      // Use standard input if no file is specified.
      val input: Reader = if (args.isEmpty) new InputStreamReader(System.in) else new FileReader(args(0))

      // Create the lexer and add the error listener.
      val lexer = new MettaVenusLexer(new ANTLRInputStream(input))
      lexer.addErrorListener(new BNFCErrorListener)

      // Create the parser and add the error listener.
      val tokens = new CommonTokenStream(lexer)
      val parser = new MettaVenusParser(tokens)
      parser.addErrorListener(new BNFCErrorListener)

      // Call the entry rule. (Test.java uses start_Module().)
      val pc = parser.start_Module()
      val ast = pc.result

      println("\nParse Successful!\n")
      println("[Abstract Syntax]\n")
      println(PrettyPrinter.show(ast))
      println("\n[Linearized Tree]\n")
      println(PrettyPrinter.print(ast))
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
}
