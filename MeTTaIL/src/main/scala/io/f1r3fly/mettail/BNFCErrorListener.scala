package io.f1r3fly.mettail

/** Error listener for the parser */
class TestError(msg: String, val line: Int, val column: Int) extends RuntimeException(msg)

class BNFCErrorListener extends org.antlr.v4.runtime.ANTLRErrorListener {
  override def syntaxError(recognizer: org.antlr.v4.runtime.Recognizer[?, ?],
                           offendingSymbol: Object,
                           line: Int,
                           charPositionInLine: Int,
                           msg: String,
                           e: org.antlr.v4.runtime.RecognitionException): Unit = {
    throw new TestError(msg, line, charPositionInLine)
  }

  override def reportAmbiguity(parser: org.antlr.v4.runtime.Parser,
                               dfa: org.antlr.v4.runtime.dfa.DFA,
                               startIndex: Int,
                               stopIndex: Int,
                               exact: Boolean,
                               ambigAlts: java.util.BitSet,
                               configs: org.antlr.v4.runtime.atn.ATNConfigSet): Unit = {
    throw new TestError("Ambiguity at", startIndex, stopIndex)
  }

  override def reportAttemptingFullContext(parser: org.antlr.v4.runtime.Parser,
                                           dfa: org.antlr.v4.runtime.dfa.DFA,
                                           startIndex: Int,
                                           stopIndex: Int,
                                           conflictingAlts: java.util.BitSet,
                                           configs: org.antlr.v4.runtime.atn.ATNConfigSet): Unit = {}

  override def reportContextSensitivity(parser: org.antlr.v4.runtime.Parser,
                                        dfa: org.antlr.v4.runtime.dfa.DFA,
                                        startIndex: Int,
                                        stopIndex: Int,
                                        prediction: Int,
                                        configs: org.antlr.v4.runtime.atn.ATNConfigSet): Unit = {}
}

