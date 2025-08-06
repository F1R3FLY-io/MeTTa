package io.f1r3fly.mettail

import java.io.File
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

class ParserSpec extends AnyFlatSpec with Matchers {
  private def loadInterpreterFor(relPath: String): (InstInterpreter, TheoryInst) = {
    val moduleFile  = new File(relPath)
    val entryPath   = moduleFile.getCanonicalPath
    val processor   = ModuleProcessor.default
    val resolvedMap = processor.resolveModules(entryPath)
    val mainMod     = resolvedMap(entryPath).asInstanceOf[ModuleImpl]
    val inst = mainMod.listprog_.asScala.toList
                   .reverse
                   .collectFirst { case prg: ProgTheoryInst => prg.theoryinst_ }
                   .getOrElse(fail(s"No top-level TheoryInst found in $entryPath"))
    val interpreter = new InstInterpreter(resolvedMap, entryPath, processor)
    (interpreter, inst)
  }

  it should "interpret the ArithmeticOperations module correctly" in {
    val (interpreter, inst) = loadInterpreterFor("../GSLT/src/test/module/ArithmeticOperations.module")
    val basePres = interpreter.interpret(Nil, inst)
                       .getOrElse(fail("Interpretation of ArithmeticOperations.module failed"))
    val actual   = PrettyPrinter.print(basePres)

    val expected =
      s"""
      |Presentation Exports
      |{
      |  T1;
      |  T2;
      |  T3;
      |  T4;
      |  (T1 -> T2);
      |}
      |Terms
      |{
      |  Qux . T1 ::= "qux";
      |  Quux . T2 ::= "quux";
      |  Bar . T3 ::= "bar" (Bind t1 T1) "." (t1) T2;
      |  Baz . T3 ::= "baz" T2;
      |  Bee . T3 ::= "bee" (T1 -> T2);
      |  Foo . T4 ::= "foo" (Bind t1t2 (T1 -> T2)) "." (t1t2) T3;
      |  Deep . T1 ::= "deep" (Bind t (((T1 -> T1) -> (T1 -> T1)) -> T1)) "." (t) T1;
      |}
      |Equations
      |{
      |}
      |Rewrites
      |{
      |}
      """.stripMargin

    actual.trim shouldEqual expected.trim
  }

}