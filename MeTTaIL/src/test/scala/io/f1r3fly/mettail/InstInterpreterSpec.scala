package io.f1r3fly.mettail

import java.io.File
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

class InstInterpreterSpec extends AnyFlatSpec with Matchers {
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

  "InstInterpreter" should "interpret the Rholang module correctly" in {
    val (interpreter, inst) = loadInterpreterFor("../GSLT/src/test/module/Rholang.module")
    val basePres = interpreter.interpret(Nil, inst)
                       .getOrElse(fail("Interpretation of Rholang.module failed"))
    val actual   = PrettyPrinter.print(basePres)

    val expected =
      s"""
      |Presentation Exports
      |{
      |  Proc;
      |  Name;
      |}
      |Terms
      |{
      |  PZero . Proc ::= "0";
      |  PPar . Proc ::= "(" Proc "|" Proc ")";
      |  PRepl . Proc ::= "!" Proc;
      |  PNew . Proc ::= "new" (Bind x Name) "in" (x) Proc;
      |  PDrop . Proc ::= "*" Name;
      |  NQuote . Name ::= "@" Proc;
      |  PSend . Proc ::= Name "!" "(" Proc ")";
      |  PRecv . Proc ::= "for" "(" (Bind x Name) "<-" Name ")" "{" (x) Proc "}";
      |}
      |Equations
      |{
      |  (Mult (Mult x y) z) == (Mult x (Mult y z));
      |  (Mult x (One)) == x;
      |  (Mult (One) x) == x;
      |  (Plus x y) == (Plus y x);
      |  if x # Q then (PPar (PNew x P) Q) == (PNew x (PPar P Q));
      |  (PNew x (PNew x P)) == (PNew x P);
      |  (PNew x (PNew y P)) == (PNew y (PNew x P));
      |  (PRepl P) == (PPar P (PRepl P));
      |  (NQuote (PDrop N)) == N;
      |  (PDrop (NQuote P)) == P;
      |}
      |Rewrites
      |{
      |  RPar1 : let Src ~> Tgt in (PPar Src Q) ~> (PPar Tgt Q);
      |  RPar2 : let Src1 ~> Tgt1 in let Src2 ~> Tgt2 in (PPar Src1 Src2) ~> (PPar Tgt1 Tgt2);
      |  RNew : let Src ~> Tgt in (PNew x Src) ~> (PNew x Tgt);
      |  RComm : (PPar (PRecv y x P) (PSend x Q)) ~> (Subst P (NQuote Q) y)
      |}
      """.stripMargin

    actual.trim shouldEqual expected.trim
  }

  it should "interpret the ArrowCats module correctly" in {
    val (interpreter, inst) = loadInterpreterFor("../GSLT/src/test/module/ArrowCats.module")
    val basePres = interpreter.interpret(Nil, inst)
                       .getOrElse(fail("Interpretation of ArrowCats.module failed"))
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

  it should "error when interpreting a module with duplicate term labels" in {
    val (interpreter, inst) = loadInterpreterFor("../GSLT/src/test/module/bad/RepeatLabel.module")
    val res = interpreter.interpret(Nil, inst)

    res shouldBe Left("Error: Duplicate label in addTerms: Foo")
  }

  it should "error when interpreting a module with duplicate replacement labels" in {
    val (interpreter, inst) = loadInterpreterFor("../GSLT/src/test/module/bad/ReplacementShadows.module")
    val res = interpreter.interpret(Nil, inst)

    res shouldBe Left("Error: Replacement rule label Bar already exists in theory.")
  }

  it should "error when local theory not found" in {
    val emptyImports = new ListImport()
    val emptyProgs   = new ListProg()
    val module       = new ModuleImpl(emptyImports, new NameVar("M"), emptyProgs)
    val resolved     = Map("path" -> module)
    val interpreter  = new InstInterpreter(resolved, "path", ModuleProcessor.default)
    val ctor         = new TheoryInstCtor(new BaseDottedPath("Missing"), new ListTheoryInst())
    val res          = interpreter.interpret(Nil, ctor)

    assert(res.isLeft)
    assert(res.left.get.contains("Theory 'Missing' not found in path or imports"))
  }

  it should "error when module alias not declared" in {
    val imports     = new ListImport()
    val progs       = new ListProg()
    val module      = new ModuleImpl(imports, new NameVar("M"), progs)
    val resolved    = Map("path" -> module)
    val interpreter = new InstInterpreter(resolved, "path", ModuleProcessor.default)
    val dp          = new QualifiedDottedPath("u", new BaseDottedPath("X"))
    val ctor        = new TheoryInstCtor(dp, new ListTheoryInst())
    val res         = interpreter.interpret(Nil, ctor)

    assert(res.isLeft)
    assert(res.left.get.contains("Module alias 'u' not found"))
  }

  it should "error when theory not found in imported module" in {
    val imports     = new ListImport()
    imports.addLast(new ImportModuleAs("u", "UnivAlg.module"))
    val progs       = new ListProg()
    val module      = new ModuleImpl(imports, new NameVar("M"), progs)
    val emptyImp    = new ModuleImpl(new ListImport(), new NameVar("UnivAlg"), new ListProg())
    val resolved    = Map("path" -> module, "UnivAlg.module" -> emptyImp)
    val interpreter = new InstInterpreter(resolved, "path", ModuleProcessor.default)
    val dp          = new QualifiedDottedPath("u", new BaseDottedPath("UnknownTheory"))
    val ctor        = new TheoryInstCtor(dp, new ListTheoryInst())
    val res         = interpreter.interpret(Nil, ctor)

    assert(res.isLeft)
    assert(res.left.get.contains("Module alias 'u' not found in ImportModuleAs statements of path"))
  }

  it should "error when identifier is free" in {
    val resolved    = Map.empty[String, Module]
    val interpreter = new InstInterpreter(resolved, "path", ModuleProcessor.default)
    val ref         = new TheoryInstRef("missing")
    val res         = interpreter.interpret(Nil, ref)

    assert(res.isLeft)
    assert(res.left.get.contains("Identifier missing is free"))
  }
}