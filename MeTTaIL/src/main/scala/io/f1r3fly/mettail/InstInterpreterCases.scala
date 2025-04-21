package io.f1r3fly.mettail

import org.scalatest.funsuite.AnyFunSuite
import io.f1r3fly.mettail.InstInterpreterCases._
import io.f1r3fly.mettail.ModuleProcessor
import io.f1r3fly.mettail.InstInterpreterCasesSpec._
import io.f1r3fly.mettail.BasePresOps
import metta_venus.Absyn._
import scala.jdk.CollectionConverters._

class InstInterpreterCasesSpec extends AnyFunSuite {

  // --- sequence ---
  test("sequence should collect rights into a Right of list") {
    val rights = List(Right(1), Right(2), Right(3))
    val result = sequence(rights)
    assert(result == Right(List(1, 2, 3)))
  }

  test("sequence should return the first Left encountered") {
    val error = Left("fail")
    val mixed = List(Right(1), error, Right(2))
    val result = sequence(mixed)
    assert(result == error)
  }

  // --- handleEmpty & handleFree ---
  test("handleEmpty should return an empty BasePres") {
    val res = handleEmpty()
    assert(res.isRight)
    assert(res.getOrElse(fail("Expected Right(BasePres)")) == BasePresOps.empty)
  }

  test("handleFree should return an empty BasePres") {
    val res = handleFree()
    assert(res.isRight)
    assert(res.getOrElse(fail("Expected Right(BasePres)")) == BasePresOps.empty)
  }
  // --- handleAddTerms ---
  test("handleAddTerms should append definitions from grammar") {
    val cat = new IdCat("C");
    val rule = new Rule(new Label("L"), cat, new ListItem())
    val base = BasePresOps.copyPres(BasePresOps.empty, listdef = Some(List(rule)))
    val inst0 = new TheoryInstEmpty()
    val defs = new ListDef(); defs.addLast(rule)
    val grammar = new MkGrammar(defs)
    val inst = new TheoryInstAddTerms(inst0, grammar)
    val interp = new SingleInterpreter(base, inst0)

    val res = handleAddTerms(interp, Nil, inst)
    assert(res.isRight)
    val out = res.getOrElse(fail())
    out.listdef_.asScala.toList shouldEqual List(rule, rule)
  }

  // --- handleAddRewrites ---
  test("handleAddRewrites should append valid rewrite declarations") {
    val cat = new IdCat("C");
    val rule = new Rule(new Label("L"), cat, new ListItem())
    val base = BasePresOps.copyPres(BasePresOps.empty, listdef = Some(List(rule)))
    val inst0 = new TheoryInstEmpty()
    val lhs = new ASTSExp(new Id("L"), new ListAST())
    val rhs = new ASTSExp(new Id("L"), new ListAST())
    val rw = new RewriteBase(lhs, rhs)
    val decls = new ListRewriteDecl(); decls.addLast(new RDecl("r", rw))
    val inst = new TheoryInstAddRewrites(inst0, decls)
    val interp = new SingleInterpreter(base, inst0)

    val res = handleAddRewrites(interp, Nil, inst)
    assert(res.isRight)
    val out = res.getOrElse(fail())
    out.listrewritedecl_.asScala.toList shouldEqual List(new RDecl("r", rw))
  }

  // --- handleCtor ---
  test("handleCtor should error when module not found") {
    val interp = new PairInterpreter(BasePresOps.empty, BasePresOps.empty, null, null)
    val env = Nil
    val resolved = Map.empty[String, Module]
    val path = "unseen"
    val ctor = new TheoryInstCtor(new BaseDottedPath("X"), new ListTheoryInst())
    val mp = ModuleProcessor.default

    val res = handleCtor(interp, env, resolved, path, ctor, mp)
    assert(res.isLeft)
    assert(res.left.get.contains(s"Module not found: $path"))
  }

  // --- handleRef ---
  test("handleRef should lookup existing binding") {
    val bp = BasePresOps.empty
    val env = List(("k", bp))
    val ref = new TheoryInstRef("k")
    val res = handleRef(env, ref)
    assert(res == Right(bp))
  }

  test("handleRef should error when identifier is free") {
    val ref = new TheoryInstRef("missing")
    val res = handleRef(Nil, ref)
    assert(res.isLeft)
    assert(res.left.get.contains("Identifier missing is free"))
  }

  // --- handleRec ---
  test("handleRec should bind and evaluate rec expression") {
    val inst1 = new TheoryInstEmpty(); val inst2 = new TheoryInstEmpty()
    val bp1 = BasePresOps.copyPres(BasePresOps.empty, listcat = Some(List(new IdCat("A"))))
    val bp2 = BasePresOps.copyPres(BasePresOps.empty, listcat = Some(List(new IdCat("B"))))
    val interp = new RecInterpreter(bp1, bp2, inst1, inst2)
    val rec = new TheoryInstRec("x", inst1, inst2)

    val res = handleRec(interp, Nil, rec)
    assert(res == Right(bp2))
  }
}

object InstInterpreterCasesSpec {  // Interpreter stubs for various handle* functions are defined below

  class RecInterpreter(
      presA: BasePres,
      presB: BasePres,
      instA: TheoryInst,
      instB: TheoryInst
  ) {
    def interpret(env: List[(String, BasePres)], inst: TheoryInst): Either[String, BasePres] =
      if (inst eq instA) Right(presA)
      else if (inst eq instB) Right(presB)
      else Left("Unexpected inst")
  }
}
