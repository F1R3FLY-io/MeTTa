package io.f1r3fly.mettail

import org.scalatest.funsuite.AnyFunSuite
import io.f1r3fly.mettail.InstInterpreterCases._
import io.f1r3fly.mettail.BasePresOps
import metta_venus.Absyn._

class InstInterpreterCasesSpec extends AnyFunSuite {
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

  test("handleEmpty should return an empty BasePres") {
    val res = handleEmpty()
    assert(res.isRight)
    val bp = res.getOrElse(fail("Expected Right(BasePres)"))
    assert(bp == BasePresOps.empty)
  }

  test("handleFree should return an empty BasePres") {
    val res = handleFree()
    assert(res.isRight)
    val bp = res.getOrElse(fail("Expected Right(BasePres)"))
    assert(bp == BasePresOps.empty)
  }

  test("handleDisj should merge two BasePres from interpreter results") {
    // Dummy interpreter that always returns a BasePres with a single category CatA
    val catA = new IdCat("A")
    val singleCatPres = BasePresOps.copyPres(BasePresOps.empty, listcat = Some(List(catA)))
    val dummyInterpreter = new InstInterpreterCasesSpec.DummyInterpreter(singleCatPres)
    val inst = new TheoryInstDisj(new TheoryInstEmpty(), new TheoryInstEmpty())

    val res = handleDisj(dummyInterpreter, Nil, inst)
    assert(res.isRight)
    val bp = res.getOrElse(fail("Expected Right(BasePres)"))
    // Disjunction of two identical pres should have same single category
    assert(bp.listcat_.asScala.toList == List(catA))
  }
}

object InstInterpreterCasesSpec {
  // Dummy interpreter stub for testing: always returns the provided BasePres
  class DummyInterpreter(pres: BasePres) extends AnyRef {
    def interpret(env: List[(String, BasePres)], inst: TheoryInst): Either[String, BasePres] =
      Right(pres)
  }
}
