package io.f1r3fly.mettail

import org.scalatest.funsuite.AnyFunSuite
import metta_venus.Absyn._
import io.f1r3fly.mettail.{TheoryEnvBuilder, TheoryEnv}

class TheoryEnvSpec extends AnyFunSuite {
  // Use a dummy FileSystem since we're not testing I/O here
  private val builder = new TheoryEnvBuilder(null)

  test("merge should prefer entries from the second environment on key conflicts") {
    val dp = new BaseDottedPath("X")
    val decl1: TheoryDecl = new BaseTheoryDecl(new NameVar("X"), new ListVariableDecl(), new TheoryInstEmpty())
    val decl2: TheoryDecl = new BaseTheoryDecl(new NameVar("Y"), new ListVariableDecl(), new TheoryInstEmpty())
    val env1 = TheoryEnv(Map(dp -> (decl1 -> (decl1, TheoryEnv(Map.empty)))))
    val env2 = TheoryEnv(Map(dp -> (decl2, TheoryEnv(Map.empty))))
    val merged = builder.merge(env1, env2)
    assert(merged.map(dp)._1 == decl2)
  }

  test("extractDottedPath should create a BaseDottedPath from a BaseTheoryDecl") {
    val thDecl: TheoryDecl = new BaseTheoryDecl(new NameVar("T"), new ListVariableDecl(), new TheoryInstEmpty())
    val dp = builder.extractDottedPath(thDecl)
    assert(dp.isInstanceOf[BaseDottedPath])
    assert(dp.asInstanceOf[BaseDottedPath].ident_ == "T")
  }

  test("qualifyDottedPath should prepend alias to a BaseDottedPath") {
    val base = new BaseDottedPath("B")
    val qualified = builder.qualifyDottedPath("A", base)
    assert(qualified.isInstanceOf[QualifiedDottedPath])
    val qp = qualified.asInstanceOf[QualifiedDottedPath]
    assert(qp.ident_ == "A")
    assert(qp.dottedpath_ == base)
  }

  test("getLastIdentifier should return the last component of a QualifiedDottedPath") {
    val dp = new QualifiedDottedPath("A", new BaseDottedPath("B"))
    assert(builder.getLastIdentifier(dp) == "B")
  }

  test("dottedPathToString should join identifiers with dots") {
    val nested = new QualifiedDottedPath("A", new QualifiedDottedPath("B", new BaseDottedPath("C")))
    assert(builder.dottedPathToString(nested) == "A.B.C")
  }

  test("prettyPrint should render environment entries as 'path -> declString'") {
    val thDecl: TheoryDecl = new BaseTheoryDecl(new NameVar("T"), new ListVariableDecl(), new TheoryInstEmpty())
    val dp = builder.extractDottedPath(thDecl)
    val env = TheoryEnv(Map(dp -> (thDecl, TheoryEnv(Map.empty))))
    val printed = builder.prettyPrint(env)
    // Expect format: "T -> <PrettyPrinter output>"
    assert(printed.startsWith("T -> "))
  }
}
