package io.f1r3fly.mettail

import org.scalatest.funsuite.AnyFunSuite
import metta_venus.Absyn._
import io.f1r3fly.mettail.ModuleProcessor
import io.f1r3fly.mettail.FileSystem

class ModuleProcessorSpec extends AnyFunSuite {
  // Dummy FileSystem stub: no real I/O
  object DummyFS extends FileSystem {
    override def canonical(path: String): String = path
    override def reader(path: String) = new java.io.StringReader("")
    override def join(parent: String, child: String): String = child
    override def parent(path: String): String = ""
  }

  private val processor = new ModuleProcessor(DummyFS)

  test("dottedPathToString should format Base and Qualified paths") {
    val base = new BaseDottedPath("X")
    val qualified = new QualifiedDottedPath("A", base)
    assert(processor.dottedPathToString(base) == "X")
    assert(processor.dottedPathToString(qualified) == "A.X")
  }

  test("findTheoryDeclInModule should locate an existing theory") {
    val decl = new BaseTheoryDecl(new NameVar("T"), new ListVariableDecl(), new TheoryInstEmpty())
    val progList = new ListProg()
    progList.add(new ProgTheoryDecl(decl))
    val module = new ModuleImpl(new ListImport(), new NameVar("M"), progList)
    assert(processor.findTheoryDeclInModule(module, "T").contains(decl))
    assert(processor.findTheoryDeclInModule(module, "_").isEmpty)
  }

  test("resolveDottedPath should resolve BaseDottedPath in current module") {
    val decl = new BaseTheoryDecl(new NameVar("T"), new ListVariableDecl(), new TheoryInstEmpty())
    val progList = new ListProg()
    progList.add(new ProgTheoryDecl(decl))
    val module = new ModuleImpl(new ListImport(), new NameVar("M"), progList)
    val resolved = Map("path" -> module)
    val dp = new BaseDottedPath("T")
    assert(processor.resolveDottedPath(resolved, "path", dp) == Right(("path", decl)))
  }

  test("resolveDottedPath should return Left when theory is missing") {
    val module = new ModuleImpl(new ListImport(), new NameVar("M"), new ListProg())
    val resolved = Map("p" -> module)
    val dp = new BaseDottedPath("X")
    assert(processor.resolveDottedPath(resolved, "p", dp).isLeft)
  }
}
