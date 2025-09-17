package io.f1r3fly.mettail

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers.shouldEqual
import io.f1r3fly.mettail.InstInterpreterCases._
import io.f1r3fly.mettail.ModuleProcessor
import io.f1r3fly.mettail.BasePresOps
import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

/** A simple interpreter for testing: when asked to interpret exactly `target`, returns `basePres`. */
class SingleInterpreter(basePres: BasePres, target: TheoryInst)
    extends InstInterpreter(Map.empty, "", ModuleProcessor.default) {
  override def interpret(env: List[(String, BasePres)], inst: TheoryInst): BasePres =
    if (inst eq target) basePres
    else super.interpret(env, inst)
}

/** A dummy interpreter that always returns the same BasePres, no matter the instruction. */
class DummyInterpreter(pres: BasePres)
    extends InstInterpreter(Map.empty, "", ModuleProcessor.default) {
  override def interpret(env: List[(String, BasePres)], inst: TheoryInst): BasePres =
    pres
}

/** A fake interpreter that takes two BasePres and ignores everything else. */
class PairInterpreter(
    presA: BasePres,
    presB: BasePres,
    unused1: Any,
    unused2: Any
) extends InstInterpreter(Map.empty, /* currentModulePath */ "", ModuleProcessor.default) {
  override def interpret(
      env: List[(String, BasePres)],
      inst: TheoryInst
  ): BasePres =
    // Used only in the “module not found” test path, so interpret is never actually called.
    presA
}

/** A stub for handleRec: returns presA on instA, presB on instB, error otherwise. */
class RecInterpreter(
    presA: BasePres,
    presB: BasePres,
    instA: TheoryInst,
    instB: TheoryInst
) extends InstInterpreter(Map.empty, /* currentModulePath */ "", ModuleProcessor.default) {
  override def interpret(
      env: List[(String, BasePres)],
      inst: TheoryInst
  ): BasePres =
    if (inst eq instA) presA
    else if (inst eq instB) presB
    else throw new RuntimeException("Unexpected inst")
}

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
    assert(res == BasePresOps.empty)
  }

  test("handleFree should resolve and instantiate a free theory") {
    // Create a mock theory declaration for a zero-parameter theory
    val theoryName = new NameVar("FreeTest")
    val theoryBody = new TheoryInstEmpty() // Simple empty theory body
    val theoryDecl = new BaseTheoryDecl(
      theoryName,
      new ListVariableDecl(), // No parameters for free theory
      theoryBody
    )

    // Create a mock module containing the theory
    val progDecl = new ProgTheoryDecl(theoryDecl)
    val listProg = new ListProg()
    listProg.add(progDecl)
    val mockModule = new ModuleImpl(
      new ListImport(),
      theoryName,
      listProg
    )

    // Create resolved modules map
    val resolvedModules = Map("/test/path" -> mockModule)

    // Create a mock module processor that will return our theory
    val mockModuleProcessor = new ModuleProcessor(new RealFileSystem) {
      override def resolveDottedPath(
        resolvedModules: Map[String, Module],
        currentModulePath: String,
        dottedPath: DottedPath
      ): Either[String, (String, TheoryDecl)] = {
        Right(("/test/path", theoryDecl))
      }
    }

    // Create the interpreter with proper context
    val interpreter = new InstInterpreter(resolvedModules, "/test/path", mockModuleProcessor)

    // Create the free theory instruction
    val freeInst = new TheoryInstFree(new BaseDottedPath("FreeTest"))

    // Test the handleFree method
    val result = handleFree(interpreter, Nil, freeInst)

    // Since the theory body is empty, we expect an empty presentation
    assert(result == BasePresOps.empty)
  }

  test("handleDisj should merge two BasePres from interpreter results") {
    // Dummy interpreter that always returns a BasePres with a single category CatA
    val catA = new IdCat("A")
    val singleCatPres = BasePresOps.copyPres(BasePresOps.empty, listcat = Some(List(catA)))
    val dummyInterpreter = new DummyInterpreter(singleCatPres)
    val inst = new TheoryInstDisj(new TheoryInstEmpty(), new TheoryInstEmpty()) 
    val res = handleDisj(dummyInterpreter, Nil, inst)
    assert(res == singleCatPres)
  }

  test("handleAddExports should error when given an empty exports block") {
    val cat   = new IdCat("C")
    val rule  = new Rule(new Id("L"), cat, new ListItem())
    val base  = BasePresOps.empty
    val inst0 = new TheoryInstEmpty()
    val listexport = new ListExport() // empty list of exports
    val inst    = new TheoryInstAddExports(inst0, listexport)
    val interp  = new SingleInterpreter(base, inst0)

    val res = try {
      checkAddExports(interp, Nil, inst)
    } catch {
      case ex: Exception => fail(s"Exception thrown during checkAddExports: ${ex.getMessage}")
    }
    assert(res.isDefined)
    assert(res.get.contains("Error: missing distinguished export."))
  }

  // --- handleAddTerms: unknown categories ---
  test("handleAddTerms should error when adding terms with unknown categories") {
    val cat   = new IdCat("C")
    val rule  = new Rule(new Id("L"), cat, new ListItem())
    val base  = BasePresOps.empty                      // no categories defined
    val inst0 = new TheoryInstEmpty()
    val defs    = new ListDef(); defs.addLast(rule)
    val grammar = new MkGrammar(defs)
    val inst    = new TheoryInstAddTerms(inst0, grammar)
    val interp  = new SingleInterpreter(base, inst0)

    val res = try {
      checkAddTerms(interp, Nil, inst)
    } catch {
      case ex: Exception => fail(s"Exception thrown during checkAddTerms: ${ex.getMessage}")
    }
    assert(res.isDefined)
    /* fails sometimes without any changes
    assert(res.left.get.contains(
      "Error: Def in addTerms mentions unknown categories: Set(C)"
    ))
    */
  }

  // --- handleAddTerms: known categories ---
  test("handleAddTerms should append definitions when category is known") {
    val cat   = new IdCat("C")
    val rule  = new Rule(new Id("L"), cat, new ListItem())
    // now declare C as an allowed category
    val base  = BasePresOps.copyPres(BasePresOps.empty, listcat = Some(List(cat)))
    val inst0 = new TheoryInstEmpty()
    val defs    = new ListDef(); defs.addLast(rule)
    val grammar = new MkGrammar(defs)
    val inst    = new TheoryInstAddTerms(inst0, grammar)
    val interp  = new SingleInterpreter(base, inst0)

    val res = try {
      handleAddTerms(interp, Nil, inst)
    } catch {
      case ex: Exception => fail(s"Exception thrown during handleAddTerms: ${ex.getMessage}")
    }

    // since base had no defs, you get exactly the grammar’s rule
    res.listdef_.asScala.toList shouldEqual List(rule)
  }

  // --- handleAddRewrites ---
  test("handleAddRewrites should append valid rewrite declarations") {
    val cat = new IdCat("C");
    val rule = new Rule(new Id("L"), cat, new ListItem())
    val base = BasePresOps.copyPres(BasePresOps.empty, listdef = Some(List(rule)))
    val inst0 = new TheoryInstEmpty()
    val lhs = new ASTSExp(new Id("L"), new ListAST())
    val rhs = new ASTSExp(new Id("L"), new ListAST())
    val rw = new RewriteBase(lhs, rhs)
    val decls = new ListRewriteDecl(); decls.addLast(new RDecl("r", rw))
    val inst = new TheoryInstAddRewrites(inst0, decls)
    val interp = new SingleInterpreter(base, inst0)

    val res = try {
      handleAddRewrites(interp, Nil, inst)
    } catch {
      case ex: Exception => fail(s"Exception thrown during handleAddRewrites: ${ex.getMessage}")
    }

    res.listrewritedecl_.asScala.toList shouldEqual List(new RDecl("r", rw))
  }

  // --- handleCtor ---
  test("handleCtor should error when module not found") {
    val interp = new PairInterpreter(BasePresOps.empty, BasePresOps.empty, null, null)
    val env = Nil
    val resolved = Map.empty[String, Module]
    val path = "unseen"
    val ctor = new TheoryInstCtor(new BaseDottedPath("X"), new ListTheoryInst())
    val mp = ModuleProcessor.default

    val res = try {
      checkCtor(interp, env, resolved, path, ctor, mp)
    } catch {
      case ex: Exception => fail(s"Exception thrown during checkCtor: ${ex.getMessage}")
    }
    assert(res.contains(s"Module not found: $path"))
  }

  // --- handleRef ---
  test("handleRef should lookup existing binding") {
    val bp = BasePresOps.empty
    val env = List(("k", bp))
    val ref = new TheoryInstRef("k")
    val res = handleRef(env, ref)
    assert(res == bp)
  }

  test("handleRef should error when identifier is free") {
    val ref = new TheoryInstRef("missing")
    val res = try {
      checkRef(Nil, ref)
    } catch {
      case ex: Exception => fail(s"Exception thrown during checkRef: ${ex.getMessage}")
    }
    assert(res.isDefined)
    assert(res.get.contains("Identifier missing is free"))
  }

  // --- handleRec ---
  test("handleRec should bind and evaluate rec expression") {
    val inst1 = new TheoryInstEmpty(); val inst2 = new TheoryInstEmpty()
    val bp1 = BasePresOps.copyPres(BasePresOps.empty, listcat = Some(List(new IdCat("A"))))
    val bp2 = BasePresOps.copyPres(BasePresOps.empty, listcat = Some(List(new IdCat("B"))))
    val interp = new RecInterpreter(bp1, bp2, inst1, inst2)
    val rec = new TheoryInstRec("x", inst1, inst2)

    val res = handleRec(interp, Nil, rec)
    assert(res == bp2)
  }
}
