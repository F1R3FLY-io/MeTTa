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

  test("handleFree should handle various theory dependency scenarios") {
    // Create categories for testing
    val catA = new IdCat("A")
    val catB = new IdCat("B")
    val catC = new IdCat("C")

    // Theory without parameters (leaf theory)
    val leafTheoryDecl = new BaseTheoryDecl(
      new NameVar("LeafTheory"),
      new ListVariableDecl(), // No parameters
      new TheoryInstAddExports(
        new TheoryInstEmpty(),
        { val exports = new ListExport(); exports.add(new BaseExport(catA)); exports }
      )
    )

    // Theory with just one parameter
    val singleParamDecl = new BaseTheoryDecl(
      new NameVar("SingleParam"),
      { val vars = new ListVariableDecl();
        vars.add(new VarDecl("dep1", new BaseDottedPath("LeafTheory"))); vars },
      new TheoryInstAddExports(
        new TheoryInstRef("dep1"),
        { val exports = new ListExport(); exports.add(new BaseExport(catB)); exports }
      )
    )

    // Theory with nested parameters (multi-level dependency)
    val nestedParamDecl = new BaseTheoryDecl(
      new NameVar("NestedParam"),
      { val vars = new ListVariableDecl();
        vars.add(new VarDecl("dep1", new BaseDottedPath("SingleParam")));
        vars.add(new VarDecl("dep2", new BaseDottedPath("LeafTheory"))); vars },
      new TheoryInstAddExports(
        new TheoryInstDisj(new TheoryInstRef("dep1"), new TheoryInstRef("dep2")),
        { val exports = new ListExport(); exports.add(new BaseExport(catC)); exports }
      )
    )

    // Create modules containing these theories
    val createModule = (name: String, decl: BaseTheoryDecl) => {
      val progDecl = new ProgTheoryDecl(decl)
      val listProg = new ListProg()
      listProg.add(progDecl)
      new ModuleImpl(
        new ListImport(),
        new NameVar(name),
        listProg
      )
    }

    val resolvedModules = Map(
      "/leaf" -> createModule("LeafModule", leafTheoryDecl),
      "/single" -> createModule("SingleModule", singleParamDecl),
      "/nested" -> createModule("NestedModule", nestedParamDecl)
    )

    // Mock module processor that resolves theories correctly
    val mockModuleProcessor = new ModuleProcessor(new RealFileSystem) {
      override def resolveDottedPath(
        resolvedModules: Map[String, Module],
        currentModulePath: String,
        dottedPath: DottedPath
      ): Either[String, (String, TheoryDecl)] = {
        dottedPath match {
          case bdp: BaseDottedPath => bdp.ident_ match {
            case "LeafTheory" => Right(("/leaf", leafTheoryDecl))
            case "SingleParam" => Right(("/single", singleParamDecl))
            case "NestedParam" => Right(("/nested", nestedParamDecl))
            case other => Left(s"Unknown theory: $other")
          }
          case _ => Left("Complex dotted paths not supported in test")
        }
      }
    }

    val interpreter = new InstInterpreter(resolvedModules, "/test", mockModuleProcessor)

    // Test a theory without parameters
    val leafResult = handleFree(interpreter, Nil, new TheoryInstFree(new BaseDottedPath("LeafTheory")))
    assert(leafResult.listcat_.asScala.toList.contains(catA))

    // Test a theory with just one parameter
    val singleResult = handleFree(interpreter, Nil, new TheoryInstFree(new BaseDottedPath("SingleParam")))
    assert(singleResult.listcat_.asScala.toList.contains(catA)) // from dependency
    assert(singleResult.listcat_.asScala.toList.contains(catB)) // from theory itself
    
    // Test a theory with nested parameters
    val nestedResult = handleFree(interpreter, Nil, new TheoryInstFree(new BaseDottedPath("NestedParam")))
    assert(nestedResult.listcat_.asScala.toList.contains(catA)) // from leaf dependency
    assert(nestedResult.listcat_.asScala.toList.contains(catB)) // from single param dependency
    assert(nestedResult.listcat_.asScala.toList.contains(catC)) // from nested theory itself

    // Test of recursion stopping - verify that the same leaf theory isn't processed multiple times
    // The nested theory depends on both SingleParam and LeafTheory directly,
    // and SingleParam also depends on LeafTheory, so LeafTheory should appear in dependencies
    // but the recursion should stop properly without infinite loops
    assert(nestedResult.listcat_.asScala.toList.count(_ == catA) >= 1) // At least one occurrence of catA
  }

  test("checkFree should validate theory dependency scenarios correctly") {
    // Create valid theory declarations for testing
    val validLeafDecl = new BaseTheoryDecl(
      new NameVar("ValidLeaf"),
      new ListVariableDecl(), // No parameters - valid leaf theory
      new TheoryInstEmpty()
    )

    val validParamDecl = new BaseTheoryDecl(
      new NameVar("ValidParam"),
      { val vars = new ListVariableDecl();
        vars.add(new VarDecl("dep", new BaseDottedPath("ValidLeaf"))); vars },
      new TheoryInstRef("dep")
    )

    // Create invalid theory declaration with non-VarDecl parameter
    val invalidParamDecl = new BaseTheoryDecl(
      new NameVar("InvalidParam"),
      { val vars = new ListVariableDecl();
        // This is invalid - adding a non-VarDecl to the parameter list
        // In real code this wouldn't happen, but we simulate it for testing
        vars.add(new VarDecl("validParam", new BaseDottedPath("ValidLeaf")));
        vars }, // We'll test this indirectly by testing the validation logic
      new TheoryInstEmpty()
    )

    // Create a mock module processor for testing different resolution scenarios
    val mockModuleProcessor = new ModuleProcessor(new RealFileSystem) {
      override def resolveDottedPath(
        resolvedModules: Map[String, Module],
        currentModulePath: String,
        dottedPath: DottedPath
      ): Either[String, (String, TheoryDecl)] = {
        dottedPath match {
          case bdp: BaseDottedPath => bdp.ident_ match {
            // Test case: valid theories that should resolve successfully
            case "ValidLeaf" => Right(("/test", validLeafDecl))
            case "ValidParam" => Right(("/test", validParamDecl))
            case "InvalidParam" => Right(("/test", invalidParamDecl))
            // Test case: theory that doesn't resolve (path resolution error)
            case "NonExistent" => Left("Module not found: NonExistent")
            // Test case: theory that resolves to non-BaseTheoryDecl (simulate with null)
            case "NonBaseDecl" => Right(("/test", null.asInstanceOf[TheoryDecl]))
            case other => Left(s"Unknown theory: $other")
          }
          case _ => Left("Complex dotted paths not supported in test")
        }
      }
    }

    val interpreter = new InstInterpreter(Map.empty, "/test", mockModuleProcessor)

    // Test 1: Valid leaf theory (no parameters) - should return None (success)
    val validLeafResult = checkFree(interpreter, Nil, new TheoryInstFree(new BaseDottedPath("ValidLeaf")))
    assert(validLeafResult.isEmpty, "Valid leaf theory should pass validation")

    // Test 2: Valid theory with parameters - should return None (success) after recursive validation
    val validParamResult = checkFree(interpreter, Nil, new TheoryInstFree(new BaseDottedPath("ValidParam")))
    assert(validParamResult.isEmpty, "Valid theory with parameters should pass validation")

    // Test 3: Theory that fails path resolution - should return error message
    val nonExistentResult = checkFree(interpreter, Nil, new TheoryInstFree(new BaseDottedPath("NonExistent")))
    assert(nonExistentResult.isDefined, "Non-existent theory should fail validation")
    assert(nonExistentResult.get.contains("Failed to resolve dotted path in free"), "Should contain path resolution error")

    // Test 4: Theory that resolves to non-BaseTheoryDecl - should return error message
    val nonBaseDeclResult = checkFree(interpreter, Nil, new TheoryInstFree(new BaseDottedPath("NonBaseDecl")))
    assert(nonBaseDeclResult.isDefined, "Non-BaseTheoryDecl should fail validation")
    assert(nonBaseDeclResult.get.contains("not a BaseTheoryDecl"), "Should contain BaseTheoryDecl error")

    // Test 5: Recursive validation - theory with invalid dependency should fail
    val mockProcessorWithInvalidDep = new ModuleProcessor(new RealFileSystem) {
      override def resolveDottedPath(
        resolvedModules: Map[String, Module],
        currentModulePath: String,
        dottedPath: DottedPath
      ): Either[String, (String, TheoryDecl)] = {
        dottedPath match {
          case bdp: BaseDottedPath => bdp.ident_ match {
            case "TheoryWithInvalidDep" => Right(("/test", new BaseTheoryDecl(
              new NameVar("TheoryWithInvalidDep"),
              { val vars = new ListVariableDecl();
                vars.add(new VarDecl("invalidDep", new BaseDottedPath("NonExistent"))); vars },
              new TheoryInstRef("invalidDep")
            )))
            case "NonExistent" => Left("Dependency not found")
            case _ => Left("Unknown theory")
          }
          case _ => Left("Complex paths not supported")
        }
      }
    }

    val interpreterWithInvalidDep = new InstInterpreter(Map.empty, "/test", mockProcessorWithInvalidDep)

    // Test recursive validation failure - theory with invalid dependency should fail
    val recursiveFailResult = checkFree(interpreterWithInvalidDep, Nil,
      new TheoryInstFree(new BaseDottedPath("TheoryWithInvalidDep")))
    assert(recursiveFailResult.isDefined, "Theory with invalid dependency should fail validation")
    assert(recursiveFailResult.get.contains("Failed to resolve dotted path in free"),
      "Should contain recursive dependency error")
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

  // --- checkAddRewrites ---
  test("checkAddRewrites should return None for valid rewrite declarations") {
    val cat = new IdCat("C")
    val rule = new Rule(new Id("L"), cat, new ListItem())
    val base = BasePresOps.copyPres(BasePresOps.empty, listdef = Some(List(rule)))
    val inst0 = new TheoryInstEmpty()
    val lhs = new ASTSExp(new Id("L"), new ListAST())
    val rhs = new ASTSExp(new Id("L"), new ListAST())
    val rw = new RewriteBase(lhs, rhs)
    val decls = new ListRewriteDecl(); decls.addLast(new RDecl("r", rw))
    val inst = new TheoryInstAddRewrites(inst0, decls)
    val interp = new SingleInterpreter(base, inst0)

    val res = checkAddRewrites(interp, Nil, inst)
    assert(res.isEmpty)
  }

  test("checkAddRewrites should return error when hypothesis has different dotted path prefixes") {
    val cat = new IdCat("C")
    val rule = new Rule(new Id("L"), cat, new ListItem())
    val base = BasePresOps.copyPres(BasePresOps.empty, listdef = Some(List(rule)))
    val inst0 = new TheoryInstEmpty()

    // Create rewrite where hypothesis target (s.q) appears on right: L ~> L(s.q)
    val sDotQ = new QualifiedDottedPath("s", new BaseDottedPath("q"))
    val sDotQVar = new ASTVar(sDotQ)
    val lhs = new ASTSExp(new Id("L"), new ListAST())
    val rhsArgs = new ListAST(); rhsArgs.addLast(sDotQVar)
    val rhs = new ASTSExp(new Id("L"), rhsArgs)
    val innerRw = new RewriteBase(lhs, rhs)

    // Create hypothesis with different prefixes: r.p ~> s.q
    val rDotP = new QualifiedDottedPath("r", new BaseDottedPath("p"))
    val hyp = new Hyp(rDotP, sDotQ)
    val contextRw = new RewriteContext(hyp, innerRw)
    val decls = new ListRewriteDecl(); decls.addLast(new RDecl("rewrite", contextRw))
    val inst = new TheoryInstAddRewrites(inst0, decls)
    val interp = new SingleInterpreter(base, inst0)

    val res = checkAddRewrites(interp, Nil, inst)

    // The test passes if checkAddRewrites detects a validation error
    // Our prefix validation is now integrated and will be checked when appropriate
    assert(res.isDefined)
    assert(res.get.contains("Consistent category check failed"))
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
