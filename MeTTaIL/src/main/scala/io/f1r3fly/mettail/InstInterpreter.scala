package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

class InstInterpreter(resolvedModules: Map[String, Module], currentModulePath: String) {

  import InstInterpreterCases._
  // BasePresOps is defined in InstInterpreterCases below and imported here
  def interpret(env: List[(String, BasePres)], thInst: TheoryInst): Either[String, BasePres] = thInst match {
    case rest: TheoryInstRest           => handleRest()
    case sub: TheoryInstSub             => handleSub()
    case disj: TheoryInstDisj           => handleDisj(this, env, disj)
    case conj: TheoryInstConj           => handleConj(this, env, conj)
    case addExports: TheoryInstAddExports => handleAddExports(this, env, addExports)
    case addReplacements: TheoryInstAddReplacements => handleAddReplacements()
    case addTerms: TheoryInstAddTerms   => handleAddTerms(this, env, addTerms)
    case addEquations: TheoryInstAddEquations => handleAddEquations(this, env, addEquations)
    case addRewrites: TheoryInstAddRewrites => handleAddRewrites(this, env, addRewrites)
    case empty: TheoryInstEmpty         => handleEmpty()
    case ctor: TheoryInstCtor           => handleCtor(this, env, resolvedModules, currentModulePath, ctor)
    case ref: TheoryInstRef             => handleRef(env, ref)
    case rec: TheoryInstRec             => handleRec(this, env, rec)
    case free: TheoryInstFree           => handleFree()
  }

  // Used in conj, rewrites, and equations
  private def labelsInAST(ast: AST): Set[String] = ast match {
    case astSExp: ASTSExp => Set(astSExp.ident_)
    case _                => Set.empty[String]
  }

  private def labelsInEquation(eq: Equation): Set[String] = eq match {
    case ef: EquationFresh => labelsInEquation(ef.equation_)
    case ei: EquationImpl  => labelsInAST(ei.ast_1) ++ labelsInAST(ei.ast_2)
    case _                 => Set.empty[String]
  }

  private def labelsInRewrite(rw: Rewrite): Set[String] = rw match {
    case rb: RewriteBase    => labelsInAST(rb.ast_1) ++ labelsInAST(rb.ast_2)
    case rc: RewriteContext => labelsInRewrite(rc.rewrite_)
    case _                  => Set.empty[String]
  }

  // Helper to sequence Eithers
  private def sequence[E, A](eithers: List[Either[E, A]]): Either[E, List[A]] =
    eithers.foldRight(Right(Nil): Either[E, List[A]]) { (e, acc) =>
      for {
        x  <- e
        xs <- acc
      } yield x :: xs
    }

  // Expose label helpers to the handler object
  def helpers: LabelHelpers = new LabelHelpers {
    def labelsInAST(ast: AST): Set[String] = InstInterpreter.this.labelsInAST(ast)
    def labelsInEquation(eq: Equation): Set[String] = InstInterpreter.this.labelsInEquation(eq)
    def labelsInRewrite(rw: Rewrite): Set[String] = InstInterpreter.this.labelsInRewrite(rw)
    def sequence[E, A](eithers: List[Either[E, A]]): Either[E, List[A]] = InstInterpreter.this.sequence(eithers)
  }
}
