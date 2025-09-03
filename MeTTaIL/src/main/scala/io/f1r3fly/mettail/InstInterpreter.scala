package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

class InstInterpreter(
  resolvedModules: Map[String, Module],
  currentModulePath: String,
  moduleProcessor: ModuleProcessor
) {

  import InstInterpreterCases._

  // BasePresOps is defined in InstInterpreterCases below and imported here
  def interpret(env: List[(String, BasePres)], thInst: TheoryInst): Either[String, BasePres] = thInst match {
    case disj: TheoryInstDisj                       => Right(handleDisj(this, env, disj))
    case conj: TheoryInstConj                       => Right(handleConj(this, env, conj))
    case subtract: TheoryInstSubtract               => handleSubtract(this, env, subtract)
    case addExports: TheoryInstAddExports           => handleAddExports(this, env, addExports)
    case addReplacements: TheoryInstAddReplacements => handleAddReplacements(this, env, addReplacements)
    case addTerms: TheoryInstAddTerms               => handleAddTerms(this, env, addTerms)
    case addEquations: TheoryInstAddEquations       => Right(handleAddEquations(this, env, addEquations))
    case addRewrites: TheoryInstAddRewrites         => Right(handleAddRewrites(this, env, addRewrites))
    case empty: TheoryInstEmpty                     => Right(handleEmpty())
    case ctor: TheoryInstCtor                       => 
      Right(handleCtor(this, env, resolvedModules, currentModulePath, ctor, moduleProcessor))
    case ref: TheoryInstRef                         => Right(handleRef(env, ref))
    case rec: TheoryInstRec                         => Right(handleRec(this, env, rec))
    case free: TheoryInstFree                       => Right(handleFree())
  }

  // Checks whether the data can be successfully processed by the interpret() method.
  // Returns None if they can; otherwise, a corresponding error message.
  def check_interpret(env: List[(String, BasePres)], thInst: TheoryInst): Option[String] = {
    thInst match {
      case disj: TheoryInstDisj                       => None
      case conj: TheoryInstConj                       => None
      case subtract: TheoryInstSubtract               => None
      case addExports: TheoryInstAddExports           => checkAddExports(this, env, addExports)
      case addReplacements: TheoryInstAddReplacements => checkAddReplacements(this, env, addReplacements)
      case addTerms: TheoryInstAddTerms               => checkAddTerms(this, env, addTerms)
      case addEquations: TheoryInstAddEquations       => checkAddEquations(this, env, addEquations)
      case addRewrites: TheoryInstAddRewrites         => checkAddRewrites(this, env, addRewrites)
      case empty: TheoryInstEmpty                     => None
      case ctor: TheoryInstCtor                       => checkCtor(
        this, env, resolvedModules, currentModulePath, ctor, moduleProcessor
      )
      case ref: TheoryInstRef                         => checkRef(env, ref)
      case rec: TheoryInstRec                         => None
      case free: TheoryInstFree                       => None
    }
  }

}
