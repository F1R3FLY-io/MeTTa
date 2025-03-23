package io.f1r3fly.mettail

import metta_venus.Absyn._

case class Presentation(
  exports: List[Cat],
  terms: List[Def],
  equations: List[Equation],
  rewrites: List[RewriteDecl]
)

object Presentation {
  val empty: Presentation = Presentation(Nil, Nil, Nil, Nil)
}

class InstInterpreter {
  def interpret(modEnv: List[Module], env: List[(String, Presentation)], inst: Inst): Presentation = inst match {
    case _: InstPar                => Presentation.empty
    case _: InstGCD                => Presentation.empty
    case _: InstRest               => Presentation.empty
    case _: InstSub                => Presentation.empty
    case _: InstDisj               => Presentation.empty
    case _: InstConj               => Presentation.empty
    case _: InstComp               => Presentation.empty
    case instAddExports: InstAddExports =>
      val basePres = interpret(modEnv, env, instAddExports.inst_)
      val newCats = instAddExports.listexport_.toArray.toList.collect {
        case base: BaseExport => base.cat_
      }
      basePres.copy(exports = basePres.exports ++ newCats)

    case _: InstAddReplacements    => Presentation.empty

    case instAddTerms: InstAddTerms =>
      val basePres = interpret(modEnv, env, instAddTerms.inst_)
      val newTerms = instAddTerms.grammar_ match {
        case g: MkGrammar =>
          import scala.jdk.CollectionConverters.IteratorHasAsScala
          g.listdef_.iterator.asScala.toList
        case _ => Nil
      }
      basePres.copy(terms = basePres.terms ++ newTerms)

    case instAddEquations: InstAddEquations =>
      val basePres = interpret(modEnv, env, instAddEquations.inst_)
      // Extract each Equation from the 'listequation_' field.
      val newEquations = instAddEquations.listequation_.toArray.toList.collect {
        case eq: Equation => eq
      }
      basePres.copy(equations = basePres.equations ++ newEquations)

    case instAddRewrites: InstAddRewrites =>
      val basePres = interpret(modEnv, env, instAddRewrites.inst_)
      // Extract each RewriteDecl from the 'listrewritedecl_' field.
      val newRewrites = instAddRewrites.listrewritedecl_.toArray.toList.collect {
        case rd: RewriteDecl => rd
      }
      basePres.copy(rewrites = basePres.rewrites ++ newRewrites)
    case _: InstEmpty              => Presentation.empty
    case _: InstCtor               => Presentation.empty
    case _: InstCtorK              => Presentation.empty
    case _: InstRef                => Presentation.empty
    case _: InstRec                => Presentation.empty
    case _: InstTail               => Presentation.empty
    case _: InstSup                => Presentation.empty
    case _: InstInf                => Presentation.empty
    case _: InstFree               => Presentation.empty
    case _: InstFreeL              => Presentation.empty
  }
}
