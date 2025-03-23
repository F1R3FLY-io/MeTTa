package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter

case class Presentation(
  exports: List[Cat],
  terms: List[Def],
  equations: List[Equation],
  rewrites: List[RewriteDecl]
)

object Presentation {
  val empty: Presentation = Presentation(Nil, Nil, Nil, Nil)

  def pretty(p: Presentation): String =
    s"""Presentation:
       |  Exports:
       |    ${p.exports.map(PrettyPrinter.print).mkString("\n    ")}
       |  Terms:
       |    ${p.terms.map(PrettyPrinter.print).mkString("\n    ")}
       |  Equations:
       |    ${p.equations.map(PrettyPrinter.print).mkString("\n    ")}
       |  Rewrites:
       |    ${p.rewrites.map(PrettyPrinter.print).mkString("\n    ")}
       |""".stripMargin
}

class InstInterpreter {
  def interpret(modEnv: List[Module], env: List[(String, Presentation)], inst: Inst): Either[String, Presentation] = inst match {
    case _: InstPar                => Right(Presentation.empty)
    case _: InstGCD                => Right(Presentation.empty)
    case _: InstRest               => Right(Presentation.empty)
    case _: InstSub                => Right(Presentation.empty)
    case _: InstDisj               => Right(Presentation.empty)
    case _: InstConj               => Right(Presentation.empty)
    case _: InstComp               => Right(Presentation.empty)
    
    case instAddExports: InstAddExports =>
      interpret(modEnv, env, instAddExports.inst_).map { basePres =>
        val newCats = instAddExports.listexport_.toArray.toList.collect {
          case base: BaseExport => base.cat_
        }
        basePres.copy(exports = basePres.exports ++ newCats)
      }
      
    case _: InstAddReplacements    => Right(Presentation.empty)
    
    case instAddTerms: InstAddTerms =>
      interpret(modEnv, env, instAddTerms.inst_).map { basePres =>
        val newTerms = instAddTerms.grammar_ match {
          case g: MkGrammar =>
            import scala.jdk.CollectionConverters.IteratorHasAsScala
            g.listdef_.iterator.asScala.toList
          case _ => Nil
        }
        basePres.copy(terms = basePres.terms ++ newTerms)
      }
      
    case instAddEquations: InstAddEquations =>
      interpret(modEnv, env, instAddEquations.inst_).map { basePres =>
        val newEquations = instAddEquations.listequation_.toArray.toList.collect {
          case eq: Equation => eq
        }
        basePres.copy(equations = basePres.equations ++ newEquations)
      }
      
    case instAddRewrites: InstAddRewrites =>
      interpret(modEnv, env, instAddRewrites.inst_).map { basePres =>
        val newRewrites = instAddRewrites.listrewritedecl_.toArray.toList.collect {
          case rd: RewriteDecl => rd
        }
        basePres.copy(rewrites = basePres.rewrites ++ newRewrites)
      }
      
    case _: InstEmpty              => Right(Presentation.empty)
    case _: InstCtor               => Right(Presentation.empty)
    case _: InstCtorK              => Right(Presentation.empty)

    case instRef: InstRef =>
      env.reverse.find { case (id, _) => id == instRef.ident_ } match {
        case Some((_, pres)) => Right(pres)
        case None => Left(s"Identifier ${instRef.ident_} is free")
      }
    
    case instRec: InstRec =>
      interpret(modEnv, env, instRec.inst_1).flatMap { pres1 =>
        // Append (ident_, pres1) to the current environment and interpret inst_2
        val envUpdated = env :+ (instRec.ident_, pres1)
        interpret(modEnv, envUpdated, instRec.inst_2)
      }
      
    case _: InstTail               => Right(Presentation.empty)
    case _: InstSup                => Right(Presentation.empty)
    case _: InstInf                => Right(Presentation.empty)
    case _: InstFree               => Right(Presentation.empty)
    case _: InstFreeL              => Right(Presentation.empty)
  }
}
