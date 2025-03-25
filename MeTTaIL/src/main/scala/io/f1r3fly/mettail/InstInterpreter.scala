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
  def interpret(modEnv: ModEnv, env: List[(String, Presentation)], thInst: TheoryInst): Either[String, Presentation] = thInst match {
    case _: TheoryInstRest               => Right(Presentation.empty)
    case _: TheoryInstSub                => Right(Presentation.empty)
    case _: TheoryInstDisj               => Right(Presentation.empty)
    case _: TheoryInstConj               => Right(Presentation.empty)
    
    case thInstAddExports: TheoryInstAddExports =>
      interpret(modEnv, env, thInstAddExports.theoryinst_).map { basePres =>
        val newCats = thInstAddExports.listexport_.toArray.toList.collect {
          case base: BaseExport => base.cat_
        }
        basePres.copy(exports = basePres.exports ++ newCats)
      }
      
    case _: TheoryInstAddReplacements    => Right(Presentation.empty)
    
    case thInstAddTerms: TheoryInstAddTerms =>
      interpret(modEnv, env, thInstAddTerms.theoryinst_).map { basePres =>
        val newTerms = thInstAddTerms.grammar_ match {
          case g: MkGrammar =>
            import scala.jdk.CollectionConverters.IteratorHasAsScala
            g.listdef_.iterator.asScala.toList
          case _ => Nil
        }
        basePres.copy(terms = basePres.terms ++ newTerms)
      }
      
    case thInstAddEquations: TheoryInstAddEquations =>
      interpret(modEnv, env, thInstAddEquations.theoryinst_).map { basePres =>
        val newEquations = thInstAddEquations.listequation_.toArray.toList.collect {
          case eq: Equation => eq
        }
        basePres.copy(equations = basePres.equations ++ newEquations)
      }
      
    case thInstAddRewrites: TheoryInstAddRewrites =>
      interpret(modEnv, env, thInstAddRewrites.theoryinst_).map { basePres =>
        val newRewrites = thInstAddRewrites.listrewritedecl_.toArray.toList.collect {
          case rd: RewriteDecl => rd
        }
        basePres.copy(rewrites = basePres.rewrites ++ newRewrites)
      }
      
    case _: TheoryInstEmpty              => Right(Presentation.empty)

    case thInstCtor: TheoryInstCtor        => 
      modEnv match {
        case ModEnv(map) => map.get(thInstCtor.dottedpath_) match {
          case Some((gslt, newmap)) => Right(Presentation.empty)
          case None => Left(s"Identifier ${ModEnv.dottedPathToString(thInstCtor.dottedpath_)} is free")
        }
        case null => Left("modEnv is null!")
      }
    
    case thInstRef: TheoryInstRef =>
      env.reverse.find { case (id, _) => id == thInstRef.ident_ } match {
        case Some((_, pres)) => Right(pres)
        case None => Left(s"Identifier ${thInstRef.ident_} is free")
      }
    
    case thInstRec: TheoryInstRec =>
      interpret(modEnv, env, thInstRec.theoryinst_1).flatMap { pres1 =>
        val envUpdated = env :+ (thInstRec.ident_, pres1)
        interpret(modEnv, envUpdated, thInstRec.theoryinst_2)
      }
      
    case _: TheoryInstFree               => Right(Presentation.empty)
  }
}
