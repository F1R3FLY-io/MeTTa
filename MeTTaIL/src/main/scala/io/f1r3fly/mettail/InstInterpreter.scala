package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

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

class InstInterpreter(resolvedModules: Map[String, Module], currentModulePath: String) {

  // Helper: sequences a list of Either values.
  private def sequence[E, A](eithers: List[Either[E, A]]): Either[E, List[A]] =
    eithers.foldRight(Right(Nil): Either[E, List[A]]) { (e, acc) =>
      for {
        x  <- e
        xs <- acc
      } yield x :: xs
    }

  def interpret(env: List[(String, Presentation)], thInst: TheoryInst): Either[String, Presentation] = thInst match {
    case _: TheoryInstRest    => Right(Presentation.empty)
    case _: TheoryInstSub     => Right(Presentation.empty)
    case _: TheoryInstDisj    => Right(Presentation.empty)
    case _: TheoryInstConj    => Right(Presentation.empty)

    case thInstAddExports: TheoryInstAddExports =>
      interpret(env, thInstAddExports.theoryinst_).map { basePres =>
        val newCats = thInstAddExports.listexport_.toArray.toList.collect {
          case base: BaseExport => base.cat_
        }
        basePres.copy(exports = basePres.exports ++ newCats)
      }

    case _: TheoryInstAddReplacements => Right(Presentation.empty)

    case thInstAddTerms: TheoryInstAddTerms =>
      interpret(env, thInstAddTerms.theoryinst_).map { basePres =>
        val newTerms = thInstAddTerms.grammar_ match {
          case g: MkGrammar =>
            import scala.jdk.CollectionConverters.IteratorHasAsScala
            g.listdef_.iterator.asScala.toList
          case _ => Nil
        }
        basePres.copy(terms = basePres.terms ++ newTerms)
      }

    case thInstAddEquations: TheoryInstAddEquations =>
      interpret(env, thInstAddEquations.theoryinst_).map { basePres =>
        val newEquations = thInstAddEquations.listequation_.toArray.toList.collect {
          case eq: Equation => eq
        }
        basePres.copy(equations = basePres.equations ++ newEquations)
      }

    case thInstAddRewrites: TheoryInstAddRewrites =>
      interpret(env, thInstAddRewrites.theoryinst_).map { basePres =>
        val newRewrites = thInstAddRewrites.listrewritedecl_.toArray.toList.collect {
          case rd: RewriteDecl => rd
        }
        basePres.copy(rewrites = basePres.rewrites ++ newRewrites)
      }

    case _: TheoryInstEmpty => Right(Presentation.empty)

    case thInstCtor: TheoryInstCtor => {
      // Use resolveDottedPath to obtain the theory declaration.
      ModuleProcessor.resolveDottedPath(resolvedModules, currentModulePath, thInstCtor.dottedpath_) match {
        case Left(error) => Left(error)
        case Right((modulePath, theoryDecl)) => {
          theoryDecl match {
            case baseDecl: BaseTheoryDecl =>
              // Ensure the number of actuals matches the number of formals.
              if (baseDecl.listvariabledecl_.size != thInstCtor.listtheoryinst_.size)
                Left(s"Mismatch in number of arguments for theory ${baseDecl.name_}")
              else {
                // Evaluate each actual parameter.
                val actuals: List[TheoryInst] = thInstCtor.listtheoryinst_.asScala.toList
                sequence(actuals.map(actual => interpret(env, actual))).flatMap { actualPresentations =>
                  // Check that every formal is a VarDecl and extract its identifier.
                  val formalEithers: List[Either[String, String]] = baseDecl.listvariabledecl_.asScala.toList.map {
                    case varDecl: VarDecl => Right(varDecl.ident_.toString)
                    case _                => Left(s"Non-var declaration encountered in formal parameter list for theory ${baseDecl.name_}")
                  }
                  sequence(formalEithers).flatMap { formals =>
                    // Bind each formal to its corresponding evaluated actual.
                    val newBindings: List[(String, Presentation)] = formals.zip(actualPresentations)
                    // **CRUCIAL CHANGE:**
                    // Use a new InstInterpreter with the current module updated to the one in which the theory is defined.
                    new InstInterpreter(resolvedModules, modulePath).interpret(env ++ newBindings, baseDecl.theoryinst_)
                  }
                }
              }
            case _ =>
              Left("Resolved theory declaration is not a BaseTheoryDecl")
          }
        }
      }
    }

    case thInstRef: TheoryInstRef =>
      env.reverse.find { case (id, _) => id == thInstRef.ident_ } match {
        case Some((_, pres)) => Right(pres)
        case None            => Left(s"Identifier ${thInstRef.ident_} is free")
      }

    case thInstRec: TheoryInstRec =>
      interpret(env, thInstRec.theoryinst_1).flatMap { pres1 =>
        val envUpdated = env :+ (thInstRec.ident_, pres1)
        interpret(envUpdated, thInstRec.theoryinst_2)
      }

    case _: TheoryInstFree => Right(Presentation.empty)
  }
}
