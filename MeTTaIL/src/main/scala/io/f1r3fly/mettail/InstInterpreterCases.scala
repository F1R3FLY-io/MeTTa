package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._
import io.f1r3fly.mettail.ModuleProcessor

object InstInterpreterCases {

  trait LabelHelpers {
    def labelsInAST(ast: AST): Set[String]
    def labelsInEquation(eq: Equation): Set[String]
    def labelsInRewrite(rw: Rewrite): Set[String]
    def sequence[E, A](eithers: List[Either[E, A]]): Either[E, List[A]]
  }

  def handleRest(): Either[String, Presentation] =
    Right(Presentation.empty)

  def handleSub(): Either[String, Presentation] =
    Right(Presentation.empty)

  def handleEmpty(): Either[String, Presentation] =
    Right(Presentation.empty)

  def handleFree(): Either[String, Presentation] =
    Right(Presentation.empty)

  def handleDisj(interpreter: InstInterpreter, env: List[(String, Presentation)], disj: TheoryInstDisj): Either[String, Presentation] =
    for {
      presA <- interpreter.interpret(env, disj.theoryinst_1)
      presB <- interpreter.interpret(env, disj.theoryinst_2)
    } yield Presentation(
      exports   = (presA.exports ++ presB.exports).distinct,
      terms     = (presA.terms ++ presB.terms).distinct,
      equations = (presA.equations ++ presB.equations).distinct,
      rewrites  = (presA.rewrites ++ presB.rewrites).distinct
    )

  def handleConj(interpreter: InstInterpreter, env: List[(String, Presentation)], conj: TheoryInstConj): Either[String, Presentation] = {
    val h = interpreter.helpers
    for {
      presA <- interpreter.interpret(env, conj.theoryinst_1)
      presB <- interpreter.interpret(env, conj.theoryinst_2)
    } yield {
      val commonExports = presA.exports.toSet intersect presB.exports.toSet
      val commonTerms   = presA.terms.toSet intersect presB.terms.toSet

      val filteredTerms = commonTerms.filter {
        case rule: Rule =>
          val fromRule  = Set(rule.cat_)
          val fromItems = rule.listitem_.asScala.collect {
            case nt: NTerminal => nt.cat_
          }.toSet
          val mentionedCats = fromRule ++ fromItems
          mentionedCats.subsetOf(commonExports)
        case _ => true
      }

      val allowedLabels = filteredTerms.collect {
        case rule: Rule => rule.label_.toString
      }

      val commonEquations = presA.equations.toSet intersect presB.equations.toSet
      val filteredEquations = commonEquations.filter { eq =>
        h.labelsInEquation(eq).subsetOf(allowedLabels)
      }

      val commonRewrites = presA.rewrites.toSet intersect presB.rewrites.toSet
      val filteredRewrites = commonRewrites.filter {
        case rdecl: RDecl => h.labelsInRewrite(rdecl.rewrite_).subsetOf(allowedLabels)
        case _ => true
      }

      Presentation(
        exports   = commonExports.toList,
        terms     = filteredTerms.toList,
        equations = filteredEquations.toList,
        rewrites  = filteredRewrites.toList
      )
    }
  }

  def handleAddExports(interpreter: InstInterpreter, env: List[(String, Presentation)], inst: TheoryInstAddExports): Either[String, Presentation] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newCats = inst.listexport_.toArray.toList.collect {
        case base: BaseExport => base.cat_
      }
      basePres.copy(exports = basePres.exports ++ newCats)
    }

  def handleAddReplacements(): Either[String, Presentation] =
    Right(Presentation.empty)

  def handleAddTerms(interpreter: InstInterpreter, env: List[(String, Presentation)], inst: TheoryInstAddTerms): Either[String, Presentation] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newTerms = inst.grammar_ match {
        case g: MkGrammar => g.listdef_.iterator.asScala.toList
        case _ => Nil
      }
      basePres.copy(terms = basePres.terms ++ newTerms)
    }

  def handleAddEquations(interpreter: InstInterpreter, env: List[(String, Presentation)], inst: TheoryInstAddEquations): Either[String, Presentation] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newEquations = inst.listequation_.toArray.toList.collect {
        case eq: Equation => eq
      }
      basePres.copy(equations = basePres.equations ++ newEquations)
    }

  def handleAddRewrites(interpreter: InstInterpreter, env: List[(String, Presentation)], inst: TheoryInstAddRewrites): Either[String, Presentation] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newRewrites = inst.listrewritedecl_.toArray.toList.collect {
        case rd: RewriteDecl => rd
      }
      basePres.copy(rewrites = basePres.rewrites ++ newRewrites)
    }

  def handleCtor(interpreter: InstInterpreter, env: List[(String, Presentation)],
                 resolvedModules: Map[String, Module], currentModulePath: String,
                 ctor: TheoryInstCtor): Either[String, Presentation] = {
    ModuleProcessor.resolveDottedPath(resolvedModules, currentModulePath, ctor.dottedpath_) match {
      case Left(error) => Left(error)
      case Right((modulePath, theoryDecl)) => theoryDecl match {
        case baseDecl: BaseTheoryDecl =>
          if (baseDecl.listvariabledecl_.size != ctor.listtheoryinst_.size)
            Left(s"Mismatch in number of arguments for theory ${baseDecl.name_}")
          else {
            val actuals = ctor.listtheoryinst_.asScala.toList
            interpreter.helpers.sequence(actuals.map(interpreter.interpret(env, _))).flatMap { actualPresentations =>
              val formalsEither = baseDecl.listvariabledecl_.asScala.toList.map {
                case varDecl: VarDecl => Right(varDecl.ident_.toString)
                case _ => Left(s"Non-var declaration in formal parameter list for theory ${baseDecl.name_}")
              }
              interpreter.helpers.sequence(formalsEither).flatMap { formals =>
                val newBindings = formals.zip(actualPresentations)
                new InstInterpreter(resolvedModules, modulePath).interpret(env ++ newBindings, baseDecl.theoryinst_)
              }
            }
          }
        case _ => Left("Resolved theory declaration is not a BaseTheoryDecl")
      }
    }
  }

  def handleRef(env: List[(String, Presentation)], ref: TheoryInstRef): Either[String, Presentation] =
    env.reverse.find(_._1 == ref.ident_) match {
      case Some((_, pres)) => Right(pres)
      case None            => Left(s"Identifier ${ref.ident_} is free")
    }

  def handleRec(interpreter: InstInterpreter, env: List[(String, Presentation)], rec: TheoryInstRec): Either[String, Presentation] =
    interpreter.interpret(env, rec.theoryinst_1).flatMap { pres1 =>
      val envUpdated = env :+ (rec.ident_, pres1)
      interpreter.interpret(envUpdated, rec.theoryinst_2)
    }
}
