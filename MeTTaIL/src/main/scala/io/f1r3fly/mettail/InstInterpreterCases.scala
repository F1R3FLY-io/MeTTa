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

  object BasePresOps {
    import scala.jdk.CollectionConverters._

    // Create an empty instance by calling the no-argument constructors.
    def empty: BasePres = {
      val listCat = new metta_venus.Absyn.ListCat()
      val listDef = new metta_venus.Absyn.ListDef()
      val listEquation = new metta_venus.Absyn.ListEquation()
      val listRewriteDecl = new metta_venus.Absyn.ListRewriteDecl()
      new BasePres(listCat, listDef, listEquation, listRewriteDecl)
    }

    // copyPres creates new list instances and adds the updated elements.
    def copyPres(
      pres: BasePres,
      listcat: Option[List[Cat]] = None,
      listdef: Option[List[Def]] = None,
      listequation: Option[List[Equation]] = None,
      listrewritedecl: Option[List[RewriteDecl]] = None
    ): BasePres = {
      val newListCat = new metta_venus.Absyn.ListCat()
      val newListDef = new metta_venus.Absyn.ListDef()
      val newListEquation = new metta_venus.Absyn.ListEquation()
      val newListRewriteDecl = new metta_venus.Absyn.ListRewriteDecl()

      val cats = listcat.getOrElse(pres.listcat_.asScala.toList)
      newListCat.addAll(cats.asJava)
      val defs = listdef.getOrElse(pres.listdef_.asScala.toList)
      newListDef.addAll(defs.asJava)
      val equations = listequation.getOrElse(pres.listequation_.asScala.toList)
      newListEquation.addAll(equations.asJava)
      val rewrites = listrewritedecl.getOrElse(pres.listrewritedecl_.asScala.toList)
      newListRewriteDecl.addAll(rewrites.asJava)

      new BasePres(newListCat, newListDef, newListEquation, newListRewriteDecl)
    }
  }

  import BasePresOps._

  def handleRest(): Either[String, BasePres] =
    Right(empty)

  def handleSub(): Either[String, BasePres] =
    Right(empty)

  def handleEmpty(): Either[String, BasePres] =
    Right(empty)

  def handleFree(): Either[String, BasePres] =
    Right(empty)

  def handleDisj(interpreter: InstInterpreter, env: List[(String, BasePres)], disj: TheoryInstDisj): Either[String, BasePres] =
    for {
      presA <- interpreter.interpret(env, disj.theoryinst_1)
      presB <- interpreter.interpret(env, disj.theoryinst_2)
      exports   = (presA.listcat_.asScala.toList ++ presB.listcat_.asScala.toList).distinct
      terms     = (presA.listdef_.asScala.toList ++ presB.listdef_.asScala.toList).distinct
      equations = (presA.listequation_.asScala.toList ++ presB.listequation_.asScala.toList).distinct
      rewrites  = (presA.listrewritedecl_.asScala.toList ++ presB.listrewritedecl_.asScala.toList).distinct
    } yield copyPres(empty,
                     listcat = Some(exports),
                     listdef = Some(terms),
                     listequation = Some(equations),
                     listrewritedecl = Some(rewrites))

  def handleConj(interpreter: InstInterpreter, env: List[(String, BasePres)], conj: TheoryInstConj): Either[String, BasePres] = {
    val h = interpreter.helpers
    for {
      presA <- interpreter.interpret(env, conj.theoryinst_1)
      presB <- interpreter.interpret(env, conj.theoryinst_2)
      commonExports = presA.listcat_.asScala.toSet intersect presB.listcat_.asScala.toSet
      commonTerms   = presA.listdef_.asScala.toSet intersect presB.listdef_.asScala.toSet

      filteredTerms = commonTerms.filter {
        case rule: Rule =>
          val fromRule  = Set(rule.cat_)
          val fromItems = rule.listitem_.asScala.collect {
            case nt: NTerminal => nt.cat_
          }.toSet
          val mentionedCats = fromRule ++ fromItems
          mentionedCats.subsetOf(commonExports)
        case _ => true
      }

      allowedLabels = filteredTerms.collect {
        case rule: Rule => rule.label_.toString
      }

      commonEquations = presA.listequation_.asScala.toSet intersect presB.listequation_.asScala.toSet
      filteredEquations = commonEquations.filter { eq =>
        h.labelsInEquation(eq).subsetOf(allowedLabels)
      }

      commonRewrites = presA.listrewritedecl_.asScala.toSet intersect presB.listrewritedecl_.asScala.toSet
      filteredRewrites = commonRewrites.filter {
        case rdecl: RDecl => h.labelsInRewrite(rdecl.rewrite_).subsetOf(allowedLabels)
        case _ => true
      }
    } yield copyPres(empty,
                     listcat = Some(commonExports.toList),
                     listdef = Some(filteredTerms.toList),
                     listequation = Some(filteredEquations.toList),
                     listrewritedecl = Some(filteredRewrites.toList))
  }

  def handleAddExports(interpreter: InstInterpreter, env: List[(String, BasePres)], inst: TheoryInstAddExports): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newCats = inst.listexport_.toArray.toList.collect {
        case base: BaseExport => base.cat_
      }
      copyPres(basePres, listcat = Some(basePres.listcat_.asScala.toList ++ newCats))
    }

  def handleAddReplacements(): Either[String, BasePres] =
    Right(empty)

  def handleAddTerms(interpreter: InstInterpreter, env: List[(String, BasePres)], inst: TheoryInstAddTerms): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newTerms = inst.grammar_ match {
        case g: MkGrammar => g.listdef_.iterator.asScala.toList
        case _ => Nil
      }
      copyPres(basePres, listdef = Some(basePres.listdef_.asScala.toList ++ newTerms))
    }

  def handleAddEquations(interpreter: InstInterpreter, env: List[(String, BasePres)], inst: TheoryInstAddEquations): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newEquations = inst.listequation_.toArray.toList.collect {
        case eq: Equation => eq
      }
      copyPres(basePres, listequation = Some(basePres.listequation_.asScala.toList ++ newEquations))
    }

  def handleAddRewrites(interpreter: InstInterpreter, env: List[(String, BasePres)], inst: TheoryInstAddRewrites): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newRewrites = inst.listrewritedecl_.toArray.toList.collect {
        case rd: RewriteDecl => rd
      }
      copyPres(basePres, listrewritedecl = Some(basePres.listrewritedecl_.asScala.toList ++ newRewrites))
    }

  def handleCtor(interpreter: InstInterpreter, env: List[(String, BasePres)],
                 resolvedModules: Map[String, Module], currentModulePath: String,
                 ctor: TheoryInstCtor): Either[String, BasePres] = {
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

  def handleRef(env: List[(String, BasePres)], ref: TheoryInstRef): Either[String, BasePres] =
    env.reverse.find(_._1 == ref.ident_) match {
      case Some((_, pres)) => Right(pres)
      case None            => Left(s"Identifier ${ref.ident_} is free")
    }

  def handleRec(interpreter: InstInterpreter, env: List[(String, BasePres)], rec: TheoryInstRec): Either[String, BasePres] =
    interpreter.interpret(env, rec.theoryinst_1).flatMap { pres1 =>
      val envUpdated = env :+ (rec.ident_, pres1)
      interpreter.interpret(envUpdated, rec.theoryinst_2)
    }
}
