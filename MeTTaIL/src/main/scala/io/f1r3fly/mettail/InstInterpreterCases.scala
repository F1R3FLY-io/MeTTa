package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

object InstInterpreterCases {
  import AddEqRwHelpers._
  import ASTHelpers._
  import BasePresOps._
  import LabelHelpers._
  import ModuleProcessor._

  // Distributes List over Either.  If any element is a Left(err),
  //   the result is a Left(err); otherwise, it's a Right(listOfA)
  def sequence[E, A](eithers: List[Either[E, A]]): Either[E, List[A]] =
    eithers.foldRight(Right(Nil): Either[E, List[A]]) { (e, acc) =>
      for {
        x  <- e
        xs <- acc
      } yield x :: xs
    }

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
        labelsInEquation(eq).subsetOf(allowedLabels)
      }

      commonRewrites = presA.listrewritedecl_.asScala.toSet intersect presB.listrewritedecl_.asScala.toSet
      filteredRewrites = commonRewrites.filter {
        case rdecl: RDecl => labelsInRewrite(rdecl.rewrite_).subsetOf(allowedLabels)
        case _ => true
      }
    } yield copyPres(empty,
                     listcat = Some(commonExports.toList),
                     listdef = Some(filteredTerms.toList),
                     listequation = Some(filteredEquations.toList),
                     listrewritedecl = Some(filteredRewrites.toList))
  }

  def handleSubtract(interpreter: InstInterpreter,
                     env: List[(String, BasePres)],
                     subtract: TheoryInstSubtract): Either[String, BasePres] = {
    for {
      bp1 <- interpreter.interpret(env, subtract.theoryinst_1)
      bp2 <- interpreter.interpret(env, subtract.theoryinst_2)
      // Subtract the exported categories
      diffCats = bp1.listcat_.asScala.toSet -- bp2.listcat_.asScala.toSet
      // For definitions, remove any that are in bp2 or that mention a category that was removed.
      diffDefs = bp1.listdef_.asScala.toSet.filter { d =>
        !bp2.listdef_.asScala.toSet.contains(d) &&
        (d match {
           case rule: Rule =>
             val ruleCats = Set(rule.cat_) ++ rule.listitem_.asScala.collect {
               case nt: NTerminal => nt.cat_
             }
             ruleCats.subsetOf(diffCats)
           case _ => true
        })
      }
      // Allowed labels are taken from the surviving Rule definitions.
      allowedLabels = diffDefs.collect { case rule: Rule => rule.label_.toString }
      // For equations, only keep those not in bp2 and whose mentioned labels are among allowedLabels.
      diffEquations = bp1.listequation_.asScala.toSet.filter { eq =>
        !bp2.listequation_.asScala.toSet.contains(eq) &&
        labelsInEquation(eq).subsetOf(allowedLabels)
      }
      // For rewrite declarations, keep only those not in bp2 and whose rewrite’s labels are a subset of allowedLabels.
      diffRewrites = bp1.listrewritedecl_.asScala.toSet.filter { rw =>
        !bp2.listrewritedecl_.asScala.toSet.contains(rw) &&
        (rw match {
           case rdecl: RDecl => labelsInRewrite(rdecl.rewrite_).subsetOf(allowedLabels)
           case _ => true
        })
      }
    } yield copyPres(empty,
                     listcat = Some(diffCats.toList),
                     listdef = Some(diffDefs.toList),
                     listequation = Some(diffEquations.toList),
                     listrewritedecl = Some(diffRewrites.toList))
  }

  def handleAddExports(interpreter: InstInterpreter, env: List[(String, BasePres)], inst: TheoryInstAddExports): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      // Process each export instruction sequentially.
      inst.listexport_.toArray.toList.foldLeft[Either[String, BasePres]](Right(basePres)) { (accEither, expInst) =>
        accEither.flatMap { currentPres =>
          expInst match {
            // For a BaseExport, simply add its Cat to the exports list.
            case base: BaseExport =>
              val updatedCats = currentPres.listcat_.asScala.toList :+ base.cat_
              Right(BasePresOps.copyPres(currentPres, listcat = Some(updatedCats)))
            // For a RenameExport, check that the old Cat is present, then update all occurrences.
            case re: RenameExport =>
              val currentCats = currentPres.listcat_.asScala.toList
              if (!currentCats.exists(cat => cat.equals(re.cat_1))) {
                Left(s"Error: Cannot rename export. Export ${PrettyPrinter.print(re.cat_1)} not found among current exports.")
              } else {
                val updatedCats = currentCats.map(cat => if (cat == re.cat_1) re.cat_2 else re.cat_1)
                val updatedDefs = currentPres.listdef_.asScala.toList.map(d => updateDef(d, re.cat_1, re.cat_2))
                Right(BasePresOps.copyPres(currentPres, listcat = Some(updatedCats), listdef = Some(updatedDefs)))
              }
            case _ =>
              Left("Error: Unknown export type encountered in addExports.")
          }
        }
      }
    }

  def handleAddReplacements(interpreter: InstInterpreter,
                            env: List[(String, BasePres)],
                            inst: TheoryInstAddReplacements): Either[String, BasePres] = {
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      import scala.jdk.CollectionConverters._
      val replacements: List[SimpleRepl] =
        inst.listreplacement_.asScala.toList.collect { case s: SimpleRepl => s }

      def convertIntList(intList: IntList): List[Int] = intList match {
        case ints: Ints => ints.listinteger_.asScala.toList.map(_.intValue())
      }

      // Process each replacement sequentially.
      replacements.foldLeft[Either[String, BasePres]](Right(basePres)) { (accEither, s) =>
        accEither.flatMap { currentPres =>
          // Find the Rule in currentPres whose label matches s.label_.
          val ruleOpt: Option[Rule] =
            currentPres.listdef_.asScala.collect { case r: Rule => r }
              .find(r => r.label_.toString == s.label_.toString)

          ruleOpt match {
            case None =>
              Left(s"Error: No definition found with label ${PrettyPrinter.print(s.label_)} in theory.")

            case Some(rule) =>
              // 1) Category must match
              if (!rule.cat_.equals(s.cat_))
                Left(s"Error: Category mismatch for definition with label ${PrettyPrinter.print(s.label_)}.")
              else {
                // s.def_ must be a Rule
                s.def_ match {
                  case replRule: Rule =>
                    // 2) Duplicate‐label check: the new rule’s label must not collide
                    val existingLabels = currentPres.listdef_.asScala.collect { case r: Rule => r.label_ }
                    val otherLabels    = existingLabels.filterNot(_ == s.label_)
                    if (otherLabels.contains(replRule.label_))
                      Left(
                        s"Error: Replacement rule label " +
                        s"${PrettyPrinter.print(replRule.label_)} already exists in theory."
                      )
                    else {
                      // 3) Arity check
                      val origNTs  = nonTerminals(rule.listitem_)
                      val replNTs  = nonTerminals(replRule.listitem_)
                      if (origNTs.size != replNTs.size)
                        Left(
                          s"Error: Arity mismatch for definition with label ${s.label_}. " +
                          s"Expected ${origNTs.size} non-terminal items but got ${replNTs.size}."
                        )
                      else {
                        val n    = origNTs.size
                        val perm = convertIntList(s.intlist_)
                        // 4) Permutation check
                        if (perm.sorted != (0 until n).toList)
                          Left(
                            s"Error: intlist in replacement for label " +
                            s"${PrettyPrinter.print(s.label_)} is not a permutation of 0 to ${n - 1}."
                          )
                        else {
                          // 5) Category‐alignment check across each position
                          val coordsMatch = (0 until n).forall { j =>
                            origNTs(j) == replNTs(perm(j))
                          }
                          if (!coordsMatch)
                            Left(
                              s"Error: Category mismatch among non-terminal items in replacement " +
                              s"for label ${PrettyPrinter.print(s.label_)}."
                            )
                          else {
                            // All OK: install the new rule
                            val newDefs = currentPres.listdef_.asScala.toList.map {
                              case r: Rule if r.label_.toString == s.label_.toString => replRule
                              case other                                             => other
                            }
                            Right(copyPres(currentPres, listdef = Some(newDefs)))
                          }
                        }
                      }
                    }

                  case _ =>
                    Left(
                      s"Error: Replacement definition for label ${PrettyPrinter.print(s.label_)} is not a Rule."
                    )
                }
              }
          }
        }
      }
    }
  }

  def handleAddTerms(
    interpreter: InstInterpreter,
    env: List[(String, BasePres)],
    inst: TheoryInstAddTerms
  ): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      // Extract the incoming list of Defs (only Rules matter here)
      val newTerms: List[Def] = inst.grammar_ match {
        case g: MkGrammar => g.listdef_.iterator.asScala.toList
        case _            => Nil
      }
      // Allowed categories come from the original BasePres
      val allowedCats: Set[Cat] = basePres.listcat_.asScala.toSet

      // Fold over newTerms, starting with Right(basePres)
      newTerms.foldLeft[Either[String, BasePres]](Right(basePres)) {
        case (Left(err), _) => Left(err)  // once an error, keep propagating
        case (Right(bp), term) => term match {
          case rule: Rule =>
            // 1) Unknown‑category check
            val fromRule  = Set(rule.cat_)
            val fromItems = rule.listitem_.asScala.collect { case nt: NTerminal => nt.cat_ }.toSet
            val mentioned = fromRule ++ fromItems
            if (!mentioned.subsetOf(allowedCats)) {
              val unknown = mentioned.diff(allowedCats).map(PrettyPrinter.print)
              Left(s"Error: Def in addTerms mentions unknown categories: $unknown")
            }
            // 2) Duplicate‑label check
            else if (bp.listdef_.asScala.collect { case r: Rule => r.label_ }.contains(rule.label_)) {
              Left(s"Error: Duplicate label in addTerms: ${PrettyPrinter.print(rule.label_)}")
            }
            // 3) Special List‑label check
            else {
              rule.label_ match {
                case l: ListE    if rule.cat_ != ListOfCat(l.cat_) =>
                  Left(s"Error: Category for []{${rule.cat_}} must be [${rule.cat_}]")
                case l: ListCons if rule.cat_ != ListOfCat(l.cat_) =>
                Left(s"Error: Category for (:){${rule.cat_}} must be [${rule.cat_}]")
                case l: ListOne  if rule.cat_ != ListOfCat(l.cat_) =>
                Left(s"Error: Category for (:[]){${rule.cat_}} must be [${rule.cat_}]")
                case _ =>
                  // All checks pass: append this rule and continue
                  Right(copyPres(bp, listdef = Some(bp.listdef_.asScala.toList :+ rule)))
              }
            }

          case _ =>
            // Non‑Rule defs (e.g. Comments) are ignored
            Right(bp)
        }
      }
    }

  def handleAddEquations(interpreter: InstInterpreter,
                          env: List[(String, BasePres)],
                          inst: TheoryInstAddEquations): Either[String, BasePres] = {
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      val defs: Map[Label, Rule] = listDefToMap(basePres.listdef_)
      inst.listequation_.asScala.toList.foldLeft[Either[String, BasePres]](
        Right(basePres)
      ) { (basePres, e) =>
        val pretty = s"equation ${PrettyPrinter.print(e)}"

        // Check validity of equations as follows
        for {
          bp <- basePres
          eqn = equationImpl(e)
          // 1. The two sides of the equation have the same category
          //    OR one has a category and the other is a top-level variable.
          _ <- sameCategory(catOfAST(eqn.ast_1, defs), catOfAST(eqn.ast_2, defs), pretty)
          // 2. Check that each variable has a consistent category
          //    Check that the vars on the left are consistent.
          m1 <- consistentCategory(eqn.ast_1, defs, pretty)
          //    Check that the vars on the right are consistent.
          m2 <- consistentCategory(eqn.ast_2, defs, pretty)
          //    Check that the both sides are consistent with each other.
          allVars = m1.keySet ++ m2.keySet
          _ <- allVars.foldLeft[Either[String, Unit]](Right(())) { (acc, ident) =>
            (m1.get(ident), m2.get(ident)) match {
              case (Some(l), Some(r)) if l != r =>
                Left(s"Variable ${ident} has category ${PrettyPrinter.print(l)} on the left-"
                     + s"hand side and category ${PrettyPrinter.print(r)} on the right-hand"
                     + s" side of $pretty")
              case _ => acc
            }
          }

        } yield copyPres(
          bp,
          listequation = Some(bp.listequation_.asScala.toList :+ e)
        )
      }
    }
  }

  def handleAddRewrites(interpreter: InstInterpreter,
                        env: List[(String, BasePres)],
                        inst: TheoryInstAddRewrites): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      val defs: Map[Label, Rule] = listDefToMap(basePres.listdef_)

      // Extract the new rewrite declarations from the instruction.
      inst.listrewritedecl_.asScala.foldLeft[Either[String, BasePres]](
        Right(basePres)
      ) { (basePres, rewriteDecl) =>
        val rw = rewrite(rewriteDecl)
        val rb = rewriteBase(rw)
        val pretty = s"rewrite ${PrettyPrinter.print(rewriteDecl)}"

        // Check validity of rewrites as follows
        for {
          // 1. The two sides of the rewrite have the same category
          //    OR one has a category and the other is a top-level variable.
          _ <- sameCategory(catOfAST(rb.ast_1, defs), catOfAST(rb.ast_2, defs), pretty)
          // 2. Check that each variable has a consistent category
          //    Check that the vars on the left are consistent.
          m1 <- consistentCategory(rb.ast_1, defs, pretty)
          //    Check that the vars on the right are consistent.
          m2 <- consistentCategory(rb.ast_2, defs, pretty)
          //    Check that the both sides are consistent with each other.
          allVars = m1.keySet ++ m2.keySet
          _ <- allVars.foldLeft[Either[String, Unit]](Right(())) { (acc, ident) =>
            (m1.get(ident), m2.get(ident)) match {
              case (Some(l), Some(r)) if l != r =>
                Left(s"Variable ${ident} has category ${PrettyPrinter.print(l)} on the left-"
                     + s"hand side and category ${PrettyPrinter.print(r)} on the right-hand"
                     + s" side of $pretty")
              case _ => acc
            }
          }
          // 3. Check each rewrite declaration to ensure that
          //    every variable on the right appears on the left.
          lVars = leftVars(rw)
          rVars = rightVars(rw)
          missingVars = rVars diff lVars
          _ <- Either.cond(
            missingVars.isEmpty,
            (),
            "Error: In RewriteDecl, variables on the right-hand side"
              + s" not found on the left-hand side: $missingVars"
          )

          // 4. When the Rewrite is a RewriteContext let Src ~> Tgt in r,
          //    Src must appear only on the left, Tgt must appear only on the right,
          //    and the category of Src must match the category of Tgt
          _ <- checkHypotheticals(hypVars(rw), defs, rb)

          bp <- basePres
        } yield copyPres(
          bp,
          listrewritedecl = Some(bp.listrewritedecl_.asScala.toList :+ rewriteDecl)
        )
      }
    }

  def handleCtor(
    interpreter: InstInterpreter,
    env: List[(String, BasePres)],
    resolvedModules: Map[String, Module],
    currentModulePath: String,
    ctor: TheoryInstCtor,
    moduleProcessor: ModuleProcessor
  ): Either[String, BasePres] = {
    moduleProcessor.resolveDottedPath(resolvedModules, currentModulePath, ctor.dottedpath_) match {
      case Left(error) => Left(error)
      case Right((modulePath, theoryDecl)) => theoryDecl match {
        case baseDecl: BaseTheoryDecl =>
          if (baseDecl.listvariabledecl_.size != ctor.listtheoryinst_.size)
            Left(s"Mismatch in number of arguments for theory ${PrettyPrinter.print(baseDecl.name_)}")
          else {
            val actuals = ctor.listtheoryinst_.asScala.toList
            sequence(actuals.map(interpreter.interpret(env, _))).flatMap { actualPresentations =>
              val formalsEither = baseDecl.listvariabledecl_.asScala.toList.map {
                case varDecl: VarDecl => Right(varDecl.ident_.toString)
                case _ => Left(s"Non-var declaration in formal parameter list"
                               + s" for theory ${PrettyPrinter.print(baseDecl.name_)}")
              }
              sequence(formalsEither).flatMap { formals =>
                val newBindings = formals.zip(actualPresentations)
                new InstInterpreter(
                  resolvedModules,
                  modulePath,
                  moduleProcessor
                ).interpret(env ++ newBindings, baseDecl.theoryinst_)
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
