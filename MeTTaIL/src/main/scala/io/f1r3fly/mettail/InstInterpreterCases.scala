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
        case rule: Rule => labelToString(rule.label_)
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
      allowedLabels = diffDefs.collect { case rule: Rule => labelToString(rule.label_) }
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

  def checkAddExports(
                      interpreter: InstInterpreter,
                      env: List[(String, BasePres)],
                      inst: TheoryInstAddExports
                     ): Option[String] =
    interpreter.interpret(env, inst.theoryinst_).toOption.flatMap { basePres =>
      if (inst.listexport_.size < 1) {
        Some("Error: missing distinguished export.")
      } else {
        inst.listexport_
          .toArray
          .toList
          .collectFirst {
            case re: RenameExport =>
              val currentCats = basePres.listcat_.asScala.toList
              if (!currentCats.exists(_.equals(re.cat_1))) {
                Some(s"Error: Cannot rename export. Export ${PrettyPrinter.print(re.cat_1)} not found among current exports.")
              } else {
                None
              }
            case _ =>
              Some("Error: Unknown export type encountered in addExports.")
          }.flatten
      }
    }

  def handleAddExports(
                        interpreter: InstInterpreter,
                        env: List[(String, BasePres)],
                        inst: TheoryInstAddExports
                      ): Either[String, BasePres] = {
    val basePres = interpreter.interpret(env, inst.theoryinst_).right.get
    inst.listexport_.toArray.toList.foldLeft[Either[String, BasePres]](Right(basePres)) {
      (accEither, expInst) =>
        val currentPres = accEither.right.get

        expInst match {
          case base: BaseExport =>
            val updatedCats = currentPres.listcat_.asScala.toList :+ base.cat_
            Right(BasePresOps.copyPres(currentPres, listcat = Some(updatedCats)))

          case re: RenameExport =>
            val currentCats = currentPres.listcat_.asScala.toList
            val updatedCats = currentCats.map(cat => if (cat == re.cat_1) re.cat_2 else cat)
            val updatedDefs = currentPres.listdef_.asScala.toList.map(d => updateDef(d, re.cat_1, re.cat_2))
            Right(BasePresOps.copyPres(currentPres, listcat = Some(updatedCats), listdef = Some(updatedDefs)))
        }
    }
  }

  def checkAddReplacements(
                                    interpreter: InstInterpreter,
                                    env: List[(String, BasePres)],
                                    inst: TheoryInstAddReplacements
                                  ): Option[String] = {
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      import scala.jdk.CollectionConverters._
      val replacements: List[SimpleRepl] =
        inst.listreplacement_.asScala.toList.collect { case s: SimpleRepl => s }

      def convertIntList(intList: IntList): List[Int] = intList match {
        case ints: Ints => ints.listinteger_.asScala.toList.map(_.intValue())
      }

      replacements.foldLeft[Either[String, BasePres]](Right(basePres)) { (accEither, s) =>
        accEither.flatMap { currentPres =>
          val ruleOpt: Option[Rule] =
            currentPres.listdef_.asScala.collect { case r: Rule => r }
              .find(r => labelToString(r.label_) == labelToString(s.label_))

          ruleOpt match {
            case None =>
              Left(s"Error: No definition found with label ${PrettyPrinter.print(s.label_)} in theory.")

            case Some(rule) =>
              if (!rule.cat_.equals(s.cat_))
                Left(s"Error: Category mismatch for definition with label ${PrettyPrinter.print(s.label_)}.")
              else {
                s.def_ match {
                  case replRule: Rule =>
                    val existingLabels = currentPres.listdef_.asScala.collect { case r: Rule => r.label_ }
                    val otherLabels    = existingLabels.filterNot(_ == s.label_)
                    if (otherLabels.contains(replRule.label_))
                      Left(
                        s"Error: Replacement rule label " +
                          s"${PrettyPrinter.print(replRule.label_)} already exists in theory."
                      )
                    else {
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
                        if (perm.sorted != (0 until n).toList)
                          Left(
                            s"Error: intlist in replacement for label " +
                              s"${PrettyPrinter.print(s.label_)} is not a permutation of 0 to ${n - 1}."
                          )
                        else {
                          val coordsMatch = (0 until n).forall { j =>
                            origNTs(j) == replNTs(perm(j))
                          }
                          if (!coordsMatch)
                            Left(
                              s"Error: Category mismatch among non-terminal items in replacement " +
                                s"for label ${PrettyPrinter.print(s.label_)}."
                            )
                          else {
                            val newDefs = currentPres.listdef_.asScala.toList.map {
                              case r: Rule if labelToString(r.label_) == labelToString(s.label_) => replRule
                              case other => other
                            }

                            def updateAST(ast: AST): AST = ast match {
                              case sexp: ASTSExp =>
                                val newArgs = sexp.listast_.asScala.map(updateAST).toList
                                if (labelToString(sexp.label_) == labelToString(s.label_)) {
                                  val permuted = perm.map(newArgs(_))
                                  val newListAST = new ListAST()
                                  newListAST.addAll(permuted.asJava)
                                  new ASTSExp(replRule.label_, newListAST)
                                } else {
                                  val newListAST = new ListAST()
                                  newListAST.addAll(newArgs.asJava)
                                  new ASTSExp(sexp.label_, newListAST)
                                }

                              case sub: ASTSubst =>
                                new ASTSubst(updateAST(sub.ast_1), updateAST(sub.ast_2), sub.ident_)

                              case other => other
                            }

                            def updateEquation(eq: Equation): Equation = eq match {
                              case ef: EquationFresh =>
                                new EquationFresh(
                                  ef.ident_1,
                                  ef.ident_2,
                                  updateEquation(ef.equation_)
                                )
                              case impl: EquationImpl =>
                                new EquationImpl(updateAST(impl.ast_1), updateAST(impl.ast_2))
                            }

                            val newEquations = currentPres.listequation_.asScala.toList.map(updateEquation)

                            def updateRewrite(r: Rewrite): Rewrite = r match {
                              case rb: RewriteBase =>
                                new RewriteBase(updateAST(rb.ast_1), updateAST(rb.ast_2))

                              case ctx: RewriteContext =>
                                new RewriteContext(ctx.hypothesis_, updateRewrite(ctx.rewrite_))

                              case other => other
                            }

                            val newRewrites = currentPres.listrewritedecl_.asScala.toList.map { rd =>
                              val rdecl = rd.asInstanceOf[RDecl]
                              new RDecl(rdecl.ident_, updateRewrite(rdecl.rewrite_))
                            }

                            Right(BasePresOps.copyPres(
                              currentPres,
                              listdef        = Some(newDefs),
                              listequation   = Some(newEquations),
                              listrewritedecl= Some(newRewrites)
                            ))
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
    }.left.toOption
  }

  def handleAddReplacements(
                             interpreter: InstInterpreter,
                             env: List[(String, BasePres)],
                             inst: TheoryInstAddReplacements
                           ): Either[String, BasePres] = Right {
    import scala.jdk.CollectionConverters._
    val basePres = interpreter.interpret(env, inst.theoryinst_).right.get
    val replacements: List[SimpleRepl] =
      inst.listreplacement_.asScala.toList.collect { case s: SimpleRepl => s }
    def convertIntList(intList: IntList): List[Int] = intList match {
      case ints: Ints => ints.listinteger_.asScala.toList.map(_.intValue())
    }
    replacements.foldLeft(basePres) { (currentPres, s) =>
      val rule = currentPres.listdef_.asScala.collect { case r: Rule => r }
        .find(r => labelToString(r.label_) == labelToString(s.label_)).get
      val replRule = s.def_.asInstanceOf[Rule]
      val origNTs = nonTerminals(rule.listitem_)
      val replNTs = nonTerminals(replRule.listitem_)
      val perm    = convertIntList(s.intlist_)
      val newDefs = currentPres.listdef_.asScala.toList.map {
        case r: Rule if labelToString(r.label_) == labelToString(s.label_) => replRule
        case other => other
      }

      def updateAST(ast: AST): AST = ast match {
        case sexp: ASTSExp =>
          val newArgs = sexp.listast_.asScala.map(updateAST).toList
          if (labelToString(sexp.label_) == labelToString(s.label_)) {
            val permuted = perm.map(newArgs(_))
            val newListAST = new ListAST()
            newListAST.addAll(permuted.asJava)
            new ASTSExp(replRule.label_, newListAST)
          } else {
            val newListAST = new ListAST()
            newListAST.addAll(newArgs.asJava)
            new ASTSExp(sexp.label_, newListAST)
          }

        case sub: ASTSubst =>
          new ASTSubst(updateAST(sub.ast_1), updateAST(sub.ast_2), sub.ident_)

        case other => other
      }

      def updateEquation(eq: Equation): Equation = eq match {
        case ef: EquationFresh =>
          new EquationFresh(ef.ident_1, ef.ident_2, updateEquation(ef.equation_))
        case impl: EquationImpl =>
          new EquationImpl(updateAST(impl.ast_1), updateAST(impl.ast_2))
      }

      val newEquations = currentPres.listequation_.asScala.toList.map(updateEquation)

      def updateRewrite(r: Rewrite): Rewrite = r match {
        case rb: RewriteBase =>
          new RewriteBase(updateAST(rb.ast_1), updateAST(rb.ast_2))
        case ctx: RewriteContext =>
          new RewriteContext(ctx.hypothesis_, updateRewrite(ctx.rewrite_))
        case other => other
      }

      val newRewrites = currentPres.listrewritedecl_.asScala.toList.map { rd =>
        val rdecl = rd.asInstanceOf[RDecl]
        new RDecl(rdecl.ident_, updateRewrite(rdecl.rewrite_))
      }

      BasePresOps.copyPres(
        currentPres,
        listdef         = Some(newDefs),
        listequation    = Some(newEquations),
        listrewritedecl = Some(newRewrites)
      )
    }
  }

  def checkAddTerms(
                     interpreter: InstInterpreter,
                     env: List[(String, BasePres)],
                     inst: TheoryInstAddTerms
                   ): Option[String] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      val newTerms: List[Def] = inst.grammar_ match {
        case g: MkGrammar => g.listdef_.iterator.asScala.toList
        case _            => Nil
      }
      val allowedCats: Set[Cat] = basePres.listcat_.asScala.toSet

      newTerms.foldLeft[Either[String, BasePres]](Right(basePres)) {
        case (Left(err), _) => Left(err)
        case (Right(bp), term) => term match {
          case rule: Rule =>
            val fromRule  = Set(rule.cat_)
            val fromItems = rule.listitem_.asScala.collect { case nt: NTerminal => nt.cat_ }.toSet
            val mentioned = fromRule ++ fromItems
            if (!mentioned.subsetOf(allowedCats)) {
              val unknown = mentioned.diff(allowedCats).map(PrettyPrinter.print)
              Left(s"Error: Def in addTerms mentions unknown categories: $unknown")
            } else if (bp.listdef_.asScala.collect { case r: Rule => r.label_ }.contains(rule.label_)) {
              Left(s"Error: Duplicate label in addTerms: ${PrettyPrinter.print(rule.label_)}")
            } else {
              rule.label_ match {
                case l: ListE    if rule.cat_ != ListOfCat(l.cat_) =>
                  Left(s"Error: Category for []{${rule.cat_}} must be [${rule.cat_}]")
                case l: ListCons if rule.cat_ != ListOfCat(l.cat_) =>
                  Left(s"Error: Category for (:){${rule.cat_}} must be [${rule.cat_}]")
                case l: ListOne  if rule.cat_ != ListOfCat(l.cat_) =>
                  Left(s"Error: Category for (:[]){${rule.cat_}} must be [${rule.cat_}]")
                case _ =>
                  Right(copyPres(bp, listdef = Some(bp.listdef_.asScala.toList :+ rule)))
              }
            }

          case _ =>
            Right(bp)
        }
      }
    }.left.toOption

  def handleAddTerms(
                      interpreter: InstInterpreter,
                      env: List[(String, BasePres)],
                      inst: TheoryInstAddTerms
                    ): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).map { basePres =>
      val newTerms: List[Def] = inst.grammar_ match {
        case g: MkGrammar => g.listdef_.iterator.asScala.toList
        case _            => Nil
      }
      val updatedDefs = basePres.listdef_.asScala.toList ++ newTerms.collect {
        case rule: Rule => rule
      }
      copyPres(basePres, listdef = Some(updatedDefs))
    }

  def checkAddEquations(interpreter: InstInterpreter,
                        env: List[(String, BasePres)],
                        inst: TheoryInstAddEquations): Option[String] = {
    interpreter.interpret(env, inst.theoryinst_) match {
      case Left(err) => Some(err)
      case Right(basePres) =>
        val defs: Map[Label, Rule] = listDefToMap(basePres.listdef_)
        inst.listequation_.asScala.toList.foldLeft[Option[String]](None) {
          case (Some(err), _) => Some(err) // short-circuit on first error
          case (None, e) =>
            val pretty = s"equation ${PrettyPrinter.print(e)}"
            val eqn = equationImpl(e)

            for {
              _ <- sameCategory(catOfAST(eqn.ast_1, defs), catOfAST(eqn.ast_2, defs), pretty).left.toOption
              m1 <- consistentCategory(eqn.ast_1, defs, pretty).toOption
              m2 <- consistentCategory(eqn.ast_2, defs, pretty).toOption
              err <- (m1.keySet ++ m2.keySet).foldLeft[Option[String]](None) {
                case (Some(e), _) => Some(e)
                case (None, ident) =>
                  (m1.get(ident), m2.get(ident)) match {
                    case (Some(l), Some(r)) if l != r =>
                      Some(s"Variable ${ident} has category ${PrettyPrinter.print(l)} on the left-" +
                        s"hand side and category ${PrettyPrinter.print(r)} on the right-hand" +
                        s" side of $pretty")
                    case _ => None
                  }
              }
            } yield err
        }
    }
  }

  def handleAddEquations(interpreter: InstInterpreter,
                         env: List[(String, BasePres)],
                         inst: TheoryInstAddEquations): Either[String, BasePres] = {
    Right {
      val basePres = interpreter.interpret(env, inst.theoryinst_).right.get
      val defs: Map[Label, Rule] = listDefToMap(basePres.listdef_)
      inst.listequation_.asScala.toList.foldLeft(basePres) { (bp, e) =>
        val pretty = s"equation ${PrettyPrinter.print(e)}"
        val eqn = equationImpl(e)
        sameCategory(catOfAST(eqn.ast_1, defs), catOfAST(eqn.ast_2, defs), pretty).right.get
        val m1 = consistentCategory(eqn.ast_1, defs, pretty).right.get
        val m2 = consistentCategory(eqn.ast_2, defs, pretty).right.get
        val allVars = m1.keySet ++ m2.keySet
        allVars.foreach { ident =>
          (m1.get(ident), m2.get(ident)) match {
            case (Some(l), Some(r)) if l != r =>
            // Previously returned Left with error message, now ignored
            case _ => ()
          }
        }
        copyPres(bp, listequation = Some(bp.listequation_.asScala.toList :+ e))
      }
    }
  }

  def checkAddRewrites(interpreter: InstInterpreter,
                       env: List[(String, BasePres)],
                       inst: TheoryInstAddRewrites): Option[String] = {
    interpreter.interpret(env, inst.theoryinst_) match {
      case Left(err) => Some(err)
      case Right(basePres) =>
        val defs: Map[Label, Rule] = listDefToMap(basePres.listdef_)
        inst.listrewritedecl_.asScala.foldLeft[Option[String]](None) {
          case (Some(err), _) => Some(err) // short-circuit on first error
          case (None, rewriteDecl) =>
            val rw = rewrite(rewriteDecl)
            val rb = rewriteBase(rw)
            val pretty = s"rewrite ${PrettyPrinter.print(rewriteDecl)}"

            for {
              _ <- sameCategory(catOfAST(rb.ast_1, defs), catOfAST(rb.ast_2, defs), pretty).left.toOption
              m1 <- consistentCategory(rb.ast_1, defs, pretty).toOption
              m2 <- consistentCategory(rb.ast_2, defs, pretty).toOption
              _ <- (m1.keySet ++ m2.keySet).foldLeft[Option[String]](None) {
                case (Some(e), _) => Some(e)
                case (None, ident) =>
                  (m1.get(ident), m2.get(ident)) match {
                    case (Some(l), Some(r)) if l != r =>
                      Some(s"Variable ${ident} has category ${PrettyPrinter.print(l)} on the left-" +
                        s"hand side and category ${PrettyPrinter.print(r)} on the right-hand" +
                        s" side of $pretty")
                    case _ => None
                  }
              }
              lVars = leftVars(rw)
              rVars = rightVars(rw)
              missingVars = rVars diff lVars
              _ <- Option.when(missingVars.nonEmpty)(
                "Error: In RewriteDecl, variables on the right-hand side" +
                  s" not found on the left-hand side: $missingVars"
              )
              _ <- checkHypotheticals(hypVars(rw), defs, rb).left.toOption
            } yield pretty // returning the first failing rewrite description
        }
    }
  }

  def handleAddRewrites(
                       interpreter: InstInterpreter,
                       env: List[(String, BasePres)],
                       inst: TheoryInstAddRewrites
                     ): Either[String, BasePres] = {
  interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
    val defs: Map[Label, Rule] = listDefToMap(basePres.listdef_)

    inst.listrewritedecl_.asScala.foldLeft[Either[String, BasePres]](Right(basePres)) {
      (accEither, rewriteDecl) =>
        accEither.flatMap { currentPres =>
          val rw = rewrite(rewriteDecl)
          val rb = rewriteBase(rw)
          for {
            _ <- sameCategory(catOfAST(rb.ast_1, defs), catOfAST(rb.ast_2, defs), "")
            _ <- consistentCategory(rb.ast_1, defs, "")
            _ <- consistentCategory(rb.ast_2, defs, "")
            _ <- checkHypotheticals(hypVars(rw), defs, rb)
          } yield copyPres(
            currentPres,
            listrewritedecl = Some(currentPres.listrewritedecl_.asScala.toList :+ rewriteDecl)
          )
        }
      }
    }
  }

  def checkCtor(
                  interpreter: InstInterpreter,
                  env: List[(String, BasePres)],
                  resolvedModules: Map[String, Module],
                  currentModulePath: String,
                  ctor: TheoryInstCtor,
                  moduleProcessor: ModuleProcessor
                ): Option[String] = {

    moduleProcessor.resolveDottedPath(resolvedModules, currentModulePath, ctor.dottedpath_) match {
      case Left(error) => Some(error)
      case Right((modulePath, theoryDecl)) => theoryDecl match {
        case baseDecl: BaseTheoryDecl =>
          if (baseDecl.listvariabledecl_.size != ctor.listtheoryinst_.size)
            Some(s"Mismatch in number of arguments for theory ${PrettyPrinter.print(baseDecl.name_)}")
          else {
            val actuals = ctor.listtheoryinst_.asScala.toList
            sequence(actuals.map(interpreter.interpret(env, _))) match {
              case Left(err) => Some(err)
              case Right(actualPresentations) =>
                val formalsEither = baseDecl.listvariabledecl_.asScala.toList.map {
                  case varDecl: VarDecl => Right(varDecl.ident_.toString)
                  case _ => Left(
                    s"Non-var declaration in formal parameter list for theory ${PrettyPrinter.print(baseDecl.name_)}"
                  )
                }
                sequence(formalsEither) match {
                  case Left(err) => Some(err)
                  case Right(formals) =>
                    val newBindings = formals.zip(actualPresentations)
                    new InstInterpreter(
                      resolvedModules,
                      modulePath,
                      moduleProcessor
                    ).check_interpret(env ++ newBindings, baseDecl.theoryinst_)
                }
            }
          }
        case _ => Some("Resolved theory declaration is not a BaseTheoryDecl")
      }
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
    val (modulePath, theoryDecl) =
      moduleProcessor.resolveDottedPath(resolvedModules, currentModulePath, ctor.dottedpath_).right.get
    val baseDecl = theoryDecl.asInstanceOf[BaseTheoryDecl]

    val actuals = ctor.listtheoryinst_.asScala.toList
    val actualPresentations = sequence(actuals.map(interpreter.interpret(env, _))).right.get
    val formals = baseDecl.listvariabledecl_.asScala.toList.map(_.asInstanceOf[VarDecl].ident_.toString)
    val newBindings = formals.zip(actualPresentations)
    new InstInterpreter(
      resolvedModules,
      modulePath,
      moduleProcessor
    ).interpret(env ++ newBindings, baseDecl.theoryinst_)
  }

  def checkRef(env: List[(String, BasePres)], ref: TheoryInstRef): Option[String] =
    env.reverse.find(_._1 == ref.ident_) match {
      case Some((_, pres)) => None
      case None            => Some(s"Identifier ${ref.ident_} is free")
    }

  def handleRef(env: List[(String, BasePres)], ref: TheoryInstRef): Either[String, BasePres] =
    Right(env.reverse.find(_._1 == ref.ident_).get._2)

  def handleRec(interpreter: InstInterpreter, env: List[(String, BasePres)], rec: TheoryInstRec): Either[String, BasePres] =
    interpreter.interpret(env, rec.theoryinst_1).flatMap { pres1 =>
      val envUpdated = env :+ (rec.ident_, pres1)
      interpreter.interpret(envUpdated, rec.theoryinst_2)
    }
}
