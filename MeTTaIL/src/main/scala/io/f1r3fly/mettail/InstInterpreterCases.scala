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

  def labelToString(l: Label): String = l match {
    case id: Id => id.ident_
    case _: Wild => "_"
    case _: ListE => "[]"
    case _: ListCons => "(:)"
    case _: ListOne => "(:[])"
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

  // Helper: If the given Cat equals oldCat, replace it with newCat.
  def updateCat(cat: Cat, oldCat: Cat, newCat: Cat): Cat =
    if (cat.equals(oldCat)) newCat else cat

  // Helper: Update an NTerminal by replacing its contained Cat if needed.
  def updateNTerminal(nt: NTerminal, oldCat: Cat, newCat: Cat): NTerminal = {
    val updatedCat = updateCat(nt.cat_, oldCat, newCat)
    // Assumes that NTerminal has a constructor taking a Cat.
    new NTerminal(updatedCat)
  }

  // Helper: Update a Rule definition by replacing occurrences of oldCat with newCat
  def updateRule(rule: Rule, oldCat: Cat, newCat: Cat): Rule = {
    // Update the main category of the rule.
    val updatedCat = updateCat(rule.cat_, oldCat, newCat)
    // Update each item in the rule’s list of items.
    val updatedItems = rule.listitem_.asScala.toList.map {
      case nt: NTerminal => updateNTerminal(nt, oldCat, newCat)
      case other         => other
    }
    // Create a new ListItem and add the updated items.
    val newListItem = new metta_venus.Absyn.ListItem()
    newListItem.addAll(updatedItems.asJava)
    // Construct and return a new Rule with the updated category and items, preserving the label.
    new Rule(rule.label_, updatedCat, newListItem)
  }

  // Helper: Update a definition (Def). For Rule definitions, apply updateRule.
  def updateDef(d: Def, oldCat: Cat, newCat: Cat): Def = d match {
    case r: Rule => updateRule(r, oldCat, newCat)
    case other   => other
  }

  // Updated handleAddExports to handle both BaseExport and RenameExport.
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
                val updatedCats = currentCats.map(cat => updateCat(cat, re.cat_1, re.cat_2))
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
                            inst: TheoryInstAddReplacements): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      import scala.jdk.CollectionConverters._
      // Convert the Java list of replacements to a Scala list.
      val replacements: List[SimpleRepl] =
        inst.listreplacement_.asScala.toList.collect { case s: SimpleRepl => s }

      // Helper function to convert an IntList (defined in Absyn/IntList.java) into a Scala List[Int].
      def convertIntList(il: IntList): List[Int] =
        il.accept(new IntList.Visitor[List[Int], Unit] {
          override def visit(p: Ints, arg: Unit): List[Int] = {
            // p.listinteger_ is a ListInteger (a LinkedList<Integer>)
            p.listinteger_.asScala.toList.map(identity)
          }
        }, ())

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
              // Check that the category in the rule matches the replacement's category.
              if (!rule.cat_.equals(s.cat_))
                Left(s"Error: Category mismatch for definition with label ${PrettyPrinter.print(s.label_)}.")
              else {
                // Extract the non-terminal items from the original rule (ignoring Terminals).
                val origNonTerminals = rule.listitem_.asScala.filter(item => !item.isInstanceOf[Terminal])
                // s.def_ must be a Rule as well.
                s.def_ match {
                  case replRule: Rule =>
                    val replNonTerminals = replRule.listitem_.asScala.filter(item => !item.isInstanceOf[Terminal])
                    if (origNonTerminals.size != replNonTerminals.size)
                      Left(s"Error: Arity mismatch for definition with label ${s.label_}. " +
                           s"Expected ${origNonTerminals.size} non-terminal items but got ${replNonTerminals.size}.")
                    else {
                      val n = origNonTerminals.size
                      val perm: List[Int] = convertIntList(s.intlist_)
                      if (perm.sorted != (0 until n).toList)
                        Left(s"Error: intlist in replacement for label ${PrettyPrinter.print(s.label_)} " +
                             s"is not a permutation of 0 to ${n - 1}.")
                      else {
                        // For each index j, verify that the category of the jth non-terminal in the original rule
                        // matches the category of the non-terminal at position perm(j) in the replacement rule.
                        val check = (0 until n).forall { j =>
                          val origCat = origNonTerminals(j).asInstanceOf[NTerminal].cat_
                          val replCat = replNonTerminals(perm(j)).asInstanceOf[NTerminal].cat_
                          origCat.equals(replCat)
                        }
                        if (!check)
                          Left(s"Error: Category mismatch among non-terminal items in replacement for label ${PrettyPrinter.print(s.label_)}.")
                        else {
                          // All checks pass; update the presentation by replacing the matching Rule.
                          val newDefs: List[Def] = currentPres.listdef_.asScala.toList.map {
                            case r: Rule if r.label_.toString == s.label_.toString => s.def_
                            case other => other
                          }
                          val updatedPres = InstInterpreterCases.BasePresOps.copyPres(currentPres, listdef = Some(newDefs))
                          Right(updatedPres)
                        }
                      }
                    }
                  case _ =>
                    Left(s"Error: Replacement definition for label ${PrettyPrinter.print(s.label_)} is not a Rule.")
                }
              }
          }
        }
      }
    }

  def handleAddTerms(interpreter: InstInterpreter, env: List[(String, BasePres)], inst: TheoryInstAddTerms): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      val newTerms = inst.grammar_ match {
        case g: MkGrammar => g.listdef_.iterator.asScala.toList
        case _ => Nil
      }
      // Get the set of allowed categories from the existing presentation
      val allowedCats = basePres.listcat_.asScala.toSet
      // Check each new term: if it is a Rule, ensure that its category and all categories
      // from its list of items are present in allowedCats.
      newTerms.find {
        case rule: Rule =>
          val fromRule  = Set(rule.cat_)
          val fromItems = rule.listitem_.asScala.collect { case nt: NTerminal => nt.cat_ }.toSet
          val mentionedCats = fromRule ++ fromItems
          !mentionedCats.subsetOf(allowedCats)
        case _ => false
      } match {
        case Some(rule: Rule) =>
          val fromRule  = Set(rule.cat_)
          val fromItems = rule.listitem_.asScala.collect { case nt: NTerminal => nt.cat_ }.toSet
          val unknownCats = (fromRule ++ fromItems) diff allowedCats
          Left(s"Error: Def in addTerms mentions unknown categories: $unknownCats")
        case _ =>
          // If all new terms pass the check, update the BasePres by adding the new terms.
          Right(copyPres(basePres, listdef = Some(basePres.listdef_.asScala.toList ++ newTerms)))
      }
    }

  def handleAddEquations(interpreter: InstInterpreter,
                          env: List[(String, BasePres)],
                          inst: TheoryInstAddEquations): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      // Extract new equations from the instruction.
      // (Adjust extraction as needed based on your grammar structure.)
      val newEquations = inst.listequation_.asScala.toList

      // Compute the set of allowed labels from the definitions in basePres.
      // Reusing logic similar to that in handleConj.
      val allowedLabels: Set[String] = basePres.listdef_.asScala.collect {
        case rule: Rule => labelToString(rule.label_)
      }.toSet

      // Check each new equation to ensure that every label it mentions is among the allowed labels.
      newEquations.find { eq =>
        !interpreter.helpers.labelsInEquation(eq).subsetOf(allowedLabels)
      } match {
        case Some(eq) =>
          val unknownLabels = interpreter.helpers.labelsInEquation(eq) diff allowedLabels
          Left(s"Error: Equation mentions unknown labels: $unknownLabels in theory ${PrettyPrinter.print(inst)}. Presentation: ${PrettyPrinter.print(basePres)}")
        case None =>
          // If all equations are valid, add them to the current presentation.
          Right(copyPres(basePres,
                         listequation = Some(basePres.listequation_.asScala.toList ++ newEquations)))
      }
    }

  def handleAddRewrites(interpreter: InstInterpreter,
                        env: List[(String, BasePres)],
                        inst: TheoryInstAddRewrites): Either[String, BasePres] =
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      // Extract the new rewrite declarations from the instruction.
      val newRewrites = inst.listrewritedecl_.asScala.toList

      // First, perform the label check (as in handleConj).
      val allowedLabels: Set[String] = basePres.listdef_.asScala.collect {
        case rule: Rule => labelToString(rule.label_)
      }.toSet

      newRewrites.find {
        case rd: RDecl => !interpreter.helpers.labelsInRewrite(rd.rewrite_).subsetOf(allowedLabels)
        case _ => false
      } match {
        case Some(rd: RDecl) =>
          val unknownLabels = interpreter.helpers.labelsInRewrite(rd.rewrite_) diff allowedLabels
          Left(s"Error: RewriteDecl mentions unknown labels: $unknownLabels in theory ${PrettyPrinter.print(inst)}. Presentation: ${PrettyPrinter.print(basePres)}")
        case _ =>
          // Now perform the variable check:
          // Helper function: extract variable identifiers from an AST.
          def varsInAST(ast: AST): Set[String] = ast match {
            case as: ASTSubst =>
              // Variables appear in as.ast_1, as.ast_2, and as.ident_
              varsInAST(as.ast_1) ++ varsInAST(as.ast_2) + as.ident_
            case av: ASTVar =>
              Set(av.ident_)
            case ase: ASTSExp =>
              ase.listast_.asScala.toSet.flatMap(varsInAST)
            case _ => Set.empty[String]
          }

          // For a Rewrite, the left-hand side is determined by:
          def leftVars(rew: Rewrite): Set[String] = rew match {
            case rb: RewriteBase    => varsInAST(rb.ast_1)
            case rc: RewriteContext => {
              leftVars(rc.rewrite_) ++ 
                Set(rc.hypothesis_ match { case h: Hyp => h.ident_1 }) ++
                Set(rc.hypothesis_ match { case h: Hyp => h.ident_2 })
            }
            case _                  => Set.empty[String]
          }

          // Similarly, extract the right-hand side variables:
          def rightVars(rew: Rewrite): Set[String] = rew match {
            case rb: RewriteBase    => varsInAST(rb.ast_2)
            case rc: RewriteContext => rightVars(rc.rewrite_)
            case _                  => Set.empty[String]
          }

          // Check each rewrite declaration (all are RDecls) to ensure that
          // every variable on the right appears on the left.
          newRewrites.find {
            case rdecl: RDecl =>
              val lVars = leftVars(rdecl.rewrite_)
              val rVars = rightVars(rdecl.rewrite_)
              !rVars.subsetOf(lVars)
            case _ => false
          } match {
            case Some(rdecl: RDecl) =>
              val lVars = leftVars(rdecl.rewrite_)
              val rVars = rightVars(rdecl.rewrite_)
              val missingVars = rVars diff lVars
              Left(s"Error: In RewriteDecl, variables on the right-hand side not found on the left-hand side: $missingVars")
            case Some(other) =>
              sys.error(s"Unexpected RewriteDecl encountered: $other")
            case None =>
              Right(copyPres(basePres,
                             listrewritedecl = Some(basePres.listrewritedecl_.asScala.toList ++ newRewrites)))
          }
      }
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
