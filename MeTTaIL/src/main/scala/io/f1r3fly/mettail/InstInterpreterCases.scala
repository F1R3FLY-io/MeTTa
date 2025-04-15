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

  private object BasePresOps {
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

  def handleSubtract(interpreter: InstInterpreter,
                     env: List[(String, BasePres)],
                     subtract: TheoryInstSubtract): Either[String, BasePres] = {
    val h = interpreter.helpers
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
        h.labelsInEquation(eq).subsetOf(allowedLabels)
      }
      // For rewrite declarations, keep only those not in bp2 and whose rewrite’s labels are a subset of allowedLabels.
      diffRewrites = bp1.listrewritedecl_.asScala.toSet.filter { rw =>
        !bp2.listrewritedecl_.asScala.toSet.contains(rw) &&
        (rw match {
           case rdecl: RDecl => h.labelsInRewrite(rdecl.rewrite_).subsetOf(allowedLabels)
           case _ => true
        })
      }
    } yield copyPres(empty,
                     listcat = Some(diffCats.toList),
                     listdef = Some(diffDefs.toList),
                     listequation = Some(diffEquations.toList),
                     listrewritedecl = Some(diffRewrites.toList))
  }

  private def replaceCats(oldCat: Cat, newCat: Cat, listItem: ListItem): ListItem = {
    val javaList = listItem.asScala.map {
      case t: Terminal => t
      case nt: NTerminal => if (nt.cat_ == oldCat) new NTerminal(newCat) else nt
      case ant: AbsNTerminal => if (ant.cat_ == oldCat) new AbsNTerminal(ant.ident_, newCat) else ant
      case bnt: BindNTerminal => if (bnt.cat_ == oldCat) new BindNTerminal(bnt.ident_, newCat) else bnt
    }.toSeq.asJava
    val newListItem = new ListItem()
    newListItem.addAll(javaList)
    newListItem
  }

  // Helper: Update a definition (Def). For Rule definitions, apply updateRule.
  private def updateDef(d: Def, oldCat: Cat, newCat: Cat): Def = d match {
    case rule: Rule => new Rule(rule.label_, newCat, replaceCats(oldCat, newCat, rule.listitem_))
    case other   => other
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

  def nonTerminals(items: ListItem): Seq[Item] = {
    items.asScala.toSeq.filter(item => !item.isInstanceOf[Terminal])
  }

  def handleAddReplacements(interpreter: InstInterpreter,
                            env: List[(String, BasePres)],
                            inst: TheoryInstAddReplacements): Either[String, BasePres] = {
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
                val origNonTerminals = nonTerminals(rule.listitem_)
                // s.def_ must be a Rule as well.
                s.def_ match {
                  case replRule: Rule =>
                    val replNonTerminals = nonTerminals(replRule.listitem_)
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
                        // For each index j, verify that the item of the jth non-terminal in the original rule
                        // matches the item of the non-terminal at position perm(j) in the replacement rule.
                        val check = (0 until n).forall { j =>
                          origNonTerminals(j) == replNonTerminals(perm(j))
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

  private object addEquationsHelpers {
    sealed trait CatOfASTResult

    case class LabelNotFound(label: Label) extends CatOfASTResult
    case class Var(varName: String) extends CatOfASTResult
    case class Concrete(cat: Cat) extends CatOfASTResult

    def printCatOfASTResult(c: CatOfASTResult) = {
      c match {
        case LabelNotFound(l) => s"LabelNotFound(${PrettyPrinter.print(l)})"
        case Var(v) => s"Var($v)"
        case Concrete(c) => s"Concrete(${PrettyPrinter.print(c)})"
      }
    }

    def catOfAST(ast: AST, defs: Map[Label, Rule]): CatOfASTResult = {
      ast match {
        case astVar: ASTVar => Var(astVar.ident_)
        case astSExp: ASTSExp => defs.get(astSExp.label_) match {
          case None => LabelNotFound(astSExp.label_)
          case Some(rule) => Concrete(rule.cat_)
        }
        case astSubst: ASTSubst => catOfAST(astSubst.ast_1, defs) match {
          case lnf: LabelNotFound => lnf
          case Var(v) if astSubst.ident_ == v => catOfAST(astSubst.ast_2, defs)
          case other => other
        }
      }
    }

    def freeVarsInAST(ast: AST): Set[String] = {
      ast match {
        case astVar: ASTVar => Set(astVar.ident_)
        case astSExp: ASTSExp => astSExp.listast_.asScala.flatMap(freeVarsInAST).toSet
        case astSubst: ASTSubst => 
          freeVarsInAST(astSubst.ast_1).filterNot(_ == astSubst.ident_) ++ freeVarsInAST(astSubst.ast_2)
      }
    }

    def listDefToMap(listDef: ListDef): Map[Label, Rule] = {
      listDef.asScala.collect {
        case rule: Rule => rule.label_ -> rule
      }.toMap
    }

    sealed trait CatOfIdentInASTResult

    case class COIIAError(err: String) extends CatOfIdentInASTResult
    case object COIIANotInAST extends CatOfIdentInASTResult
    case class COIIAVar(varName: String) extends CatOfIdentInASTResult
    case class COIIAConcrete(cat: Cat) extends CatOfIdentInASTResult

    def catOfIdentInAST(
      ident: String,
      defs: Map[Label, Rule],
      context: Option[Cat],
      ast: AST
    ): CatOfIdentInASTResult = {
      ast match {
        case astSubst: ASTSubst => handleASTSubst(ident, defs, context, astSubst)
        case astVar: ASTVar     => handleASTVar(ident, defs, context, astVar)
        case astSExp: ASTSExp   => handleASTSExp(ident, defs, context, astSExp)
        case _                  => COIIAError(s"Unknown AST type: ${PrettyPrinter.print(ast)}")
      }
    }

    def optCatFromItem(item: Item): Option[Cat] = {
      item match {
        case nt: NTerminal => Some(nt.cat_)
        case ant: AbsNTerminal => Some(ant.cat_)
        case bnt: BindNTerminal => Some(new IdCat(bnt.ident_))
        case _: Terminal => None
      }
    }

    def handleASTSExp(ident: String, defs: Map[Label, Rule], context: Option[Cat], astSExp: ASTSExp): CatOfIdentInASTResult = {
      // match length with rule
      val optRule = defs.get(astSExp.label_)
      optRule match {
        case None => COIIAError(s"No rule with label ${PrettyPrinter.print(astSExp.label_)}")
        case Some(rule) => {
          val filtered = nonTerminals(rule.listitem_)
          val children = astSExp.listast_.asScala
          if (filtered.length != children.length) {
            COIIAError(s"Length mismatch with label ${PrettyPrinter.print(astSExp.label_)}")
          } else {
            // match category of rule with context
            context match {
              case Some(ctxCat) if rule.cat_ != ctxCat => 
                COIIAError(s"""Label ${PrettyPrinter.print(astSExp.label_)}'s 
                              |category ${PrettyPrinter.print(rule.cat_)} doesn't 
                              |match context ${PrettyPrinter.print(ctxCat)}""")
              case _ => {
                // fold over children
                val childCats = children.zipWithIndex.map {
                  case (child, idx) => {
                    val ctx = optCatFromItem(filtered(idx))
                    catOfIdentInAST(ident, defs, ctx, child)
                  }
                }.toSeq
                val result = childCats.foldLeft[CatOfIdentInASTResult](
                  COIIANotInAST
                ) {
                  // An error in any subtree propagates up.
                  case (COIIAError(err), _) => COIIAError(err)
                  case (_, COIIAError(err)) => COIIAError(err)
                  // If it's not found in one subtree, defer to any other result.
                  case (COIIANotInAST, other) => other
                  case (other, COIIANotInAST) => other
                  case (COIIAConcrete(x), COIIAConcrete(y)) => if (x == y) {
                    COIIAConcrete(x)
                  } else {
                    COIIAError(s"""Identifier $ident has mismatched categories 
                                  |${PrettyPrinter.print(x)} and ${PrettyPrinter.print(y)} 
                                  |in ${PrettyPrinter.print(astSExp)}""")
                  }
                  case pair => COIIAError(s"Unexpected pairing in fold: $pair")
                }
                result
              }
            }
          }
        }
      }
    }

    def handleASTVar(ident: String, defs: Map[Label, Rule], context: Option[Cat], astVar: ASTVar): CatOfIdentInASTResult = {
      if (ident == astVar.ident_) {
        context match {
          case None => COIIAVar(ident)
          case Some(ctx) => COIIAConcrete(ctx)
        }
      } else {
        COIIANotInAST
      }
    }

    def handleASTSubst(ident: String, defs: Map[Label, Rule], context: Option[Cat], astSubst: ASTSubst): CatOfIdentInASTResult = {
      catOfIdentInAST(ident, defs, context, findAndReplace(astSubst.ast_2, astSubst.ident_, defs)(astSubst.ast_1))
    }

    // Precondition: any label in the AST has to appear in defs.
    def findAndReplace(replacement: AST, ident: String, defs: Map[Label, Rule])(ast: AST): AST = {
      ast match {
        case astVar: ASTVar => if (astVar.ident_ == ident) replacement else astVar
        case astSExp: ASTSExp => {
          val optRule = defs.get(astSExp.label_)
          optRule match {
            case Some(rule) => {
              val filtered = nonTerminals(rule.listitem_)
              val javaList = filtered.zip(astSExp.listast_.asScala).map {
                case (item, ast) => item match {
                  // In the usual case, we recursively replace
                  case nt: NTerminal => findAndReplace(replacement, ident, defs)(ast)

                  // If the bound variable shadows the one being replaced, don't recurse; otherwise, do
                  case ant: AbsNTerminal =>
                    if (ant.ident_ == ident) ast else findAndReplace(replacement, ident, defs)(ast)

                  // Never replace in a BindNTerminal
                  case bnt: BindNTerminal => ast
                }
              }.toSeq.asJava
              val newListAST = new ListAST()
              newListAST.addAll(javaList)
              new ASTSExp(astSExp.label_, newListAST)
            }
          }
        }
        case astSubst: ASTSubst => {
          findAndReplace(replacement, ident, defs)(
            findAndReplace(astSubst.ast_2, astSubst.ident_, defs)(astSubst.ast_1)
          )
        }
      }
    }
  }

  import addEquationsHelpers._

  def handleAddEquations(interpreter: InstInterpreter,
                          env: List[(String, BasePres)],
                          inst: TheoryInstAddEquations): Either[String, BasePres] = {
    interpreter.interpret(env, inst.theoryinst_).flatMap { basePres =>
      val defs: Map[Label, Rule] = listDefToMap(basePres.listdef_)
      val checkEqns = inst.listequation_.asScala.toList.foldLeft[Either[String, Unit]](
        Right(())
      ) { (acc, e) =>
        acc match {
          case Left(err) => Left(err)
          case Right(()) => {
            var eqAbs = e
            while (eqAbs.isInstanceOf[EquationFresh]) eqAbs match {
              case ef: EquationFresh => eqAbs = ef.equation_
            }
            eqAbs match {
              case eqn: EquationImpl => {
                // Check validity of equations as follows
                // 1. The two sides of the equation have the same category
                //    OR one has a category and the other is a top-level variable.
                val leftCat = catOfAST(eqn.ast_1, defs)
                val rightCat = catOfAST(eqn.ast_2, defs)
                val sameCategory: Either[String, Cat] = leftCat match {
                  case LabelNotFound(label) => Left(s"Label $label not found in equation ${PrettyPrinter.print(eqn)}")
                  case Var(leftVarName) => rightCat match {
                    case LabelNotFound(label) => Left(s"Label $label not found in equation ${PrettyPrinter.print(eqn)}")
                    case Var(rightVarName) =>
                      Left(s"""Cannot determine categories of variables $leftVarName and $rightVarName 
                              |in equation ${PrettyPrinter.print(eqn)}""")
                    case Concrete(rightConcreteCat) => Right(rightConcreteCat)
                  }
                  case Concrete(leftConcreteCat) => rightCat match {
                    case LabelNotFound(label) => Left(s"Label $label not found in equation ${PrettyPrinter.print(eqn)}")
                    case Var(rightVarName) => Right(leftConcreteCat)
                    case Concrete(rightConcreteCat) => if (leftConcreteCat == rightConcreteCat) {
                      Right(leftConcreteCat)
                    } else {
                      Left(s"""Categories of the sides differ (${PrettyPrinter.print(leftConcreteCat)} 
                              |!= ${PrettyPrinter.print(rightConcreteCat)}) in equation ${PrettyPrinter.print(eqn)}""")
                    }
                  }
                }

                sameCategory match {
                  case Left(err) => Left(err)
                  case Right(concreteCat) => {
                    // 2. Check that each variable has a consistent category

                    val freeInAST1 = freeVarsInAST(eqn.ast_1).foldLeft[Either[String, Map[String, Cat]]](
                      Right(Map.empty[String, Cat])
                    ) { (acc, ident) =>
                      acc match {
                        case Left(err) => Left(err)
                        case Right(m) => {
                          catOfIdentInAST(ident, defs, None, eqn.ast_1) match {
                            case COIIAError(err) => Left(err)
                            case COIIAConcrete(cat) => Right(m + (ident -> cat))
                            case COIIAVar(v) => Right(m)
                            case COIIANotInAST => {
                              Left(s"""Somehow ${ident} is free (so it appears), but has no category (so it doesn't) in 
                                      |${PrettyPrinter.print(eqn.ast_1)}?""")
                            }
                          }
                        }
                      }
                    }

                    freeInAST1 match {
                      case Left(err) => Left(err)
                      case Right(freeVars) => {
                        freeVarsInAST(eqn.ast_2).foldLeft[Either[String, Unit]](
                          Right(())
                        ) { (acc, ident) =>
                          val result = catOfIdentInAST(ident, defs, None, eqn.ast_2) match {
                            case COIIAError(err) => Left(err)
                            case COIIAConcrete(cat) => freeVars.get(ident) match {
                              case None => Right(())
                              case Some(cat2) if cat == cat2 => Right(())
                              case Some(cat2) => {
                                Left(s"""Variable ${ident} has category ${PrettyPrinter.print(cat)} on the left-
                                        |hand side and category ${PrettyPrinter.print(cat2)} on the right-hand 
                                        |side of ${PrettyPrinter.print(eqn)}""")
                              }
                            }
                            case COIIAVar(v) => freeVars.get(ident) match {
                              case None => Left(s"""Variable $ident can't be assigned a category in 
                                                   |equation ${PrettyPrinter.print(eqn)}""")
                              case Some(cat2) => Right(())
                            }
                            case COIIANotInAST => {
                              Left(s"""Somehow ${ident} is free (so it appears), but has no category (so it doesn't) in 
                                      |${PrettyPrinter.print(eqn.ast_1)}?!""")
                            }
                          }
                          result
                        }
                      }
                    }

                  }
                }
              }
            }
          }
        }
      }
      checkEqns match {
        case Left(err) => Left(err)
        case Right(()) =>
          // If all equations are valid, add them to the current presentation.
          Right(
            copyPres(
              basePres,
              listequation = Some(
                basePres.listequation_.asScala.toList ++ inst.listequation_.asScala.toList
              )
            )
          )
      }
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
            Left(s"Mismatch in number of arguments for theory ${PrettyPrinter.print(baseDecl.name_)}")
          else {
            val actuals = ctor.listtheoryinst_.asScala.toList
            interpreter.helpers.sequence(actuals.map(interpreter.interpret(env, _))).flatMap { actualPresentations =>
              val formalsEither = baseDecl.listvariabledecl_.asScala.toList.map {
                case varDecl: VarDecl => Right(varDecl.ident_.toString)
                case _ => Left(s"""Non-var declaration in formal parameter list 
                                  |for theory ${PrettyPrinter.print(baseDecl.name_)}""")
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
