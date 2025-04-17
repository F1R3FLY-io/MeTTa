package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

object InstInterpreterHelpers {
  import BasePresOps._

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

  // Used in conj, rewrites, and equations
  private def labelsInAST(ast: AST): Set[String] = ast match {
    case astSExp: ASTSExp => Set(labelToString(astSExp.label_))
    case _                => Set.empty[String]
  }

  private def labelsInEquation(eq: Equation): Set[String] = eq match {
    case ef: EquationFresh => labelsInEquation(ef.equation_)
    case ei: EquationImpl  => labelsInAST(ei.ast_1) ++ labelsInAST(ei.ast_2)
    case _                 => Set.empty[String]
  }

  private def labelsInRewrite(rw: Rewrite): Set[String] = rw match {
    case rb: RewriteBase    => labelsInAST(rb.ast_1) ++ labelsInAST(rb.ast_2)
    case rc: RewriteContext => labelsInRewrite(rc.rewrite_)
    case _                  => Set.empty[String]
  }

  private def sequence[E, A](eithers: List[Either[E, A]]): Either[E, List[A]] =
    eithers.foldRight(Right(Nil): Either[E, List[A]]) { (e, acc) =>
      for {
        x  <- e
        xs <- acc
      } yield x :: xs
    }

  def rewriteBase(r: Rewrite): RewriteBase = r match {
    case rb: RewriteBase => rb
    case rc: RewriteContext => rewriteBase(rc.rewrite_)
  }
  
  def rewrite(rd: RewriteDecl): Rewrite = rd match {
    case r: RDecl => r.rewrite_
  }

  def createLabelHelpers: LabelHelpers = new LabelHelpers {
    def labelsInAST(ast: AST): Set[String] = InstInterpreterHelpers.labelsInAST(ast)
    def labelsInEquation(eq: Equation): Set[String] = InstInterpreterHelpers.labelsInEquation(eq)
    def labelsInRewrite(rw: Rewrite): Set[String] = InstInterpreterHelpers.labelsInRewrite(rw)
    def sequence[E, A](eithers: List[Either[E, A]]): Either[E, List[A]] =
      InstInterpreterHelpers.sequence(eithers)
  }

  def replaceCats(oldCat: Cat, newCat: Cat, listItem: ListItem): ListItem = {
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

  def updateDef(d: Def, oldCat: Cat, newCat: Cat): Def = d match {
    case rule: Rule => new Rule(rule.label_, newCat, replaceCats(oldCat, newCat, rule.listitem_))
  }

  def nonTerminals(items: ListItem): Seq[Item] = {
    items.asScala.toSeq.filter(item => !item.isInstanceOf[Terminal])
  }

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

  def leftVars(rew: Rewrite): Set[String] = rew match {
    case rb: RewriteBase    => varsInAST(rb.ast_1)
    case rc: RewriteContext => {
      leftVars(rc.rewrite_) ++
        Set(rc.hypothesis_ match { case h: Hyp => h.ident_1 }) ++
        Set(rc.hypothesis_ match { case h: Hyp => h.ident_2 })
    }
    case _                  => Set.empty[String]
  }

  def rightVars(rew: Rewrite): Set[String] = rew match {
    case rb: RewriteBase    => varsInAST(rb.ast_2)
    case rc: RewriteContext => rightVars(rc.rewrite_)
    case _                  => Set.empty[String]
  }

  def hypVars(rew: Rewrite): Set[(String, String)] = rew match {
    case rc: RewriteContext => {
      hypVars(rc.rewrite_) ++
        Set(rc.hypothesis_ match { case h: Hyp => (h.ident_1, h.ident_2) })
    }
    case _                  => Set.empty[(String, String)]
  }

  object addEquationsHelpers {
    sealed trait CatOfASTResult

    case class COALabelNotFound(label: Label) extends CatOfASTResult
    case class COAVar(varName: String) extends CatOfASTResult
    case class COAConcrete(cat: Cat) extends CatOfASTResult

    def printCatOfASTResult(c: CatOfASTResult) = {
      c match {
        case COALabelNotFound(l) => s"COALabelNotFound(${PrettyPrinter.print(l)})"
        case COAVar(v) => s"COAVar($v)"
        case COAConcrete(c) => s"COAConcrete(${PrettyPrinter.print(c)})"
      }
    }

    def catOfAST(ast: AST, defs: Map[Label, Rule]): CatOfASTResult = {
      ast match {
        case astVar: ASTVar => COAVar(astVar.ident_)
        case astSExp: ASTSExp => defs.get(astSExp.label_) match {
          case None => COALabelNotFound(astSExp.label_)
          case Some(rule) => COAConcrete(rule.cat_)
        }
        case astSubst: ASTSubst => catOfAST(astSubst.ast_1, defs) match {
          case lnf: COALabelNotFound => lnf
          case COAVar(v) if astSubst.ident_ == v => catOfAST(astSubst.ast_2, defs)
          case other => other
        }
      }
    }

    def sameCategory(
      leftCat: CatOfASTResult,
      rightCat: CatOfASTResult,
      rewriteDecl: RewriteDecl
    ): Either[String, Unit] = leftCat match {
      case COALabelNotFound(label) => 
        Left(s"Label $label not found in rewrite ${PrettyPrinter.print(rewriteDecl)}")
      case COAVar(leftVarName) => rightCat match {
        case COALabelNotFound(label) => 
          Left(s"Label $label not found in rewrite ${PrettyPrinter.print(rewriteDecl)}")
        case COAVar(rightVarName) =>
          Left(s"Cannot determine categories of variables $leftVarName and $rightVarName"
               + s" in rewrite ${PrettyPrinter.print(rewriteDecl)}")
        case COAConcrete(rightConcreteCat) => Right(())
      }
      case COAConcrete(leftConcreteCat) => rightCat match {
        case COALabelNotFound(label) => 
          Left(s"Label $label not found in rewrite ${PrettyPrinter.print(rewriteDecl)}")
        case COAVar(rightVarName) => Right(())
        case COAConcrete(rightConcreteCat) if (leftConcreteCat != rightConcreteCat) =>
          Left(s"Categories of the sides differ (${PrettyPrinter.print(leftConcreteCat)}"
               + s" != ${PrettyPrinter.print(rightConcreteCat)}) in rewrite"
               + s" ${PrettyPrinter.print(rewriteDecl)}")
        case _ => Right(())
      }
    }
    
    def consistentCategory(
      ast: AST,
      rewriteDecl: RewriteDecl,
      defs: Map[Label, Rule]
    ): Either[String, Map[String, Cat]] = {
      freeVarsInAST(ast).foldLeft[Either[String, Map[String, Cat]]](
        Right(Map.empty[String, Cat])
      ){ (acc, ident) =>
        for {
          m <- acc
          newAcc <- catOfIdentInAST(ident, defs, None, ast) match {
            case COIIAError(err) => Left(err)
            case COIIAConcrete(cat) => Right(m + (ident -> cat))
            case COIIAVar(v) => Right(m)
            case COIIANotInAST => {
              Left(s"Somehow ${ident} is free (so it appears), but has no category"
                   + s" (so it doesn't) in ${PrettyPrinter.print(rewriteDecl)}?")
            }
          }
        } yield newAcc
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

    def checkHypotheticals(
      hVars: Set[(String, String)],
      defs: Map[Label, Rule],
      rb: RewriteBase
    ): Either[String, Unit] = {
      hVars.foldLeft[Either[String, Unit]](Right(())) { case (acc, (src, tgt)) =>
        catOfIdentInAST(src, defs, None, rb.ast_1) match {
          case COIIAError(err) => Left(err)
          case COIIANotInAST => Left(s"Source of hypothetical rewrite $src ~> $tgt must"
                                     + s" appear on the left of ${PrettyPrinter.print(rb)}")
          case COIIAVar(_) => {
            catOfIdentInAST(src, defs, None, rb.ast_2) match {
              case COIIAError(err) => Left(err)
              case COIIANotInAST => {
                catOfIdentInAST(tgt, defs, None, rb.ast_1) match {
                  case COIIAError(err) => Left(err)
                  case COIIANotInAST => {
                    catOfIdentInAST(tgt, defs, None, rb.ast_2) match {
                      case COIIAError(err) => Left(err)
                      case COIIANotInAST => Left(s"Target of hypothetical rewrite $src ~> $tgt must"
                                                 + s" appear on the right of ${PrettyPrinter.print(rb)}")
                      case _ => Right(())
                    }
                  }
                  case _ => Left(s"Target of hypothetical rewrite $src ~> $tgt must not"
                                 + s" appear on the left of ${PrettyPrinter.print(rb)}")
                }
              }
              case _ => Left(s"Source of hypothetical rewrite $src ~> $tgt must not"
                             + s" appear on the right of ${PrettyPrinter.print(rb)}")
            }
          }
          case COIIAConcrete(cat1) => {
            catOfIdentInAST(src, defs, None, rb.ast_2) match {
              case COIIAError(err) => Left(err)
              case COIIANotInAST => {
                catOfIdentInAST(tgt, defs, None, rb.ast_1) match {
                  case COIIAError(err) => Left(err)
                  case COIIANotInAST => {
                    catOfIdentInAST(tgt, defs, None, rb.ast_2) match {
                      case COIIAError(err) => Left(err)
                      case COIIANotInAST => Left(s"Target of hypothetical rewrite $src ~> $tgt must"
                                                 + s" appear on the right of ${PrettyPrinter.print(rb)}")
                      case COIIAVar(_) => Right(())
                      case COIIAConcrete(cat2) if cat1 == cat2 => Right(())
                      case _ => Left(s"Variables of hypothetical rewrite $src ~> $tgt have"
                                     + s" have different categories ${PrettyPrinter.print(cat1)}"
                                     + s" and ${PrettyPrinter.print(cat1)} in ${PrettyPrinter.print(rb)}")
                    }
                  }
                  case _ => Left(s"Target of hypothetical rewrite $src ~> $tgt must not"
                                 + s" appear on the left of ${PrettyPrinter.print(rb)}")
                }
              }
              case _ => Left(s"Source of hypothetical rewrite $src ~> $tgt must not"
                             + s" appear on the right of ${PrettyPrinter.print(rb)}")
            }
          }
        }
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
                COIIAError(s"Label ${PrettyPrinter.print(astSExp.label_)}'s"
                           + s" category ${PrettyPrinter.print(rule.cat_)} doesn't"
                           + s" match context ${PrettyPrinter.print(ctxCat)}")
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
                    COIIAError(s"Identifier $ident has mismatched categories"
                               + s" ${PrettyPrinter.print(x)} and ${PrettyPrinter.print(y)}"
                               + s" in ${PrettyPrinter.print(astSExp)}")
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
}