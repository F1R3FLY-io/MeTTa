package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

object AddEqRwHelpers {
  def nonTerminals(items: ListItem): Seq[Item] = {
    items.asScala.toSeq.filter(item => !item.isInstanceOf[Terminal])
  }

  sealed trait CatOfASTResult

  case class COALabelNotFound(label: Label) extends CatOfASTResult
  case class COAVar(varName: String) extends CatOfASTResult
  case class COAConcrete(cat: Cat) extends CatOfASTResult

  // Determines the category of an AST.  Doesn't recurse.
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

  // Checks if the two sides of an equation or rewrite have the same category
  // and provides nice error handling when they're not the same.
  def sameCategory(
    leftCat: CatOfASTResult,
    rightCat: CatOfASTResult,
    prettyStructure: String
  ): Either[String, Unit] = leftCat match {
    case COALabelNotFound(label) => 
      Left(s"Label ${PrettyPrinter.print(label)} not found in $prettyStructure")
    case COAVar(leftVarName) => rightCat match {
      case COALabelNotFound(label) => 
        Left(s"Label ${PrettyPrinter.print(label)} not found in $prettyStructure")
      case COAVar(rightVarName) =>
        Left(s"Cannot determine categories of variables $leftVarName and $rightVarName"
             + s" in $prettyStructure")
      case COAConcrete(rightConcreteCat) => Right(())
    }
    case COAConcrete(leftConcreteCat) => rightCat match {
      case COALabelNotFound(label) => 
        Left(s"Label ${PrettyPrinter.print(label)} not found in $prettyStructure")
      case COAVar(rightVarName) => Right(())
      case COAConcrete(rightConcreteCat) if (leftConcreteCat != rightConcreteCat) =>
        Left(s"Categories of the sides differ (${PrettyPrinter.print(leftConcreteCat)}"
             + s" != ${PrettyPrinter.print(rightConcreteCat)}) in $prettyStructure")
      case _ => Right(())
    }
  }
  
  // Checks whether all the free vars in an AST have a consistent category.
  // For example, we don't want x to refer to both a process and a name in
  // RHO calculus.
  // TODO: check consistency of shadowing vars
  //   Do a preliminary renaming to avoid shadowing and then check consistency
  def consistentCategory(
    ast: AST,
    defs: Map[Label, Rule],
    prettyStructure: String
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
                 + s" (so it doesn't) in $prettyStructure?\n${PrettyPrinter.print(ast)}")
          }
        }
      } yield newAcc
    }
  }

  // Finds all the free variables in an AST.
  def freeVarsInAST(ast: AST): Set[String] = {
    ast match {
      case astVar: ASTVar => Set(astVar.ident_)
      case astSExp: ASTSExp => astSExp.listast_.asScala.flatMap(freeVarsInAST).toSet
      case astSubst: ASTSubst => 
        freeVarsInAST(astSubst.ast_1).filterNot(_ == astSubst.ident_) ++ freeVarsInAST(astSubst.ast_2)
    }
  }

  sealed trait CatOfIdentInASTResult

  case class COIIAError(err: String) extends CatOfIdentInASTResult
  case object COIIANotInAST extends CatOfIdentInASTResult
  case class COIIAVar(varName: String) extends CatOfIdentInASTResult
  case class COIIAConcrete(cat: Cat) extends CatOfIdentInASTResult

  // Infers the category of an identifier from its position in an AST.
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
    // Find cat of ident in astSubst.ast_2, then check it's consistent with
    //   cat of ident in astSubst.ast_1 after substitution happens
    val catInReplaced = catOfIdentInAST(
      ident,
      defs,
      context,
      findAndReplace(astSubst.ast_2, astSubst.ident_, defs)(astSubst.ast_1)
    )
    val coiiacat1 = catOfIdentInAST(ident, defs, context, astSubst.ast_2)
    coiiacat1 match {
      case COIIAError(err) => COIIAError(err)
      case COIIAConcrete(cat1) => catInReplaced match {
        case COIIAError(err) => COIIAError(err)
        case COIIAConcrete(cat2) if cat1 == cat2 => COIIAConcrete(cat1)
        case COIIAConcrete(cat2) => COIIAError(s"Variable $ident has inconsistent categories"
                                               + s" $cat1 and $cat2 in ${PrettyPrinter.print(astSubst)}")
        case _ => COIIAConcrete(cat1)
      }
      case _ => catInReplaced
    }
  }

  def optCatFromItem(item: Item): Option[Cat] = {
    item match {
      case nt: NTerminal => Some(nt.cat_)
      case ant: AbsNTerminal => optCatFromItem(ant.item_)
      case bnt: BindNTerminal => Some(new IdCat(bnt.ident_))
      case _: Terminal => None
    }
  }

  // Validates the use of the vars introduced in the freshness constraints of equations.
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

  // Precondition: any label in the AST has to appear in defs.
  private def findAndReplace(replacement: AST, ident: String, defs: Map[Label, Rule])(ast: AST): AST = {
    ast match {
      case astVar: ASTVar => if (astVar.ident_ == ident) replacement else astVar
      case astSExp: ASTSExp => {
        val rule = defs(astSExp.label_)
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
      case astSubst: ASTSubst => {
        findAndReplace(replacement, ident, defs)(
          findAndReplace(astSubst.ast_2, astSubst.ident_, defs)(astSubst.ast_1)
        )
      }
    }
  }
}
