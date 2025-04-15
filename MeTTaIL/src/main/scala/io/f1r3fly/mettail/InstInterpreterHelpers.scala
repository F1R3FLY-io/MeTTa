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