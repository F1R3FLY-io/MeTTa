package io.f1r3fly.mettail

import metta_venus.Absyn._
import scala.annotation.tailrec
import scala.jdk.CollectionConverters._

object ASTHelpers {
  
  // Gets the EquationImpl from an Equation.
  @tailrec
  def equationImpl(e: Equation): EquationImpl = e match {
    case ef: EquationFresh   => equationImpl(ef.equation_)
    case impl: EquationImpl  => impl
  }

  // Gets the RewriteBase from a Rewrite.
  @tailrec
  def rewriteBase(r: Rewrite): RewriteBase = r match {
    case rc: RewriteContext => rewriteBase(rc.rewrite_)
    case rb: RewriteBase => rb
  }

  // Gets the Rewrite from a RewriteDecl.
  def rewrite(rd: RewriteDecl): Rewrite = rd match {
    case r: RDecl => r.rewrite_
  }

  // Substitutes one category for another.  Used by addExports when there's a RenameExport.
  def replaceCats(oldCat: Cat, newCat: Cat, listItem: ListItem): ListItem = {
    val javaList = listItem.asScala.map {
      case t: Terminal => t
      case nt: NTerminal => if (nt.cat_ == oldCat) new NTerminal(newCat) else nt
      case ant: AbsNTerminal => {
        val antListItem = new ListItem()
        antListItem.add(ant.item_)
        new AbsNTerminal(ant.ident_, replaceCats(oldCat, newCat, antListItem).get(0))
      }
      case bnt: BindNTerminal => if (bnt.cat_ == oldCat) new BindNTerminal(bnt.ident_, newCat) else bnt
    }.toSeq.asJava
    val newListItem = new ListItem()
    newListItem.addAll(javaList)
    newListItem
  }

  // Updates a rule with new information.  Used by addReplacements.
  def updateDef(d: Def, oldCat: Cat, newCat: Cat): Def = d match {
    case rule: Rule => new Rule(rule.label_, newCat, replaceCats(oldCat, newCat, rule.listitem_))
  }

  // All vars (as opposed to free vars)
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
}