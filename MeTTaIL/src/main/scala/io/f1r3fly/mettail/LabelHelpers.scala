package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter

object LabelHelpers {
  private def labelToString(l: Label): String = l match {
    case id: Id => id.ident_
    case _: Wild => "_"
    case _: ListE => "[]"
    case _: ListCons => "(:)"
    case _: ListOne => "(:[])"
  }

  private def labelsInAST(ast: AST): Set[String] = ast match {
    case astSExp: ASTSExp => Set(labelToString(astSExp.label_))
    case _                => Set.empty[String]
  }

  def labelsInEquation(eq: Equation): Set[String] = eq match {
    case ef: EquationFresh => labelsInEquation(ef.equation_)
    case ei: EquationImpl  => labelsInAST(ei.ast_1) ++ labelsInAST(ei.ast_2)
    case _                 => Set.empty[String]
  }

  def labelsInRewrite(rw: Rewrite): Set[String] = rw match {
    case rb: RewriteBase    => labelsInAST(rb.ast_1) ++ labelsInAST(rb.ast_2)
    case rc: RewriteContext => labelsInRewrite(rc.rewrite_)
    case _                  => Set.empty[String]
  }
}