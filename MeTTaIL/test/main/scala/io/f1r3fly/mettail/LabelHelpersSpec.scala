package io.f1r3fly.mettail

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import io.f1r3fly.mettail.LabelHelpers

class LabelHelpersSpec extends AnyFlatSpec with Matchers {

  "labelsInEquation" should "extract labels from an EquationImpl" in {
    val emptyListAST = new ListAST()
    val ast1 = new ASTSExp(new Id("foo"), emptyListAST)
    val ast2 = new ASTSExp(new ListCons(), emptyListAST)
    val eqImpl = new EquationImpl(ast1, ast2)

    val labels = LabelHelpers.labelsInEquation(eqImpl)
    labels should contain allOf ("foo", ":)")
    labels.size shouldEqual 2
  }

  it should "delegate through EquationFresh" in {
    val emptyListAST = new ListAST()
    val ast1 = new ASTSExp(new Id("bar"), emptyListAST)
    val ast2 = new ASTSExp(new ListE(), emptyListAST)
    val eqImpl = new EquationImpl(ast1, ast2)
    val eqFresh = new EquationFresh("x", "y", eqImpl)

    val labels = LabelHelpers.labelsInEquation(eqFresh)
    labels should contain allOf ("bar", "[]")
    labels.size shouldEqual 2
  }

  "labelsInRewrite" should "extract labels from a RewriteBase" in {
    val emptyListAST = new ListAST()
    val ast1 = new ASTSExp(new Id("baz"), emptyListAST)
    val ast2 = new ASTSExp(new ListOne(), emptyListAST)
    val rwBase = new RewriteBase(ast1, ast2)

    val labels = LabelHelpers.labelsInRewrite(rwBase)
    labels should contain allOf ("baz", "(:[])")
    labels.size shouldEqual 2
  }

  it should "unwrap through RewriteContext" in {
    val emptyListAST = new ListAST()
    val ast1 = new ASTSExp(new Id("qux"), emptyListAST)
    val ast2 = new ASTSExp(new Wild(), emptyListAST)
    val rwBase = new RewriteBase(ast1, ast2)
    val hyp = new Hyp("h1", "h2")
    val rwCtx = new RewriteContext(hyp, rwBase)

    val labels = LabelHelpers.labelsInRewrite(rwCtx)
    labels should contain allOf ("qux", "_")
    labels.size shouldEqual 2
  }

  it should "return empty for unsupported types" in {
    // Using an ASTSubst wrapped in RewriteContext without Label elements
    val subst = new ASTSubst(new ASTVar("v1"), new ASTVar("v2"), "v2")
    val rwBase = new RewriteBase(subst, subst)
    val labels = LabelHelpers.labelsInRewrite(rwBase)
    labels shouldBe empty
  }
}
