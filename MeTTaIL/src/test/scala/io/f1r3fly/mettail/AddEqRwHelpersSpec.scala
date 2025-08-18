package io.f1r3fly.mettail

import org.scalatest.funsuite.AnyFunSuite
import metta_venus.Absyn._
import io.f1r3fly.mettail.AddEqRwHelpers._

class AddEqRwHelpersSpec extends AnyFunSuite {
  test("nonTerminals should filter out Terminal items") {
    val list = new ListItem()
    list.addLast(new Terminal("lit"))
    list.addLast(new NTerminal(new IdCat("C")))
    list.addLast(new BindNTerminal("x", new IdCat("C")))

    val nts = nonTerminals(list)
    assert(nts.forall(item => !item.isInstanceOf[Terminal]))
    assert(nts.size == 2)
  }

  test("catOfAST should return COAVar for ASTVar") {
    val result = catOfAST(new ASTVar("v"), Map.empty)
    assert(result.isInstanceOf[COAVar])
    assert(result.asInstanceOf[COAVar].varName == "v")
  }

  test("catOfAST should return COALabelNotFound for unknown ASTSExp label") {
    val ast = new ASTSExp(new Id("L"), new ListAST())
    val result = catOfAST(ast, Map.empty)
    assert(result.isInstanceOf[COALabelNotFound])
    assert(result.asInstanceOf[COALabelNotFound].label == new Id("L"))
  }

  test("catOfAST should return COAConcrete when ASTSExp label has a rule") {
    val rule = new Rule(new Id("L"), new IdCat("C"), new ListItem())
    val ast = new ASTSExp(new Id("L"), new ListAST())
    val result = catOfAST(ast, Map(new Id("L") -> rule))
    assert(result.isInstanceOf[COAConcrete])
    assert(result.asInstanceOf[COAConcrete].cat == new IdCat("C"))
  }

  test("catOfAST should unwrap ASTSubst when var matches") {
    val rule = new Rule(new Id("L"), new IdCat("C"), new ListItem())
    val subst = new ASTSubst(
      new ASTVar("x"),
      new ASTSExp(new Id("L"), new ListAST()),
      "x"
    )
    val result = catOfAST(subst, Map(new Id("L") -> rule))
    assert(result.isInstanceOf[COAConcrete])
    assert(result.asInstanceOf[COAConcrete].cat == new IdCat("C"))
  }

  test("catOfAST should propagate COALabelNotFound on ASTSubst when left side unknown") {
    val subst = new ASTSubst(
      new ASTSExp(new Id("M"), new ListAST()),
      new ASTVar("v"),
      "x"
    )
    val result = catOfAST(subst, Map.empty)
    assert(result.isInstanceOf[COALabelNotFound])
    assert(result.asInstanceOf[COALabelNotFound].label == new Id("M"))
  }

  val pretty = "structure"
  test("sameCategory should fail when left label not found") {
    val left = COALabelNotFound(new Id("L"))
    val right = COAVar("v")
    val err = sameCategory(left, right, pretty)
    assert(err.isLeft)
    assert(err.left.get.contains("Label L not found in structure"))
  }

  test("sameCategory should error when both sides are variables") {
    val left = COAVar("x")
    val right = COAVar("y")
    val err = sameCategory(left, right, pretty)
    assert(err.isLeft)
    assert(err.left.get.contains("Cannot determine categories of variables x and y in structure"))
  }

  test("sameCategory should succeed when a var is compared to a concrete cat") {
    val left = COAVar("x")
    val right = COAConcrete(new IdCat("C"))
    assert(sameCategory(left, right, pretty).isRight)
  }

  test("sameCategory should succeed when concrete cat compared to var") {
    val left = COAConcrete(new IdCat("C"))
    val right = COAVar("x")
    assert(sameCategory(left, right, pretty).isRight)
  }

  test("sameCategory should succeed when two concrete cats match") {
    val left = COAConcrete(new IdCat("C"))
    val right = COAConcrete(new IdCat("C"))
    assert(sameCategory(left, right, pretty).isRight)
  }

  test("sameCategory should error when two concrete cats differ") {
    val left = COAConcrete(new IdCat("C1"))
    val right = COAConcrete(new IdCat("C2"))
    val err = sameCategory(left, right, pretty)
    assert(err.isLeft)
    assert(err.left.get.contains("Categories of the sides differ"))
  }
}
