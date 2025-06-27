package io.f1r3fly.mettail

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

class BNFCRendererSpec extends AnyFlatSpec with Matchers {

  "addDesugaredLambdas" should "add a desugared arrow rule for a binder pattern" in {
    // Create the rule: Foo . T ::= "foo" (Bind x U) "." (x)V;

    val label = new Id("Foo")
    val catT = new IdCat("T")
    val catU = new IdCat("U")
    val catV = new IdCat("V")
    val x = "x"

    val items = new ListItem()
    items.addLast(new Terminal("foo"))
    items.addLast(new BindNTerminal(x, catU))
    items.addLast(new Terminal("."))
    items.addLast(new AbsNTerminal(x, new NTerminal(catV)))

    val originalRule = new Rule(label, catT, items)
    val inputDefs = new ListDef()
    inputDefs.addLast(originalRule)

    // Apply transformation
    val resultDefs = BNFCRenderer.addDesugaredLambdas(inputDefs)

    // It should add exactly one new rule
    resultDefs.size() shouldBe 2

    val desugaredRule = resultDefs.get(1).asInstanceOf[Rule]

    // Check label: FooToArrow
    desugaredRule.label_ shouldBe a[Id]
    desugaredRule.label_.asInstanceOf[Id].ident_ shouldBe "FooToArrow"

    // First item: Terminal("FooToArrow")
    val itemsOut = desugaredRule.listitem_
    itemsOut.get(0) shouldBe a[Terminal]
    itemsOut.get(0).asInstanceOf[Terminal].string_ shouldBe "FooToArrow"

    // Second item: NTerminal(ArrowCat(U, V))
    itemsOut.get(1) shouldBe a[NTerminal]
    val arrowCat = itemsOut.get(1).asInstanceOf[NTerminal].cat_
    arrowCat shouldBe a[ArrowCat]
    val ac = arrowCat.asInstanceOf[ArrowCat]
    ac.cat_1 shouldBe catU
    ac.cat_2 shouldBe catV
  }
}
