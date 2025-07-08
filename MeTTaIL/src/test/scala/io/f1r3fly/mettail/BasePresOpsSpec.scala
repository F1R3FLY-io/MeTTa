package io.f1r3fly.mettail

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import io.f1r3fly.mettail.BasePresOps
import scala.jdk.CollectionConverters._

class BasePresOpsSpec extends AnyFlatSpec with Matchers {
  "empty" should "produce a BasePres with all empty lists" in {
    val pres = BasePresOps.empty
    pres.listcat_.asScala shouldBe empty
    pres.listdef_.asScala shouldBe empty
    pres.listequation_.asScala shouldBe empty
    pres.listrewritedecl_.asScala shouldBe empty
  }

  "copyPres without overrides" should "clone the BasePres and maintain equality but not referential identity" in {
    val orig = BasePresOps.empty
    val copy = BasePresOps.copyPres(orig)
    copy shouldEqual orig
    copy should not be theSameInstanceAs(orig)
  }

  "copyPres with overrides" should "replace the specified lists" in {
    val cat = new IdCat("C1")
    val rule = new Rule(new Id("L1"), new IdCat("C1"), new ListItem())

    val pres = BasePresOps.empty
    val overridden = BasePresOps.copyPres(
      pres,
      listcat = Some(List(cat)),
      listdef = Some(List(rule))
    )

    overridden.listcat_.asScala.toList should contain only cat
    overridden.listdef_.asScala.toList should contain only rule
    // other lists remain empty
    overridden.listequation_.asScala shouldBe empty
    overridden.listrewritedecl_.asScala shouldBe empty
  }

  "listDefToMap" should "map Rule labels to Rule instances" in {
    val rule1 = new Rule(new Id("A"), new IdCat("C"), new ListItem())
    val rule2 = new Rule(new Id("B"), new IdCat("D"), new ListItem())
    val defs = new ListDef()
    defs.addLast(rule1)
    defs.addLast(rule2)

    val map = BasePresOps.listDefToMap(defs)
    map.keySet should contain allOf (rule1.label_, rule2.label_)
    map(rule1.label_) shouldEqual rule1
    map(rule2.label_) shouldEqual rule2
  }
}
