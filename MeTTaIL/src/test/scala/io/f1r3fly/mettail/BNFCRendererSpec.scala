package io.f1r3fly.mettail

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import scala.jdk.CollectionConverters._

class BNFCRendererSpec extends AnyFlatSpec with Matchers {
  "BNFCRenderer.render" should "mangle ArrowCat and ProdCat correctly and add constructor rules" in {
    val catA = new IdCat("A")
    val catB = new IdCat("B")
    val arrowCat = new ArrowCat(catA, catB)
    val prodCat = new ProdCat({
      val list = new ListCat()
      list.add(catA)
      list.add(catB)
      list
    })

    val arrowRule = new Rule(
      new Id("arrowRule"),
      arrowCat,
      {
        val list = new ListItem()
        list.add(new Terminal("some"))
        list
      }
    )

    val prodRule = new Rule(
      new Id("prodRule"),
      prodCat,
      {
        val list = new ListItem()
        list.add(new Terminal("other"))
        list
      }
    )

    val defs = new ListDef()
    defs.add(arrowRule)
    defs.add(prodRule)

    val basePres = new BasePres(new ListCat(), defs, new ListEquation(), new ListRewriteDecl())

    val result = BNFCRenderer.render(basePres)

    val labels = result.asScala.collect {
      case r: Rule => r.label_ match {
        case id: Id => id.ident_
        case _ => "<unknown>"
      }
    }.toSet

    val expectedAppName = s"AppCC${catA.ident_}_${catB.ident_}DD"
    val expectedLamName = s"LamCC${catA.ident_}_${catB.ident_}DD"
    val expectedIdentArrow = s"IdentCC${catA.ident_}_${catB.ident_}DD"
    val expectedMakeProd = s"MakeProdCC${catA.ident_}_${catB.ident_}DD"

    labels should contain(expectedAppName)
    labels should contain(expectedLamName)
    labels should contain(expectedIdentArrow)
    labels should contain(expectedMakeProd)
  }
}
