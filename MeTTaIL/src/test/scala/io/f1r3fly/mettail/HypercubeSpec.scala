package io.f1r3fly.mettail

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import scala.jdk.CollectionConverters._

class HypercubeSpec extends AnyFunSuite with Matchers {

  test("transform should add type-lifted terms for base constructors like PZero and PPar") {
    val catProc = new IdCat("Proc")

    val rulePZero = new Rule(new Id("PZero"), catProc, mkItems("0"))
    val rulePPar  = new Rule(new Id("PPar"), catProc,
      mkItems("(", new NTerminal(catProc), "|", new NTerminal(catProc), ")"))

    val pres = BasePresOps.copyPres(
      BasePresOps.empty,
      listcat = Some(List(catProc)),
      listdef = Some(List(rulePZero, rulePPar))
    )

    val transformed = Hypercube.transform(pres)
    val labels = ruleLabels(transformed)

    labels should contain allOf ("TypeLiftCCPZeroDD", "TypeLiftCCPParDD")
  }

  test("transform should lift binders like PNew into PNewToArrow and TypeLiftCCPNewToArrowDD") {
    import io.f1r3fly.mettail.DesugarBinds

    val catProc = new IdCat("Proc")
    val catName = new IdCat("Name")

    val rulePNew = new Rule(new Id("PNew"), catProc,
      mkItems("new", new BindNTerminal("x", catName), "in", new AbsNTerminal("x", new NTerminal(catProc))))

    val pres = BasePresOps.copyPres(
      BasePresOps.empty,
      listcat = Some(List(catProc, catName)),
      listdef = Some(List(rulePNew))
    )

    // Desugar binders to produce PNewToArrow before hypercube
    val desugared  = DesugarBinds.transform(pres)
    val transformed = Hypercube.transform(desugared)
    val labels = ruleLabels(transformed)

    labels should contain ("PNewToArrow")
    labels should contain ("TypeLiftCCPNewToArrowDD")
  }

  test("transform should lift receives like PRecv into PRecvToArrow and TypeLiftCCPRecvToArrowDD") {
    import io.f1r3fly.mettail.DesugarBinds

    val catProc = new IdCat("Proc")
    val catName = new IdCat("Name")

    val rulePRecv = new Rule(new Id("PRecv"), catProc,
      mkItems("for", "(", new BindNTerminal("x", catName), "<-", new NTerminal(catName), ")",
              "{", new AbsNTerminal("x", new NTerminal(catProc)), "}"))

    val pres = BasePresOps.copyPres(
      BasePresOps.empty,
      listcat = Some(List(catProc, catName)),
      listdef = Some(List(rulePRecv))
    )

    // Desugar binders to produce PRecvToArrow before hypercube
    val desugared  = DesugarBinds.transform(pres)
    val transformed = Hypercube.transform(desugared)
    val labels = ruleLabels(transformed)

    labels should contain ("PRecvToArrow")
    labels should contain ("TypeLiftCCPRecvToArrowDD")
  }

  // Helpers
  private def mkItems(parts: Any*): ListItem = {
    val items = new ListItem()
    parts.foreach {
      case s: String if s.trim.nonEmpty => items.addLast(new Terminal(s))
      case nt: NTerminal                => items.addLast(nt)
      case b: BindNTerminal             => items.addLast(b)
      case a: AbsNTerminal              => items.addLast(a)
      case _                            => // skip
    }
    items
  }

  private def ruleLabels(pres: BasePres): Set[String] =
    pres.listdef_.asScala.collect {
      case rule: Rule => rule.label_ match {
        case id: Id => id.ident_
        case _       => ""
      }
    }.toSet
}
