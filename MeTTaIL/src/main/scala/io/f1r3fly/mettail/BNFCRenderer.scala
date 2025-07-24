package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.collection.mutable
import scala.jdk.CollectionConverters._

object BNFCRenderer {
  def render(basePres: BasePres): ListDef = {
    monomorphizeArrowsAndProducts(basePres.listdef_)
    // TODO: add term constructors for rewrites
  }

  def idCatPairToMangledArrow(src: IdCat, tgt: IdCat): IdCat =
    new IdCat(s"ArrowCC${src.ident_}_${tgt.ident_}DD")

  def idCatListToMangledProd(ids: List[IdCat]): IdCat = {
    val name = ids.map(_.ident_).mkString("_")
    new IdCat(s"ProdCC${name}DD")
  }

  def mangleCat(cat: Cat, acs: mutable.Set[(IdCat, IdCat)], pcs: mutable.Set[List[IdCat]]): Cat = {
    def mcHelper(cat: Cat, mangling: Boolean): Cat = {
      cat match {
        case loc: ListOfCat =>
          if (mangling) {
            val mangled: IdCat = mcHelper(loc.cat_, true).asInstanceOf[IdCat]
            new IdCat(s"ListCC${mangled.ident_}DD")
          } else {
            new ListOfCat(mcHelper(loc.cat_, false))
          }
        case idc: IdCat => idc
        case ac: ArrowCat =>
          val src: IdCat = mcHelper(ac.cat_1, true).asInstanceOf[IdCat]
          val tgt: IdCat = mcHelper(ac.cat_2, true).asInstanceOf[IdCat]
          acs.add((src, tgt))
          idCatPairToMangledArrow(src, tgt)
        case pc: ProdCat =>
          val ids: List[IdCat] = pc.listcat_.asScala.map(
            mcHelper(_, true).asInstanceOf[IdCat]
          ).toList
          pcs.add(ids)
          idCatListToMangledProd(ids)
      }
    }
    mcHelper(cat, false)
  }

  def monomorphizeArrowsAndProducts(listDef: ListDef): ListDef = {
    val arrows: mutable.Set[(IdCat, IdCat)] = mutable.Set()
    val prods: mutable.Set[List[IdCat]] = mutable.Set()

    val mangled = listDef.asScala.map(defn => {
      val rule = defn.asInstanceOf[Rule]
      def mangleCatInItem(item: Item): Item = item match {
        case t: Terminal => t
        case nt: NTerminal => new NTerminal(mangleCat(nt.cat_, arrows, prods))
        case ant: AbsNTerminal =>
          new AbsNTerminal(ant.ident_, mangleCatInItem(ant.item_))
        case bnt: BindNTerminal =>
          new BindNTerminal(bnt.ident_, mangleCat(bnt.cat_, arrows, prods))
      }
      val scalaItems = rule.listitem_.asScala.map(mangleCatInItem)
      val javaItems = new ListItem()
      javaItems.addAll(scalaItems.asJava)
      new Rule(
        rule.label_,
        mangleCat(rule.cat_, arrows, prods),
        javaItems
      ).asInstanceOf[Def]
    }).toBuffer

    // Arrow constructors
    for ((t1, t2) <- arrows) {
      val arrowCat = idCatPairToMangledArrow(t1, t2)

      // App
      val appItems = new ListItem()
      appItems.addAll(List(
        new Terminal("α"),
        new Terminal("{"),
        new NTerminal(arrowCat),
        new Terminal("("),
        new NTerminal(t1),
        new Terminal(")"),
        new Terminal("}")
      ).asJava)
      mangled += new Rule(new Id(s"AppCC${t1.ident_}_${t2.ident_}DD"), t2, appItems)

      // IdentT1T2
      val identArrowItems = new ListItem()
      identArrowItems.add(new NTerminal(new IdCat("Ident")))
      mangled += new Rule(new Id(s"IdentCC${t1.ident_}_${t2.ident_}DD"), arrowCat, identArrowItems)

      // Lambda
      val lamItems = new ListItem()
      lamItems.addAll(List(
        new Terminal("λ"),
        new Terminal("{"),
        new Terminal("("),
        new NTerminal(new IdCat("Ident")),
        new Terminal(")"),
        new Terminal("=>"),
        new NTerminal(t2),
        new Terminal("}")
      ).asJava)
      mangled += new Rule(new Id(s"LamCC${t1.ident_}_${t2.ident_}DD"), arrowCat, lamItems)

      // IdentT1
      val identT1ListItem = new ListItem()
      identT1ListItem.add(new NTerminal(new IdCat("Ident")))
      mangled += new Rule(new Id(s"IdentCC${t1.ident_}DD"), t1, identT1ListItem)
    }

    // Prod constructors
    for (idList <- prods) {
      val prodCat = idCatListToMangledProd(idList)
      val prodItems = new ListItem()
      prodItems.add(new Terminal("∏"))
      prodItems.add(new Terminal("{"))
      idList.foreach(c => prodItems.add(new NTerminal(c)))
      prodItems.add(new Terminal("}"))

      val label = new Id(s"Make${prodCat.ident_}")
      mangled += new Rule(label, prodCat, prodItems)
    }

    val result = new ListDef()
    result.addAll(mangled.asJava)
    result
  }
}

