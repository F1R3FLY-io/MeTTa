package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.collection.mutable
import scala.jdk.CollectionConverters._

object BNFCRenderer {
  def render(basePres: BasePres): Grammar = {
    var listDef = addDesugaredLambdas(basePres.listdef_)
    listDef = monomorphizeArrows(listDef)
    // TODO: add term constructors for rewrites
    new MkGrammar(listDef)
  }
  
  def mangleBindLabel(labelStr: String): String = {
    labelStr + "ToArrow"
  }

  def idCatPairToMangledArrow(src: IdCat, tgt: IdCat): IdCat =
    new IdCat(s"ArrowCC${src.ident_}_${tgt.ident_}DD")

  // Name-mangles arrow types and lists under an arrow.
  // Whenever an arrow type is encountered, it's added to acs.
  // CC and DD are used as parens in the mangling, underscore as arrow.
  // E.g. [A -> B]   becomes [ArrowCCA_BDD]
  //      [A] -> [B] becomes ArrowCCListCCADD_ListCCBDDDD
  // TODO: escape *CC, DD, and _ in the IdCat case.
  def mangleCat(cat: Cat, acs: mutable.Set[(IdCat, IdCat)]): Cat = {
    // The `arrowed` parameter should be set to false at the top level.
    //   It gets set to true internally when recursing on an arrow type.
    //   Whenever the flag is set to `true`, the result is an `IdCat`.
    def mcHelper(cat: Cat, arrowed: Boolean): Cat = {
      cat match {
        case loc: ListOfCat =>
          if (arrowed) {
            val mangled: IdCat = mcHelper(loc.cat_, true).asInstanceOf[IdCat]
            new IdCat(s"ListCC${mangled.ident_}DD")
          } else {
            new ListOfCat(mcHelper(loc.cat_, false))
          }
        case idc: IdCat => idc
        case ac: ArrowCat => {
          val src: IdCat = mcHelper(ac.cat_1, true).asInstanceOf[IdCat]
          val tgt: IdCat = mcHelper(ac.cat_2, true).asInstanceOf[IdCat]
          acs.add((src, tgt))
          idCatPairToMangledArrow(src, tgt)
        }
      }
    }
    mcHelper(cat, false)
  }

  // Adds a desugared form of each rule that involves a binder.
  // These AST nodes won't be used in the result of a parse, but
  // after the parse, the sugared nodes can be converted to
  // desugared ones.
  def addDesugaredLambdas(listDef: ListDef): ListDef = {
    val retList = new ListDef()
    for (defn <- listDef.asScala) {
      retList.add(defn)

      val rule = defn.asInstanceOf[Rule]
      val varToCat: mutable.Map[String, Cat] = mutable.Map()
      var hasBind = false

      for (item <- rule.listitem_.asScala) {
        item match {
          case bnt: BindNTerminal => {
            varToCat(bnt.ident_) = bnt.cat_
            hasBind = true
          }
          case _ => ()
        }
      }

      if (hasBind) {
        val labelStr = mangleBindLabel(rule.label_.asInstanceOf[Id].ident_)
        val items = new ListItem()
        items.add(Terminal(labelStr))
        val r = new Rule(Id(labelStr), rule.cat_, items)

        for (item <- rule.listitem_.asScala) {
          item match {
            case nt: NTerminal => {
              r.listitem_.add(new NTerminal(nt.cat_))
            }
            case ant: AbsNTerminal => {
              val stack: mutable.Stack[Item] = mutable.Stack()
              stack.push(item)
              while (stack.top.isInstanceOf[AbsNTerminal]) {
                stack.push(stack.top.asInstanceOf[AbsNTerminal].item_)
              }
              var p = stack.pop().asInstanceOf[NTerminal].cat_
              while (stack.nonEmpty) {
                val sourceVar = stack.pop().asInstanceOf[AbsNTerminal].ident_
                p = new ArrowCat(varToCat(sourceVar), p)
              }
              r.listitem_.add(new NTerminal(p))
            }
            case _ => ()
          }
        }
        retList.add(r)
      }
    }
    retList
  }
  
  // Name mangle arrow types and add constructors
  def monomorphizeArrows(listDef: ListDef): ListDef = {
    // Make a set of Cat called `arrows` for the arrow categories found
    val arrows: mutable.Set[(IdCat, IdCat)] = mutable.Set()
    // Name mangle the arrow categories in the rules and
    //   collect the original arrow categories in `arrows`.
    val mangled = listDef.asScala.map(defn => {
      val rule = defn.asInstanceOf[Rule]
      def mangleCatInItem(item: Item): Item = item match {
        case t: Terminal => t
        case nt: NTerminal => new NTerminal(mangleCat(nt.cat_, arrows))
        case ant: AbsNTerminal =>
          new AbsNTerminal(ant.ident_, mangleCatInItem(ant.item_))
        case bnt: BindNTerminal =>
          new BindNTerminal(bnt.ident_, mangleCat(bnt.cat_, arrows))
      }
      val scalaItems = rule.listitem_.asScala.map(mangleCatInItem)
      val javaItems = new ListItem()
      javaItems.addAll(scalaItems.asJava)
      new Rule(
        rule.label_,
        mangleCat(rule.cat_, arrows),
        javaItems
      ).asInstanceOf[Def]
    })
    // For each arrow in arrows
    for ((t1, t2) <- arrows) {
      // Add the four constructors to mangled

      // AppT1T2 . T2 ::= "α" "{" (T1 -> T2) "(" T1 ")" "}" ;
      val appT1T2ListItem = new ListItem()
      val appT1T2Items: List[Item] = List(
        new Terminal("α"),
        new Terminal("{"),
        new NTerminal(idCatPairToMangledArrow(t1, t2)),
        new Terminal("("),
        new NTerminal(t1),
        new Terminal(")"),
        new Terminal("}")
      )
      appT1T2ListItem.addAll(appT1T2Items.asJava)
      val appT1T2Rule: Def = new Rule(
        new Id(s"AppCC${t1.ident_}_${t2.ident_}DD"),
        t2,
        appT1T2ListItem
      )
      mangled += appT1T2Rule

      // IdentT1T2 . (T1 -> T2) ::= Ident ;
      val identT1T2ListItem = new ListItem()
      identT1T2ListItem.add(new NTerminal(IdCat("Ident")))
      val identT1T2Rule: Def = new Rule(
        new Id(s"IdentCC${t1.ident_}_${t2.ident_}DD"),
        idCatPairToMangledArrow(t1, t2),
        identT1T2ListItem
      )
      mangled += identT1T2Rule
      
      // LamT1T2 . (T1 -> T2) ::= "λ" "{" "(" Ident ")" "=>" T2 "}" ;
      val lamT1T2ListItem = new ListItem()
      val lamT1T2Items: List[Item] = List(
        new Terminal("λ"),
        new Terminal("{"),
        new Terminal("("),
        new NTerminal(new IdCat("Ident")),
        new Terminal(")"),
        new Terminal("=>"),
        new NTerminal(t2),
        new Terminal("}"),
      )
      lamT1T2ListItem.addAll(lamT1T2Items.asJava)
      val lamT1T2Rule: Def = new Rule(
        new Id(s"LamCC${t1.ident_}_${t2.ident_}DD"),
        idCatPairToMangledArrow(t1, t2),
        lamT1T2ListItem
      )
      mangled += lamT1T2Rule
      
      // IdentT1 . T1 ::= Ident ;
      val identT1ListItem = new ListItem()
      identT1ListItem.add(new NTerminal(IdCat("Ident")))
      val identT1Rule: Def = new Rule(
        new Id(s"IdentCC${t1.ident_}DD"),
        t1,
        identT1ListItem
      )
      mangled += identT1Rule
    }
    val result = new ListDef()
    result.addAll(mangled.asJava)
    result
  }
}











