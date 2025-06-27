package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.collection.mutable
import scala.collection.mutable.Stack
import scala.jdk.CollectionConverters._

object BNFCRenderer {
  def render(basePres: BasePres): Grammar = {
    var listDef = addDesugaredLambdas(basePres.listdef_)
    listDef = monomorphizeArrows(listDef)
    // TODO: add term constructors for rewrites
    new MkGrammar(listDef)
  }
  
  def arrowMangleLabel(labelStr: String): String = {
    labelStr + "ToArrow"
  }
  
  // Add a desugared form of each rule that involves a binder.
  // These AST nodes won't be used in the result of a parse, but
  // after the parse, the sugared nodes can be converted to
  // desugared ones.
  def addDesugaredLambdas(listDef: ListDef): ListDef = {
    val retList = new ListDef()
    for (defn <- listDef.asScala) {
      retList.add(defn)

      val rule = defn.asInstanceOf[Rule]
      val varToCat: mutable.Map[String, Cat] = mutable.Map()

      for (item <- rule.listitem_.asScala) {
        item match {
          case bnt: BindNTerminal => {
            varToCat(bnt.ident_) = bnt.cat_
          }
          case _ => ()
        }
      }

      val labelStr = arrowMangleLabel(rule.label_.asInstanceOf[Id].ident_)
      val items = new ListItem()
      items.add(Terminal(labelStr))
      val r = new Rule(Id(labelStr), rule.cat_, items)

      for (item <- rule.listitem_.asScala) {
        item match {
          case nt: NTerminal => {
            r.listitem_.add(new NTerminal(nt.cat_))
          }
          case ant: AbsNTerminal => {
            val stack: Stack[Item] = Stack()
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
    retList
  }
  
  // Name mangle arrow types and add constructors
  def monomorphizeArrows(listDef: ListDef): ListDef = {
    listDef
  }
}