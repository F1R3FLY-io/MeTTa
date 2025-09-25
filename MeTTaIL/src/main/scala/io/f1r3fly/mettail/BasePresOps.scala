package io.f1r3fly.mettail

import metta_venus.Absyn._
import scala.jdk.CollectionConverters._

object BasePresOps {
  // Create an empty instance by calling the no-argument constructors.
  def empty: BasePres = {
    val listCat = new metta_venus.Absyn.ListCat()
    val listDef = new metta_venus.Absyn.ListDef()
    val listEquation = new metta_venus.Absyn.ListEquation()
    val listRewriteDecl = new metta_venus.Absyn.ListRewriteDecl()
    val listMapEntry = new metta_venus.Absyn.ListMapEntry()
    new BasePres(listCat, listDef, listEquation, listRewriteDecl, listMapEntry)
  }

  // copyPres creates new list instances and adds the updated elements.
  def copyPres(
    pres: BasePres,
    listcat: Option[List[Cat]] = None,
    listdef: Option[List[Def]] = None,
    listequation: Option[List[Equation]] = None,
    listrewritedecl: Option[List[RewriteDecl]] = None,
    listmapentry: Option[List[MapEntry]] = None
  ): BasePres = {
    val newListCat = new metta_venus.Absyn.ListCat()
    val newListDef = new metta_venus.Absyn.ListDef()
    val newListEquation = new metta_venus.Absyn.ListEquation()
    val newListRewriteDecl = new metta_venus.Absyn.ListRewriteDecl()
    val newListMapEntry = new metta_venus.Absyn.ListMapEntry()

    val cats = listcat.getOrElse(pres.listcat_.asScala.toList)
    newListCat.addAll(cats.asJava)
    val defs = listdef.getOrElse(pres.listdef_.asScala.toList)
    newListDef.addAll(defs.asJava)
    val equations = listequation.getOrElse(pres.listequation_.asScala.toList)
    newListEquation.addAll(equations.asJava)
    val rewrites = listrewritedecl.getOrElse(pres.listrewritedecl_.asScala.toList)
    newListRewriteDecl.addAll(rewrites.asJava)
    val mapEntries = listmapentry.getOrElse(pres.listmapentry_.asScala.toList)
    newListMapEntry.addAll(mapEntries.asJava)

    new BasePres(newListCat, newListDef, newListEquation, newListRewriteDecl, newListMapEntry)
  }
  
  // Converts the list of defs in a BasePres to a map.
  def listDefToMap(listDef: ListDef): Map[Label, Rule] = {
    listDef.asScala.collect {
      case rule: Rule => rule.label_ -> rule
    }.toMap
  }  
}
