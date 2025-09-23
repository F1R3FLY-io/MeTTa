package io.f1r3fly.mettail

import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.collection.mutable
import scala.collection.mutable.Map
import scala.jdk.CollectionConverters._
import io.f1r3fly.mettail.DottedPathUtils.dottedPathToString

object Hypercube {

  /**  
    * Given an untyped BasePres, produce a new, typed BasePres  
   */
  def transform(base: BasePres): BasePres = {
    val origDefs = base.listdef_.asScala.toList
    val origEqs  = base.listequation_.asScala.toList
    val origRws  = base.listrewritedecl_.asScala.toList

    // Create a list of type-lifted defs
    val typeLiftedDefs = typeLift(base.listdef_)
    val origDefsMap = defsToRuleMap(origDefs)
    println("origDefsMap:")
    for ((label, rule) <- origDefsMap) {
      println(s"${PrettyPrinter.print(label)} -> ${PrettyPrinter.print(rule)}")
    }
    println("typeLiftedDefs:")
    for ((labelCase, rule) <- typeLiftedDefs) {
      println(s"${labelCase} -> ${PrettyPrinter.print(rule)}")
    }
    // Add extra parameters for those appearing in LHS of base rewrites with repeated values
    val extendedDefs = extend(base, origDefsMap, typeLiftedDefs)
    // Add modal types for the process-shaped subtrees of LHS of base rewrites
    /*
      Let a *base reduction* be a function symbol whose input arity does not 
      use R and whose output arity is R.  For each base reduction B: ∏ᵢ Aᵢ -> R, 
      consider the actual source of B, C = src ⚬ B: ∏ᵢ Aᵢ -> P.
 
      - The abstract syntax tree for C has internal nodes labeled by function 
        symbols and leaves labeled by shapes.  For each occurrence of P as an 
        input to a function symbol in the AST, we get two possibility modal 
        types expressing the fact that the process-shaped subtree of the AST 
        in the context surrounding that subtree possibly reduces to the target 
        of the base reduction.  One of the possibility modal types is 
        "independent", and only has type information; the other is "dependent", 
        and tracks the specific target process as well.
         - For example, src(comm(T, U, V)) = |(!(T, V), ?(T, U)).  There are 
           three process-shaped proper subtrees of |(!(T, V), ?(T, U)):
       
           1. V in the context |(!(T, []), ?(T, U)), giving rise to the modal types ctxcomm_i and ctxcomm_d
           2. !(T, V) in the context |([], ?(T, U)), giving rise to the modal types ctxrecv_i and ctxrecv_d
           3. ?(T, U) in the context |(!(T, V), []), giving rise to the modal types ctxsend_i and ctxsend_d
       
           I chose names for the modal type function symbols based on my 
           knowledge of the semantics of the comm rule, but a formal transformation 
           should choose names based on the location of the subtree instead.
  
      Finally, we add the function symbols ctxposs_i: P -> P and ctxposs_d: P x P -> P.
    */
    // extendedDefs.addAll(contextModals(base))
    // Add modal types for arbitrary reductions
    // extendedDefs.addAll(generalModals())

    BasePresOps.copyPres(
      base,
      listdef = Some(origDefs ++ extendedDefs.asScala.toList)
    )
  }

  sealed trait LabelCase

  case class LCId(ident: String) extends LabelCase
  case object LCWild extends LabelCase
  case class LCListE(cat: Cat) extends LabelCase
  case class LCListCons(cat: Cat) extends LabelCase
  case class LCListOne(cat: Cat) extends LabelCase
  
  private def labelToLabelCase(l: Label) = l match {
    case id: Id => LCId(id.ident_)
    case _: Wild => LCWild
    case le: ListE => LCListE(le.cat_)
    case lc: ListCons => LCListE(lc.cat_)
    case lo: ListOne => LCListE(lo.cat_)
  }
  
  private def defsToRuleMap(defs: List[Def]): Map[Label, Rule] = {
    Map.from(defs.map { d =>
      val rule = d.asInstanceOf[Rule]
      rule.label_ -> rule
    }.toMap)
  }
  
  private def typeLiftDef(defn: Def): Option[Rule] = defn match {
    case r: Rule => {
      println(s"type lifting ${PrettyPrinter.print(r)}")
      val result = new Rule(
        // Name mangle the original
        new Id(s"TypeLiftCC${r.label_.asInstanceOf[Id].ident_}DD"),
        transform(r.cat_),
        new ListItem()
      )
      // Use the mangled name and matching parens for the syntax
      result.listitem_.add(Terminal(result.label_.asInstanceOf[Id].ident_))
      result.listitem_.add(Terminal("("))
      var hasBind = false
      for (item <- r.listitem_.asScala) {
        item match {
          case t: Terminal => ()
          case nt: NTerminal => result.listitem_.add(new NTerminal(transform(nt.cat_)))
          case ant: AbsNTerminal => hasBind = true
          case bnt: BindNTerminal => hasBind = true
        }
      }
      result.listitem_.add(Terminal(")"))
      if (hasBind) { 
        println(s"Found binder, ignoring")
        None 
      } else { Some(result) }
    }
    case _ => None
  }

  private def transform(cat: Cat): Cat = {
    cat match {
      case ic: IdCat => ic
      case loc: ListOfCat => new ListOfCat(transform(loc.cat_))
      case ac: ArrowCat => {
        val result = new ProdCat(new ListCat())
        val first = transform(ac.cat_1)
        val second = transform(ac.cat_2)
        result.listcat_.add(first)
        result.listcat_.add(new ArrowCat(first, second))
        result
      }
      case pc: ProdCat => {
        val result = new ProdCat(new ListCat())
        result.listcat_.addAll(pc.listcat_.asScala.map(transform).asJava)
        result
      }
    }
  }

  private def typeLift(defs: ListDef): Map[LabelCase, Rule] = {
    val result = Map.empty[LabelCase, Rule]
    for (defn <- defs.asScala) {
      typeLiftDef(defn) match {
        case Some(d) => result += labelToLabelCase(defn.asInstanceOf[Rule].label_) -> d
        case None => ()
      }
    }
    result
  }
  
  private def labelCaseToString(label: LabelCase) = 
  {
    def mangle(cat: Cat, prefix: String): String = {
      val mangledCat = BNFCRenderer.mangleCat(
        cat,
        mutable.Set.empty[(IdCat, IdCat)],
        mutable.Set.empty[List[IdCat]]
      )
      s"${prefix}CC{mangledCat}DD"
    }
    label match {
      case LCId(ident) => ident
      case LCWild => "_";
      case LCListE(cat) => mangle(cat, "ListECC")
      case LCListCons(cat) => mangle(cat, "ListConsCC")
      case LCListOne(cat) => mangle(cat, "ListOneCC")
    }
  }
  
  private def extend(
    base: BasePres,
    origDefs: Map[Label, Rule],
    typeLiftedDefs: Map[LabelCase, Rule]
  ): ListDef = {
    val lcods = origDefs.map((label, rule) => labelToLabelCase(label) -> rule)
    // Find LHSs of base rewrites in base
    for (rw <- base.listrewritedecl_.asScala) {
      val rd = rw.asInstanceOf[RDecl]
      rd.rewrite_ match {
        case rb: RewriteBase => {
          // Look for repeated free variables in LHS
          val repeated = freeVarsInAST(rb.ast_1).filter { case (_, sexps) => sexps.size > 1 }.toSet
          // For each repeated variable, add a parameter to the type lifted def containing it
          for ((varName, sexps) <- repeated) {
            for (sexp <- sexps) {
              var lc = labelToLabelCase(sexp.label_)
              var maybetlr = typeLiftedDefs.get(lc)
              var arrowId = ""
              if (maybetlr == None && sexp.label_.isInstanceOf[Id]) {
                arrowId = s"${sexp.label_.asInstanceOf[Id].ident_}ToArrow"
                maybetlr = typeLiftedDefs.get(labelToLabelCase(new Id(arrowId)))
              }
              if (maybetlr == None) {
                println(s"Couldn't find ${PrettyPrinter.print(sexp.label_)} or ${arrowId}")
              } else {
                val tlr = maybetlr.get
                val coiia = AddEqRwHelpers.catOfIdentInAST(varName, origDefs.toMap, None, sexp)
                val cat = coiia.asInstanceOf[AddEqRwHelpers.COIIAConcrete].cat
                val li = tlr.listitem_
                // Add the extra item before the final close paren
                li.add(li.size() - 1, new NTerminal(cat))
              }
            }
          }
        }
        case _ => ()
      }
    }
    // Return the list of values in the map
    val result = new ListDef()
    result.addAll(typeLiftedDefs.values.asJavaCollection)
    result
  }
  
  /**  
   * Returns a map from each free‐var name to the set of ASTSExp nodes
   * that directly contain it.  If the var is at the top level (i.e. the
   * AST itself is an ASTVar), the set will be empty.  
   */
  def freeVarsInAST(ast: AST): Map[String, Set[ASTSExp]] = {
    // mutable map from var name → set of ASTSExp
    val result = Map.empty[String, Set[ASTSExp]]

    def helper(node: AST, parent: Option[ASTSExp]): Unit = node match {
      case v: ASTVar =>
        val name = dottedPathToString(v.dottedpath_)
        parent match {
          case Some(p) =>
            // get the existing set (or empty), then add `p`
            val prevSet = result.getOrElse(name, Set.empty[ASTSExp])
            result(name) = prevSet + p

          case None =>
            // ensure there’s at least an empty set for top‐level vars
            result.getOrElseUpdate(name, Set.empty[ASTSExp])
        }

      case s: ASTSExp =>
        s.listast_.asScala.foreach(child => helper(child, Some(s)))
    }

    helper(ast, None)
    result
  }
}
