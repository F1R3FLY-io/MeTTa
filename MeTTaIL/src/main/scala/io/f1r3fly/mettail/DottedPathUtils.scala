package io.f1r3fly.mettail

import metta_venus.Absyn._
import io.f1r3fly.mettail.ASTHelpers.{hypVars, leftVars, rightVars}
import scala.jdk.CollectionConverters._

object DottedPathUtils {

  // Convert a DottedPath to its string representation
  def dottedPathToString(dp: DottedPath): String = dp match {
    case b: BaseDottedPath      => b.ident_
    case q: QualifiedDottedPath => s"${q.ident_}.${dottedPathToString(q.dottedpath_)}"
    case _                      => ""
  }

  // Extract the prefix from a dotted path string (everything before the first dot)
  def extractPrefix(dottedPath: String): String = {
    val dotIndex = dottedPath.indexOf('.')
    if (dotIndex == -1) dottedPath // No dot found, entire string is the prefix
    else dottedPath.substring(0, dotIndex)
  }

  // Check that hypothesis dotted path prefixes match
  def checkHypothesisPathPrefixes(hVars: Set[(String, String)]): Either[String, Unit] = {
    hVars.foldLeft[Either[String, Unit]](Right(())) { case (acc, (src, tgt)) =>
      acc match {
        case Left(err) => Left(err) // short-circuit on first error
        case Right(_) =>
          val srcPrefix = extractPrefix(src)
          val tgtPrefix = extractPrefix(tgt)
          if (srcPrefix != tgtPrefix) {
            Left(s"Error: In hypothesis $src ~> $tgt, dotted path prefixes differ: '$srcPrefix' != '$tgtPrefix'")
          } else {
            Right(())
          }
      }
    }
  }

  // Check that all dotted path prefixes in a rewrite exist in the References section
  def checkDottedPathPrefixesInReferences(basePres: BasePres, rewrite: Rewrite, context: String): Option[String] = {
    import DottedPathUtils.extractPrefix
    // Get all variables from the rewrite (left, right, and hypothesis)
    val allVars = leftVars(rewrite) ++ rightVars(rewrite) ++
      hypVars(rewrite).flatMap { case (left, right) => Set(left, right) }
    // Extract all dotted path prefixes (variables that contain dots)
    val dottedVars = allVars.filter(_.contains("."))
    val prefixes = dottedVars.map(extractPrefix)
    // Get available references from the References section
    val availableRefs = basePres.listmapentry_.asScala.map {
      case mapEntry: MakeMapEntry => mapEntry.ident_
      case _ => ""
    }.toSet
    // Find any prefix that doesn't exist in References
    val missingPrefixes = prefixes -- availableRefs
    if (missingPrefixes.nonEmpty) {
      Some(s"Error: In $context, dotted path prefixes not found in References section: ${missingPrefixes.mkString(", ")}")
    } else {
      None
    }
  }

}
