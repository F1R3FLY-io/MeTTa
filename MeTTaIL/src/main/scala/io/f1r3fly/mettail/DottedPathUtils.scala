package io.f1r3fly.mettail

import metta_venus.Absyn._

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
}
