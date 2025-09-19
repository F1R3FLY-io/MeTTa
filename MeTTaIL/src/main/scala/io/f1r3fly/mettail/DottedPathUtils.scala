package io.f1r3fly.mettail

import metta_venus.Absyn._

object DottedPathUtils {

  // Convert a DottedPath to its string representation
  def dottedPathToString(dp: DottedPath): String = dp match {
    case b: BaseDottedPath      => b.ident_
    case q: QualifiedDottedPath => s"${q.ident_}.${dottedPathToString(q.dottedpath_)}"
    case _                      => ""
  }
}