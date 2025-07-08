package io.f1r3fly.mettail

import metta_venus.Absyn._
import org.antlr.v4.runtime.{ANTLRInputStream, CommonTokenStream}
import scala.jdk.CollectionConverters._
import io.f1r3fly.mettail.FileSystem
import io.f1r3fly.mettail.RealFileSystem
import metta_venus.{MettaVenusLexer, MettaVenusParser, PrettyPrinter}

final case class TheoryEnv(map: Map[DottedPath, (TheoryDecl, TheoryEnv)])

/**
 * Parameterized builder for TheoryEnv that decouples file I/O via FileSystem.
 */
class TheoryEnvBuilder(fs: FileSystem) {

  /** Merge two theory environments, with env2 taking precedence on conflicts. */
  def merge(env1: TheoryEnv, env2: TheoryEnv): TheoryEnv =
    TheoryEnv(env1.map ++ env2.map)

  /** Build a theory environment from a Module AST.
    * For each theory declaration (TheoryDecl) in a ProgDecl, we extract its qualified name.
    * Then we process each import to merge in the imported module’s environment.
    */
  def build(module: Module): TheoryEnv = module match {
    case m: ModuleImpl =>
      // Build the "self" environment from theory declarations declared in this module.
      val selfMap: Map[DottedPath, (TheoryDecl, TheoryEnv)] =
        m.listprog_.iterator.asScala.toList.collect {
          case ptd: ProgTheoryDecl => ptd.theorydecl_ match {
            case thDecl: TheoryDecl =>
              val key = extractDottedPath(thDecl)
              key -> (thDecl, TheoryEnv(Map.empty))
          }
        }.toMap

      // Process imports and merge in the imported module environments.
      val importMap: Map[DottedPath, (TheoryDecl, TheoryEnv)] =
        m.listimport_.iterator.asScala.toList.flatMap {
          case i: ImportModuleAs =>
            // Qualify every entry from the imported environment using the alias
            loadTheoryEnv(i.string_).map.map { case (dp, pair) =>
              (qualifyDottedPath(i.ident_, dp), pair)
            }.toList
          case i: ImportFromModule =>
            // For "import from", pick the entry whose last identifier matches the provided name.
            loadTheoryEnv(i.string_).map.find { case (dp, _) =>
              getLastIdentifier(dp) == i.ident_
            }.toList
          case _ => Nil
        }.toMap

      TheoryEnv(selfMap ++ importMap)
    case _ => TheoryEnv(Map.empty)
  }

  /** Load and parse a module file into a TheoryEnv, using fs for I/O. */
  def loadTheoryEnv(path: String): TheoryEnv = {
    try {
      // Normalize path
      val canonicalPath = fs.canonical(path)
      // Open reader via FileSystem
      val rdr = fs.reader(canonicalPath)
      val lexer = new MettaVenusLexer(new ANTLRInputStream(rdr))
      val tokens = new CommonTokenStream(lexer)
      val parser = new MettaVenusParser(tokens)
      val pc = parser.start_Module()
      val mod = pc.result.asInstanceOf[Module]
      build(mod)
    } catch {
      case _: Exception => TheoryEnv(Map.empty)
    }
  }

  /** Extract a DottedPath from a TheoryDecl. */
  def extractDottedPath(thDecl: TheoryDecl): DottedPath =
    new BaseDottedPath(thDecl match {
      case btd: BaseTheoryDecl => btd.name_ match {
        case _: NameWildcard => "_"
        case nameVar: NameVar => nameVar.ident_
      }
    })

  /** Qualify a DottedPath by prepending an alias (a String) to the existing path.
    * For a BaseDottedPath, returns a QualifiedDottedPath with the alias and the base.
    * For a QualifiedDottedPath, similarly prepends the alias.
    */
  def qualifyDottedPath(alias: String, dp: DottedPath): DottedPath = dp match {
    case b: BaseDottedPath       => new QualifiedDottedPath(alias, b)
    case q: QualifiedDottedPath  => new QualifiedDottedPath(alias, q)
    case _                       => dp
  }

  /** Get the last identifier from a DottedPath. */
  def getLastIdentifier(dp: DottedPath): String = dp match {
    case b: BaseDottedPath      => b.ident_
    case q: QualifiedDottedPath => getLastIdentifier(q.dottedpath_)
    case _                      => ""
  }

  /** Convert a DottedPath to its string representation. */
  def dottedPathToString(dp: DottedPath): String = dp match {
    case b: BaseDottedPath      => b.ident_
    case q: QualifiedDottedPath => s"${q.ident_}.${dottedPathToString(q.dottedpath_)}"
    case _                      => ""
  }

  /** Pretty-print the theory environment. */
  def prettyPrint(env: TheoryEnv): String =
    env.map.map { case (dp, (decl, _)) =>
      s"${dottedPathToString(dp)} -> ${PrettyPrinter.print(decl)}"
    }.mkString("\n")
}

/** Default builder using the real filesystem. */
object TheoryEnv extends TheoryEnvBuilder(new RealFileSystem)
