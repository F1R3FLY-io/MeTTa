package io.f1r3fly.mettail

import org.antlr.v4.runtime.{ANTLRInputStream, CommonTokenStream}
import metta_venus.Absyn._
import metta_venus.{MettaVenusLexer, MettaVenusParser, PrettyPrinter}
import scala.collection.mutable
import scala.jdk.CollectionConverters._

class ModuleProcessor(fs: FileSystem) {

  def dottedPathToString(dottedPath: DottedPath): String =
    dottedPath match {
      case bdp: BaseDottedPath           => bdp.ident_
      case qdp: QualifiedDottedPath =>
        s"${qdp.ident_}.${dottedPathToString(qdp.dottedpath_)}"
    }

  def resolveModules(entryPath: String): Map[String, Module] = {
    // A mutable map from canonical file paths to parsed modules.
    val loaded = mutable.Map[String, Module]()

    def resolveModule(path: String): Unit = {
      // Normalize. If this module is already loaded, skip reloading.
      val canonicalPath = fs.canonical(path)
      if (loaded.contains(canonicalPath)) return

      // Open and parse the module.
      val rdr    = fs.reader(canonicalPath)
      val lexer  = new MettaVenusLexer(new ANTLRInputStream(rdr))
      lexer.addErrorListener(new BNFCErrorListener)
      val tokens = new CommonTokenStream(lexer)
      val parser = new MettaVenusParser(tokens)
      parser.addErrorListener(new BNFCErrorListener)
      val pc     = parser.start_Module()
      val mod    = pc.result.asInstanceOf[Module]

      // Add the parsed module to the cache.
      loaded(canonicalPath) = mod

      val parentDir = fs.parent(canonicalPath)

      // Walk imports.
      mod match {
        case m: ModuleImpl =>
          m.listimport_.asScala.foreach {
            case imp: ImportModuleAs =>
              val importedPath = fs.canonical(fs.join(parentDir, imp.string_))
              resolveModule(importedPath)

            case imp: ImportFromModule =>
              val importedPath = fs.canonical(fs.join(parentDir, imp.string_))
              resolveModule(importedPath)

            case _ => ()
          }

        case _ => ()
      }
    }

    resolveModule(entryPath)
    loaded.toMap
  }

  // Helper function to search for a theory declaration with the given name in a module.
  def findTheoryDeclInModule(m: ModuleImpl, theoryName: String): Option[TheoryDecl] =
    m.listprog_.asScala.flatMap {
      case pt: ProgTheoryDecl =>
        pt.theorydecl_ match {
          case bt: BaseTheoryDecl =>
            bt.name_ match {
              case nv: NameVar if nv.ident_ == theoryName => Some(pt.theorydecl_)
              case nw: NameWildcard if theoryName == "_"  => Some(pt.theorydecl_)
              case _                                      => None
            }
          case _ => None
        }
      case _ => None
    }.headOption

  /** Resolve a dotted path to a theory declaration.
    *
    * The parameter `dottedPath` is either a single identifier (BaseDottedPath)
    * or a pair (QualifiedDottedPath) where the first element identifies a module
    * imported via ImportModuleAs and the second is the name of a theory declaration.
    *
    * If dottedPath is a single element, we first look for a theory declaration
    * in the current module. If not found there, we look for an ImportFromModule
    * whose alias matches the identifier, and then search that imported module.
    *
    * @param resolvedModules a map from canonical module paths to parsed Module ASTs.
    * @param canonicalPathToCurrentModule the canonical path of the current module.
    * @param dottedPath the dotted path to resolve.
    * @return Either an error message (Left) or a pair consisting of the canonical path of
    *         the module that contains the theory and the resolved TheoryDecl (Right).
    */
  def resolveDottedPath(
      resolvedModules: Map[String, Module],
      currentModulePath: String,
      dottedPath: DottedPath
  ): Either[String, (String, TheoryDecl)] = {
    def load(path: String) = resolvedModules.get(path).toRight("Module not found: " + path)

    load(currentModulePath).flatMap {
      case m: ModuleImpl =>
        dottedPath match {
          // Single-element dotted path.
          case bp: BaseDottedPath =>
            val name = bp.ident_
            // First try to find the theory in the current module.
            findTheoryDeclInModule(m, name) match {
              case Some(td) => Right(currentModulePath -> td)
              case None =>
                // Not found in the current module; check each ImportFromModule.
                m.listimport_.asScala.collectFirst {
                  case imp: ImportFromModule if imp.ident_ == name => imp
                } match {
                  case Some(imp) =>
                    val importedPath = fs.canonical(fs.join(currentModulePath, imp.string_))
                    load(importedPath).flatMap {
                      case im: ModuleImpl =>
                        findTheoryDeclInModule(im, name)
                          .toRight(s"Theory '$name' not found in module $importedPath}"
                                   + s"\nImported module: ${PrettyPrinter.print(im)}")
                          .map(importedPath -> _)
                      case nami => Left(s"Module at $importedPath is not a ModuleImpl:" 
                                        + s"\n${PrettyPrinter.print(nami)}")
                    }
                  case None =>
                    Left(s"Theory '$name' not found in $currentModulePath or imports")
                }
            }

          case qp: QualifiedDottedPath =>
            qp.dottedpath_ match {
              case inner: BaseDottedPath =>
                val alias      = qp.ident_
                val theoryName = inner.ident_
                m.listimport_.asScala.collectFirst {
                  case imp: ImportModuleAs if imp.ident_ == alias => imp
                } match {
                  case Some(imp) =>
                    val importedPath = fs.canonical(fs.join(currentModulePath, imp.string_))
                    load(importedPath).flatMap {
                      case im: ModuleImpl =>
                        findTheoryDeclInModule(im, theoryName)
                          .toRight(s"Theory '$theoryName' not in $importedPath")
                          .map(importedPath -> _)
                      case _ => Left("Not a ModuleImpl: " + importedPath)
                    }
                  case None =>
                    Left(s"Module alias '$alias' not found in ImportModuleAs statements of $currentModulePath")
                }

              case _ => Left("Invalid dotted path: expected a base dotted path,"
                             + s" but got ${PrettyPrinter.print(qp.dottedpath_)}")
            }
        }

      case _ => Left(s"Current module is not a ModuleImpl: $currentModulePath")
    }
  }
}

object ModuleProcessor {
  def default: ModuleProcessor = new ModuleProcessor(new RealFileSystem)
}
