package io.f1r3fly.mettail

import java.io.{File, FileReader, Reader}
import org.antlr.v4.runtime.ANTLRInputStream
import org.antlr.v4.runtime.CommonTokenStream
import metta_venus.Absyn._
import metta_venus.{MettaVenusLexer, MettaVenusParser, PrettyPrinter}
import scala.collection.mutable
import scala.jdk.CollectionConverters._

object ModuleProcessor {

  def dottedPathToString(dottedPath: DottedPath): String =
    dottedPath match {
      case bdp: BaseDottedPath => bdp.ident_
      case qdp: QualifiedDottedPath => s"${qdp.ident_}.${dottedPathToString(qdp.dottedpath_)}"
    }

  def resolveModules(entryPath: String): Map[String, Module] = {
    // A mutable map from canonical file paths to parsed modules.
    val loaded = mutable.Map[String, Module]()

    def resolveModule(path: String): Unit = {
      val file = new File(path)
      val canonicalPath = file.getCanonicalPath

      // If this module is already loaded, skip reloading.
      if (loaded.contains(canonicalPath)) return

      // Open and parse the module.
      val reader: Reader = new FileReader(file)
      val lexer = new MettaVenusLexer(new ANTLRInputStream(reader))
      lexer.addErrorListener(new BNFCErrorListener)
      val tokens = new CommonTokenStream(lexer)
      val parser = new MettaVenusParser(tokens)
      parser.addErrorListener(new BNFCErrorListener)
      val pc = parser.start_Module()
      val mod = pc.result.asInstanceOf[Module]

      // Add the parsed module to the cache.
      loaded(canonicalPath) = mod

      // Process each import statement in the module.
      // We assume that if the parsed module is an instance of ModuleImpl,
      // it has a field `listimport_` containing the list of import statements.
      mod match {
        case m: ModuleImpl =>
          m.listimport_.asScala.foreach {
            case imp: ImportModuleAs =>
              val importedFile = new File(file.getParentFile, imp.string_)
              resolveModule(importedFile.getCanonicalPath)
            case imp: ImportFromModule =>
              val importedFile = new File(file.getParentFile, imp.string_)
              resolveModule(importedFile.getCanonicalPath)
            case _ => ()
          }
        case _ => ()
      }
    }

    resolveModule(entryPath)
    loaded.toMap
  }

  /** Helper function to search for a theory declaration with the given name
    * in a module (assumed to be a ModuleImpl).
    */
  def findTheoryDeclInModule(m: ModuleImpl, theoryName: String): Option[TheoryDecl] = {
    m.listprog_.asScala.flatMap {
      case pt: ProgTheoryDecl =>
        pt.theorydecl_ match {
          case bt: BaseTheoryDecl =>
            bt.name_ match {
              case nv: NameVar if nv.ident_ == theoryName => Some(pt.theorydecl_)
              case nw: NameWildcard if "_" == theoryName   => Some(pt.theorydecl_)
              case _ => None
            }
          case _ => None
        }
      case _ => None
    }.headOption
  }

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
  def resolveDottedPath(resolvedModules: Map[String, Module],
                        canonicalPathToCurrentModule: String,
                        dottedPath: DottedPath): Either[String, (String, TheoryDecl)] = {
    // Retrieve the current module.
    val currentModule = resolvedModules.get(canonicalPathToCurrentModule) match {
      case Some(m) => m
      case None    => return Left("Current module not found: " + canonicalPathToCurrentModule)
    }
    currentModule match {
      case m: ModuleImpl =>
        dottedPath match {
          // Single-element dotted path.
          case bp: BaseDottedPath => {
            val theoryName = bp.ident_
            // First try to find the theory in the current module.
            findTheoryDeclInModule(m, theoryName) match {
              case Some(td) => Right((canonicalPathToCurrentModule, td))
              case None =>
                // Not found in the current module; check each ImportFromModule.
                val importOpt = m.listimport_.asScala.collectFirst {
                  case imp: ImportFromModule if imp.ident_ == theoryName => imp
                }
                importOpt match {
                  case Some(imp) =>
                    val currentFile = new File(canonicalPathToCurrentModule)
                    val importedFile = new File(currentFile.getParentFile, imp.string_)
                    val importedCanonicalPath = importedFile.getCanonicalPath
                    resolvedModules.get(importedCanonicalPath) match {
                      case Some(importedModule) =>
                        importedModule match {
                          case im: ModuleImpl =>
                            findTheoryDeclInModule(im, theoryName) match {
                              case Some(td) => Right((importedCanonicalPath, td))
                              case None     => Left(s"Theory '${theoryName}' not found in module ${importedCanonicalPath}\nImported module: ${PrettyPrinter.print(importedModule)}")
                            }
                          case _ =>
                            Left("Imported module is not a ModuleImpl: " + importedCanonicalPath)
                        }
                      case None => Left("Imported module not found: " + importedCanonicalPath)
                    }
                  case None =>
                    Left("Theory '" + theoryName + "' not found in current module or via any ImportFromModule")
                }
            }
          }
          // Two-element dotted path.
          case qp: QualifiedDottedPath =>
            qp.dottedpath_ match {
              case inner: BaseDottedPath =>
                val moduleAlias = qp.ident_
                val theoryName  = inner.ident_
                // Find the matching ImportModuleAs in the current module.
                val importOpt = m.listimport_.asScala.collectFirst {
                  case imp: ImportModuleAs if imp.ident_ == moduleAlias => imp
                }
                importOpt match {
                  case Some(imp) =>
                    val currentFile = new File(canonicalPathToCurrentModule)
                    val importedFile = new File(currentFile.getParentFile, imp.string_)
                    val importedCanonicalPath = importedFile.getCanonicalPath
                    resolvedModules.get(importedCanonicalPath) match {
                      case Some(importedModule) =>
                        importedModule match {
                          case im: ModuleImpl =>
                            findTheoryDeclInModule(im, theoryName) match {
                              case Some(td) => Right((importedCanonicalPath, td))
                              case None     => Left("Theory '" + theoryName + "' not found in module " + importedCanonicalPath)
                            }
                          case _ =>
                            Left("Imported module is not a ModuleImpl: " + importedCanonicalPath)
                        }
                      case None => Left("Imported module not found: " + importedCanonicalPath)
                    }
                  case None =>
                    Left("Module alias '" + moduleAlias + "' not found in ImportModuleAs statements")
                }
              case _ =>
                Left("Invalid dotted path: expected a base dotted path for theory name")
            }
        }
      case _ =>
        Left("Current module is not a ModuleImpl: " + canonicalPathToCurrentModule)
    }
  }
}
