package io.f1r3fly.mettail

import java.io.Reader

/** A small interface over a backing store.
  * In prod use RealFileSystem; in tests swap in a FakeFileSystem.
  */
trait FileSystem {
  /** Normalize and dedupe a path (e.g. remove “../” and symlinks). */
  def canonical(path: String): String

  /** Open a reader on the given path. */
  def reader(path: String): Reader

  /** Given a parent directory and a child filename, produce a new path. */
  def join(parentPath: String, child: String): String

  /** Given a path, return its parent directory path. */
  def parent(path: String): String
}

/** Implementation using java.io.File/FileReader. */
class RealFileSystem extends FileSystem {
  import java.io.{File, FileReader}
  override def canonical(path: String): String =
    new File(path).getCanonicalPath

  override def reader(path: String): Reader =
    new FileReader(path)

  override def join(parentPath: String, child: String): String = {
    new File(parentPath, child).getCanonicalPath
  }
    
  override def parent(path: String): String =
    new File(path).getParentFile.getPath
}

