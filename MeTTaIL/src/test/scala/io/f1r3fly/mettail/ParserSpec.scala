package io.f1r3fly.mettail

import java.io.File
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._

class ParserSpec extends AnyFlatSpec with Matchers {
  val moduleFile  = new File("../GSLT/src/test/module/ArithmeticOperations.module")
  val entryPath   = moduleFile.getCanonicalPath
  val processor   = ModuleProcessor.default
  var test_passed = true
  try {
    processor.resolveModules(entryPath)
  } catch {
    case e: Exception => {
      test_passed = false
      println("--------- Parsing error ---------")
      println(e.getMessage)
      println(e.printStackTrace())
      println("----- End of parsing error ------")
    }
  }
  assert(test_passed)
}
