package io.f1r3fly.mettail

import java.io.File
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import metta_venus.Absyn._
import metta_venus.PrettyPrinter
import scala.jdk.CollectionConverters._

class InstInterpreterSpec extends AnyFlatSpec with Matchers {
  "InstInterpreter" should "interpret the Rholang module correctly" in {
    // Setup omitted for brevity...
    
    // After interpreting:
    val actual = PrettyPrinter.print(basePres)

    val expected =
      s"""
      Equations
      {
        Proc;
        Name;
      }
      Terms
      {
        PZero . Proc ::= "0";
        PPar . Proc ::= "(" Proc "|" Proc ")";
        PRepl . Proc ::= "!" Proc;
        PNew . Proc ::= "new" (Bind x Name) "in" (x) Proc;
        PDrop . Proc ::= "*" Name;
        NQuote . Name ::= "@" Proc;
        PSend . Proc ::= Name "!" (Proc);
        PRecv . Proc ::= "for" (Bind x Name "<-" Name) "{" x Proc "}";
      }
      Equations
      {
        (Mult (Mult x y) z) == (Mult x (Mult y z));
        (Mult x (One)) == x;
        (Mult (One) x) == x;
        (Plus x y) == (Plus y x);
        if x # Q then (PPar (PNew x P) Q) == (PNew x (PPar P Q));
        (PNew x (PNew x P)) == (PNew x P);
        (PNew x (PNew y P)) == (PNew y (PNew x P));
        (PRepl P) == (PPar P (PRepl P));
        (NQuote (PDrop N)) == N;
        (PDrop (NQuote P)) == P;
      }
      Rewrites
      {
        RPar1 : let Src ~> Tgt in (PPar Src Q) ~> (PPar Tgt Q);
        RPar2 : let Src1 ~> Tgt1 in let Src2 ~> Tgt2 in (PPar Src1 Src2) ~> (PPar Tgt1 Tgt2);
        RNew : let Src ~> Tgt in (PNew x Src) ~> (PNew x Tgt);
        RComm : (PPar (PRecv y x P) (PSend x Q)) ~> (Subst P (NQuote Q) y);
      }
      """.stripMargin

    actual.trim shouldEqual expected.trim
  }
}