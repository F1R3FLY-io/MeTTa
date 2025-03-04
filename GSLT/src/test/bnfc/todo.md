- scoping of facts (e.g. rho vs pi)
- desugar syntax defined in theory to lispy ast in rewrites, eqns, and facts
- possible reduce/reduce conflict with comma delimiter for facts.  Escaping?
- need explicit conversion

Foo.

    Theory MinPi() = {
      Exports {
        Proc ;
        Name ;
      };
      Terms {
        PZero . Proc ::= "0" ;
        PPar  . Proc ::= Proc "|" Proc ;
        PSend . Proc ::= Name "!" "(" Name ")" ;
        PRecv . Proc ::= "for" "(" (Bind Name [2]) "<-" Name ")" "{" Proc "}" ;
      };
      Equations {
        ( PPar.Proc P Q ) == ( PPar.Proc Q P ) ;
        ( PPar.Proc ( PPar.Proc P Q ) R ) == ( PPar.Proc P ( PPar.Proc Q R ) ) ;
        ( PPar.Proc P ( PZero.Proc ) ) == P ;
      };
      Rewrites {
        RComm : ( PPar.Proc ( PRecv.Proc y x P) ( PSend.Proc x z ) ) ~> ( Subst P z y ) ;
        RPar1 : let Src ~> Tgt in 
                ( PPar.Proc Src Q ) ~> ( PPar.Proc Tgt Q ) ;
        RPar2 : let Src1 ~> Tgt1 in 
                let Src2 ~> Tgt2 in 
                ( PPar.Proc Src1 Src2 ) ~> ( PPar.Proc Tgt1 Tgt2 ) ;
      }
    }

    Theory PiCalc(m: MinPi) = {
      Exports {
        Proc extends m.Proc ; // So Proc rewrites extend m.Proc rewrites
        Name extends m.Name ;
      };
      Terms {
        PRepl . Proc ::= "!" Proc ;
        PNew  . Proc ::= "new" (Bind Name [1]) "in" Proc ;
      };
      Equations {
        if x # Q then
          ( PPar.Proc ( PNew.Proc x P ) Q ) == ( PNew.Proc x ( PPar.Proc P Q ) ) ;
        ( PNew.Proc x ( PNew.Proc x P ) ) == ( PNew.Proc x P ) ;
        ( PNew.Proc x ( PNew.Proc y P ) ) == ( PNew.Proc y ( PNew.Proc x P ) ) ;
      };
      Rewrites {
        RNew  : let Src ~> Tgt in
                (PNew.Proc x Src) ~> (PNew.Proc x Tgt) ;
      }
    }

    Theory RhoCalc(m: MinPi) = {
      Exports {
        Proc extends m.Proc ;
        Name extends m.Name ;
      };
      Terms {
        PDrop . Proc ::= "*" Name ;
        NQuote . Name ::= "@" Proc ;
      };
      Equations {
        ( PDrop.Proc ( NQuote.Name P ) ) == P ;
        ( NQuote.Name ( PDrop.Proc N ) ) == N ;
      };
      Rewrites {}
    }

    Theory Rholang(p: PiCalc, r: RhoCalc, std: Std) = {
      Exports {
        Proc extends p.Proc union r.Proc;
        Name extends p.Name union r.Name;
      };
      Terms {
        IntProc . Proc ::= std.IntExpr ;
      };
      Equations {};
      Rewrites {}
    }



    Theory Monoid() = {
      Exports {
        Proc ;
      };
      Terms {
        One . Proc = "1" ;
        Mult . Proc = "(" Proc "*" Proc ")" ;
      };
      Equations {
        (Mult.Proc (Mult.Proc x y) z) == (Mult.Proc x (Mult.Proc y z));
        (Mult.Proc x (Id.Proc)) == x;
        (Mult.Proc (Id.Proc) x) == x;
      };
      Rewrites {};
    }

    Theory CommutativeMonoid(m: Monoid) = {
      Exports {
        Proc extends m.Proc ;
      };
      Terms {};
      Equations {
        (Mult.Proc x y) == (Mult.Proc y x);
      };
      Rewrites {};
    }

    Theory Ring(add: CommutativeMonoid, mult: Monoid) = {
      Exports {
        Proc 
          extends add.Proc where {
            One . Proc => Zero . Proc ::= "0" ;
            Mult . Proc => Plus . Proc ::= "(" Proc "+" Proc ")" ;
          }
          and mult.Proc;
      }
      Terms {};
      Equations {
        (Mult.Proc x (Plus.Proc y z)) == (Plus.Proc (Mult.Proc x y) (Mult.Proc x z));
        (Mult.Proc (Plus.Proc x y) z) == (Plus.Proc (Mult.Proc x z) (Mult.Proc y z));
        (Mult.Proc x (Zero.Proc)) == (Zero.Proc);
        (Mult.Proc (Zero.Proc) x) == (Zero.Proc);
      }
      Rewrites {};
    }



    Theory F(g : G) = {
      Exports { S ; };
      Terms {
        Const . S ::= "f";
        AsF . S ::= "F" "[" g.S "]";
        Mult . S ::= S S;
      };
      Equations {};
      Rewrites {};
    }

    Theory G(f : F) = {
      Exports { S ; };
      Terms {
        Const . S ::= "g";
        AsG . S ::= "G" "[" f.S "]";
        Mult . S ::= S S;
      };
      Equations {};
      Rewrites {};
    }

    Mutually recursive with no way to construct an instance.
    Some theory instance ffix = µx. F(G(x)), gfix = G(ffix)?  Or ffix = µx.F(G(x)), gfix = G(ffix)?  Or ffix = F(gfix), gfix = G(ffix)?

TODO:
mutual recursion
tree calc sugar examples
package management
