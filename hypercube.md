Given an interactive finitely-presented GSLT T, produce new typed GSLT.

Fn sym arrows o: X1 x ... x Xn -> Y are sugar for Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ o(t1, ..., tn): Y.
Rewrite squiggly arrows ρ: os(t1, ..., tn) ~> ot(t1, ..., tn) are sugar for 
    Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ s(ρ(t1, ..., tn)) = os(t1, ..., tn)
    Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ t(ρ(t1, ..., tn)) = ot(t1, ..., tn)
Equations os(t1, ..., tn) = ot(t1, ..., tn) are sugar for 
    Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ os(t1, ..., tn) = ot(t1, ..., tn)

- E.g. RHO calculus

    shapes
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.
      N

    fn syms
      0: 1 -> P
      |: P x P -> P
      !: N x P -> P
      ?: N x (N -> P) -> P
      *: N -> P
      @: P -> N

    eqns
      // V = P from above
      comm. mon. eqns
      @*n = n

    rewrites
      comm: N x (N -> P) x P -> R
      comm: x?Q | x!R ~> ev(Q, @R)

      par1: R x P -> R
      par1: s(r) | p ~> t(r) | p

      par2: R x R -> R
      par2: s(r1) | s(r2) ~> t(r1) | t(r2)

      run: P -> P
      run: *@P ~> P

- E.g. λ-calculus

    shapes
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.

    fn syms
      App: P x P -> P
      Lam: (P -> P) -> P

    eqns
      // V = P from above

    rewrites
      beta: (P -> P) x P -> R
      beta: App(Lam(K), Q) ~> ev(K, Q)

      head: R x P -> R
      head: App(s(E), Q) ~> App(t(E), Q)

- E.g. SKI

    shapes
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.

    fn syms
      App: P x P -> P
      S, K, I: 1 -> P
      S1: P -> P
      S2: P x P -> P
      K1: P -> P

    eqns
      // V = P from above

    rewrites
      σ1: P -> R
      σ1: App(S, x) ~> S1(x)

      σ2: P x P -> R
      σ2: App(S1(x) y) ~> S2(x, y)

      σ3: P x P x P -> R
      σ3: App(S2(x, y) z) ~> ((x z) (y z))

      κ1: P -> R
      κ1: App(K, x) ~> K1(x)

      κ2: P x P -> R
      κ2: App(K1(x), y) ~> x

      ι1: P -> R
      ι1: App(I, x) ~> x

      head: R x P -> R
      head: App(s(E), Q) ~> App(t(E), Q)

- E.g. Ambient

    shapes
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.
      N
      M

    fn syms
      ν: (N -> P) -> P
      0: 1 -> P
      |: P x P -> P
      !: P -> P
      []: N x P -> P
      .: M x P -> P
      in, out, open: N -> M

    eqns
      comm. mon.
      νx.νy.P = νy.νx.P
      νx.νx.P = νx.P

      Γ, x: N ⊢ Q1: P    Γ ⊢ Q2: P    ⊨    Γ ⊢ (νx.Q1) | Q2 = νx.(Q1 | Q2)

    rewrites
      expand: P -> R
      expand: !Q ~> Q | !Q

      ambient: N x R -> R
      ambient: n[s(E)] ~> n[t(E)]

      in: N x N x P x P x P -> R
      in: n[in m.Q | R] | m[S] ~> m[n[Q | R] | S]

      out: N x N x P x P x P -> R
      out: m[n[out m:Q | R] | S] ~> n[Q | R] | m[S]

      open: N x P x P -> R
      open: open m.P | m[Q] ~> P | Q

  - E.g. Rule 110?

We'll consider the free theory on empty sets.  Since it's free, we get an algebra for building up terms and a coalgebra for taking them apart.  That lets us do destructuring assignment in the premises of an inference rule.

We'll add term constructors and a typing endospan : on terms in a typing context.

Judgments are of the form A: B where A and B are both terms (which may include free variables) of the same shape.  We write s^T to indicate that there are up to two rules, depending on where you are in the hypercube: one for type^T, one for kind^T (see Axiom below for those terms).  We can read "A: B" as "a way that A relates to B", since a span allows A to be related to B in multiple ways.

Entailments involve a typing context (a list of variable typing judgments) on the left of a turnstile and a single term judgment on the right.  All the free variables on the right must appear on the left.  We read `Γ ⊢ A: B` as "a way that A relates to B in the context Γ".  More specifically, we read `x₁: X₁, ..., xₙ: Xₙ ⊢ A: B` as "for each way that x₁ relates to X₁, ..., and xₙ relates to Xₙ, a way that A relates to B".

Inference rules have a list of entailments on top and an entailment on the bottom.  All the free metavariables on the bottom must appear on the top with the same variance.  We read

  Γ ⊢ A₁: B₁    ⋯    Γ ⊢ Aₙ: Bₙ
  —————————————————————————————
  Γ ⊢ A: B

as "for each way that A₁ relates to B₁ in the context Γ, ..., and Aₙ relates to Bₙ in the context Γ, a way that A relates to B in the context Γ".

- Axiom

    Add term constructors `*^T, □^T: 1 -> T` for each generating shape T in the theory.

      Type . T ::= "type" "T" ;
      Kind . T ::= "kind" "T" ;

    In all cases, the output category must be a generating category.  We'll add ArrowCat as an Item.

      ArrowCat . Item ::= "(" Cat "->" Cat ")" ;

    Qux  . T1 ::= "qux" ;

    Quux . T2 ::= "quux" ;

    // Bar: (T1 -> T2) -> T3
    // TODO: Rewrite all Bind forms to Arrow forms with a compiler pass
    Bar  . T3 ::= "bar" (Bind t1 T1) "." (t1)T2 ;

    Baz  . T3 ::= "baz" T2 ;
    
    // Bee: (T1 -> T2) -> T3
    Bee  . T3 ::= "bee" (T1 -> T2) ;

    // Foo: ((T1 -> T2) -> T3) -> T4
    Foo  . T4 ::= "foo" (Bind t1t2 (T1 -> T2)) "." (t1t2)T3 ;


    // In Foo and Bee,
    //   (T1 -> T2)
    // is used as a category, so we generate
    //   AppT1T2 . T2 ::= "α" "{" (T1 -> T2) "," T1 "}" ;
    //   IdentT1T2 . (T1 -> T2) ::= Ident ; 
    //   LamT1T2 . (T1 -> T2) ::= "λ" "{" Ident "," T2 "}" ;
    //   IdentT1 . T1 ::= Ident ;
    // The IdentTX productions are the same as the one for Bind.

    // foo(bar)
    // ⇓ η
    // foo(λf.bar(f))
    // ⇓ η
    // foo(λf.bar(λx.f(x)))
    foo f . bar x . α{f, x}

    // foo(λf.baz(f(qux)))
    foo f . baz α{f, qux}

    // bar(λx.quux)
    bar x quux
    
    // bee(λx.quux)
    bee λ{x, quux}
    
    // bee(λx.bar(λy.quux))
    bee λ{x, bar y quux}

- Start

    Γ ⊢ A: s
    ——————————————
    Γ, x: A ⊢ x: A

- Weakening

    Γ ⊢ A: B    Γ ⊢ C: s
    ————————————————————
    Γ, x: C ⊢ A: B

- Arrow type (Not dependent product!  This is just a lambda theory), abstraction, application, beta equivalence as part of lambda theory

- For each term constructor, a pair of functions (one for structural type, one for term) and inference rules for principal structural types.

  - E.g. RHO calc

      00^s: 1 -> P

      ———————————
      ⊢ 00^s: s^P

      0^s: 1 -> P

      ———————————
      ⊢ 0^s: 00^s


      ||^s: P x P -> P

      Γ ⊢ A: s^P  Γ ⊢ B: s^P
      ——————————————————————
      Γ ⊢ ||^s(A, B): s^P

      Γ ⊢ A: s^P
      —————————————————————
      Γ ⊢ ||^s(A, 00^s) = A

      Γ ⊢ A: s^P  Γ ⊢ B: s^P
      ———————————————————————————
      Γ ⊢ ||^s(A, B) = ||^s(B, A)

      Γ ⊢ A: s^P  Γ ⊢ B: s^P  Γ ⊢ C: s^P
      —————————————————————————————————————————————
      Γ ⊢ ||^s(||^s(A, B), C) = ||^s(A, ||^s(B, C))


      |^s: P x P -> P

      Γ ⊢ A: s^P  Γ ⊢ B: s^P  Γ ⊢ C: A  Γ ⊢ D: B
      ——————————————————————————————————————————
      ⊢ |^s(C, D): ||^s(A, B)

      Γ ⊢ A: s^P  Γ ⊢ C: A
      ————————————————————————————
      Γ ⊢ |^s(C, 0^s) = C

      Γ ⊢ A: s^P  Γ ⊢ B: s^P  Γ ⊢ C: A  Γ ⊢ D: B
      ——————————————————————————————————————————
      Γ ⊢ |^s(C, D) = |^s(D, C)

      Γ ⊢ A: s^P  Γ ⊢ B: s^P  Γ ⊢ C: s^P  Γ ⊢ D: A  Γ ⊢ E: B  Γ ⊢ F: C
      ———————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ |^s(|^s(D, E), F) = |^s(D, |^s(E, F))


      !!^{s₁, s₂}: N x P x N -> P

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P
      ———————————————————————————
      Γ ⊢ !!^{s₁, s₂}(A, B): s₁^P

      !^{s₁, s₂}: N x P -> P

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ ⊢ x: A  Γ ⊢ Q: B
      ——————————————————————————————————————————————
      ⊢ !^{s₁, s₂}(x, Q): !!^{s₁, s₂}(A, B, x)

      
      forfor^{s₁, s₂, s₃}: N x N x (N -> P) x N -> P

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^N  Γ, y: B ⊢ C: s₃^P  Γ ⊢ x: A
      —————————————————————————————————————————————————————
      Γ ⊢ forfor^{s₁, s₂, s₃}(A, B, λy.C, x): s₃^P

      for^{s₁, s₂, s₃}: N x (N -> P) -> P

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^N  Γ, y: B ⊢ C: s₃^P  Γ ⊢ x: A  Γ, y: B ⊢ D: C
      ——————————————————————————————————————————————————————————————————————————————
      Γ ⊢ for^{s₁, s₂, s₃}(x, λy. D): forfor^{s₁, s₂, s₃}(A, B, λy.C, x)


      @@^s: P -> N

      Γ ⊢ A: s^P
      ————————————————
      Γ ⊢ @@^s(A): s^N

      @^s: P -> N

      Γ ⊢ A: s^P  Γ ⊢ B: A
      ——————————————————————
      Γ ⊢ @^s(B): @@^s(A)

      **^s: N -> P

      Γ ⊢ A: s^N
      ————————————————
      Γ ⊢ **^s(A): s^P

      *^s: N -> P

      Γ ⊢ A: s^N  Γ ⊢ x: A
      ————————————————————
      ⊢ *^s(x): **^s(A)

      Γ ⊢ A: s^P
      —————————————————————
      Γ ⊢ **^s(@@^s(A)) = A

      Γ ⊢ A: s^N
      —————————————————————
      Γ ⊢ @@^s(**^s(N)) = N

      Γ ⊢ A: s^P  Γ ⊢ B: A
      ———————————————————————————————
      Γ ⊢ *^s(@^s(B)) = B

      Γ ⊢ A: s^N  Γ ⊢ B: A
      ———————————————————————————————
      Γ ⊢ @^s(*^s(B)) = B


      // Rewrites
      
      srcsrc^s, tgttgt^s: R -> P

      Γ ⊢ A: s^R
      —————————————————————————————————
      Γ ⊢ srcsrc^s(A), tgttgt^s(A): s^P

      src, tgt: R -> P

      Γ ⊢ A: s^R  Γ ⊢ r: A
      ————————————————————————————————————————————————————
      ⊢ src^s(r), tgt^s(r): srcsrc^s(A), tgttgt^s(A)

      // Non-dependent

      commcomm^{s₁, s₂}: N x N x (N -> P) x N -> R

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ ⊢ C: s₁^P  Γ ⊢ x: A
      ——————————————————————————————————————————————— y # C
      Γ ⊢ commcomm^{s₁, s₂}(A, @@B, λy.C, x): s₁^R

      comm: N x (N -> P) x P -> R

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ ⊢ C: s₁^P  Γ ⊢ x: A  Γ, y: @@(B) ⊢ L: C  Γ ⊢ Q: B
      ——————————————————————————————————————————————————————————————————————————————— y # C
      Γ ⊢ comm^{s₁, s₂}(x, λy.L, Q): commcomm^{s₁, s₂}(A, @@B, λy.C, x)

      // Dependent

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ, y: @@(B) ⊢ C: s₁^P  Γ ⊢ x: A
      —————————————————————————————————————————————————————————
      Γ ⊢ commcomm^{s₁, s₂}(A, @@B, λy.C, x): s₁^R

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ, y: @@(B)⊢ C: s₁^P  Γ ⊢ x: A  Γ, y: @@(B) ⊢ L: C  Γ ⊢ Q: B
      ——————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ comm^{s₁, s₂}(x, λy.L, Q): commcomm^{s₁, s₂}(A, @@B, λy.C, x)


      par1par1^s: R x P -> R

      Γ ⊢ A: s^R  Γ ⊢ B: s^P
      —————————————————————————
      Γ ⊢ par1par1^s(A, B): s^R

      par1^s: R x P x R x P -> R

      Γ ⊢ A: s^R  Γ ⊢ B: s^P  Γ ⊢ r: A  Γ ⊢ Q: B
      ——————————————————————————————————————————
      Γ ⊢ par1^s(r, Q): par1par1^s(A, B)

      par2par2^s: R x R -> R

      Γ ⊢ A: s^R  Γ ⊢ B: s^R
      —————————————————————————
      Γ ⊢ par2par2^s(A, B): s^R

      Γ ⊢ A: s^R  Γ ⊢ B: s^R  Γ ⊢ r1: A  Γ ⊢ r2: B
      ————————————————————————————————————————————
      Γ ⊢ par2^s(r1, r2): par2par2^s(A, B)



      ////////////// Non-dependent continuation type //////////

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ ⊢ C: s₁^P  Γ ⊢ x: A
      ————————————————————————————————————————————————— y # C
      Γ ⊢ srcsrc^s₁(commcomm^{s₁, s₂}(A, @@B, λy.C, x))
      .   ==
      .   ||^s₁(!!^s₁(A, B, x), forfor^{s₁, s₂, s₁}(A, @@B, λy.C, x))  // Is s₁ s₂ s₁ correct?

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ ⊢ C: s₁^P  Γ ⊢ x: A  Γ, y:@@(B) ⊢ L: C  Γ ⊢ Q: B
      ————————————————————————————————————————————————————————————————————————————— y # C
      Γ ⊢ src(comm(x, λy.L, Q)): srcsrc(commcomm(A, @@B, λy.C, x))
      .   ==
      .   |(!(x, Q), for(x, λy.L)): ||(!!(A, B, x), forfor(A, @@B, λy.C, x))

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ ⊢ C: s₁^P  Γ ⊢ x: A
      ———————————————————————————————————————————————— y # C
      Γ ⊢ tgttgt(commcomm(A, @@B, λy.C, x))
      .   ==
      .   ((λy.C) @(Q))
      .   ==
      .   C

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ ⊢ C: s₁^P  Γ ⊢ x: A  Γ, y:@@(B) ⊢ L: C  Γ ⊢ Q: B
      ———————————————————————————————————————————————————————————————————————————— y # C
      Γ ⊢ tgt(comm(x, λy.L, Q)): tgttgt(commcomm(A, @@B, λy.C, x))
      .   ==
      .   ((λy.L) @(Q)): ((λy.C) @(Q)) 
      .   ==
      .   ((λy.L) @(Q)): C


      ////////////// Dependent continuation type: no type equations //////////

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ, y: @@(B) ⊢ C: s₁^P  Γ ⊢ x: A  Γ, y: @@(B) ⊢ L: C  Γ ⊢ Q: B
      ———————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ src(comm(x, λy.L, Q)): srcsrc(commcomm(A, @@B, λy.C, x))
      .   ==
      .   |(!(x, Q), for(x, λy.L)): ||(!!(A, B, x), forfor(A, @@B, λy.C, x))

      Γ ⊢ A: s₁^N  Γ ⊢ B: s₂^P  Γ, y: @@(B) ⊢ C: s₁^P  Γ ⊢ x: A  Γ, y: @@(B) ⊢ L: C  Γ ⊢ Q: B
      ————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ tgt(comm(x, λy.L, Q)): tgttgt(commcomm(A, @@B, λy.C, x))
      .   ==
      .   ((λy.L) @(Q)): ((λy.C) @(Q))


      ////////////// Context rules //////////

      Γ ⊢ A: s^R  Γ ⊢ B: s^P
      ——————————————————————————
      Γ ⊢ srcsrc(par1par1(A, B))
      .   ==
      .   ||(srcsrc(A), B)

      Γ ⊢ A: s^R  Γ ⊢ B: s^P  Γ ⊢ C: A  Γ ⊢ D: B
      —————————————————————————————————————————————————————————————————
      Γ ⊢ src(par1(C, D)): srcsrc(par1par1(A, B))
      .   ==
      .   |(src(C), D): ||(srcsrc(A), B)

      Γ ⊢ A: s^R  Γ ⊢ B: s^P
      ——————————————————————————
      Γ ⊢ tgttgt(par1par1(A, B))
      .   ==
      .   ||(tgttgt(A), B)

      Γ ⊢ A: s^R  Γ ⊢ B: s^P  Γ ⊢ C: A  Γ ⊢ D: B
      —————————————————————————————————————————————————————————————————
      Γ ⊢ tgt(par1(C, D)): tgttgt(par1par1(A, B))
      .   ==
      .   |(tgt(C), D): ||(tgttgt(A), B)

      // Reduction context distributes over modality

      Q:A ~> Q':A'

      Γ ⊢ A': s^P  Γ ⊢ Q: ◊A'  Γ, Y: s^P, y: Y ⊢ B: s^P     // A' and Y are the same sort because Q:◊A' replaces y:Y
      ————————————————————————————————————————————————— K[Y, y]: B
      Γ ⊢ K[◊A'/Y][Q/y]: B[◊A' / Y][Q / y]  // have
      Γ ⊢ K[◊A'/Y][Q/y]: ◊B[A' / Y][Q' / y] // want


      // Non-dependent B
      Γ ⊢ A': s^P  Γ ⊢ Q: ◊A'  Γ, Y: s^P ⊢ B: s^P
      ——————————————————————————————————————————— K[Y]: B, y # B  Can do polymorphic, type operator, non-dependent
      Γ ⊢ K[◊A'/Y][Q/y]: B[◊A' / Y]
      Γ ⊢ K[◊A'/Y][Q/y]: ◊B[A' / Y]

      // Dependent B requires witness, so ◊ has to track the witness
      Γ ⊢ A': s^P  Γ ⊢ Q: ◊(Q':A')  Γ, Y: s^P, y: Y ⊢ B: s^P     // A' and Y are the same sort because Q:◊A' replaces y:Y
      —————————————————————————————————————————————————————— K[Y, y]: B
      Γ ⊢ K[◊A'/Y][Q/y]: ◊(K[A'/Y][Q'/y]: B[A' / Y][Q' / y])




- Conv-like rule

    `◊: P -> P`

    Γ ⊢ A: s
    ——————————
    Γ ⊢ ◊A: s

    Γ ⊢ A: s    Γ ⊢ B: A    Γ ⊢ ρ: B ~> B'    Γ ⊢ B': A'
    ————————————————————————————————————————————————————
    Γ ⊢ B: ◊A'

    `◊*: P -> P`

    Γ ⊢ A: B
    ———————————
    Γ ⊢ A: ◊*B

    Γ ⊢ A: ◊◊*B
    —————————————
    Γ ⊢ A: ◊*B

    Γ ⊢ A: ◊*◊*B
    —————————————
    Γ ⊢ A: ◊*B

- Modalities from all process-shaped subterms of LHS of base rewrites.  RHS gets turned into structural type.  Structural type has only type info in a slot when the type is a process; when it's not a process, the value is also part of the type (e.g. names in ambient/pi/RHO).  In this approach, the types aren't dependent.  For example, in the first SKI inference rule below, the term doesn't have access to z, so even though the result type does, the result type isn't actually dependent.  Also, we can't make S, x, or y depend on z because z would be free in the conclusion.

  Also laws based on context rewrites.

  Γ ⊢ <K(-)>B: □
  ————————————————————
  Γ ⊢ K(<K(-)>B) = ◊B

  Γ ⊢ A: B
  ——————————————
  Γ ⊢ K(A): K(B)

  - E.g. SKI `σ: App(App(App(S, x), y), z) ~> App(App(x, z), App(y, z))`
                               `A   B   C`

    Γ ⊢ A: s^P    Γ ⊢ x: A    Γ ⊢ B: s^P    Γ ⊢ y: B    Γ ⊢ C: s^P
    ——————————————————————————————————————————————————————————————
    Γ ⊢ App(App(S, x), y): <App(-, z: C)>App(App(A, C), App(B, C)) // Do we need a freshness assertion for z?

    Γ ⊢ A: s^P    Γ ⊢ x: A    Γ ⊢ B: s^P    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————————
    Γ ⊢ App(S, x): <App(App(-, y: B), z: C)>App(App(A, C), App(B, C))

    Γ ⊢ A: s^P    Γ ⊢ B: s^P    Γ ⊢ C: s^P
    ————————————————————————————————————————————————————————————————————
    Γ ⊢ S: <App(App(App(-, x: A), y: B), z: C)>App(App(A, C), App(B, C))

    Γ ⊢ A: s^P    Γ ⊢ x: A    Γ ⊢ B: s^P    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————————
    Γ ⊢ x: <App(App(App(S, -), y: B), z: C)>App(App(A, C), App(B, C))

    Γ ⊢ A: s^P    Γ ⊢ B: s^P    Γ ⊢ y: B    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————————
    Γ ⊢ y: <App(App(App(S, x: A), -), z: C)>App(App(A, C), App(B, C))

    Γ ⊢ A: s^P    Γ ⊢ B: s^P    Γ ⊢ C: s^P    Γ ⊢ z: C
    —————————————————————————————————————————————————————————————————
    Γ ⊢ z: <App(App(App(S, x: A), y: B), -)>App(App(A, C), App(B, C))

    How do we get something like an arrow type from this?
    S: (C=>B=>A) => (C=>B) => C => A

    We need a context rule like

    Γ, ρ: S ~> T ⊢ χ(ρ): K(S) ~> K'(T)    Γ ⊢ A: s₁    Γ ⊢ T: A
    ———————————————————————————————————————————————————————————
    Γ ⊢ K(S): ◊K'(A)

    That is, because of ρ, S:◊A, so we could already derive K(S): K(◊A).  This is necessary to pull the diamond past the K.

    Γ ⊢ <App(-, C)><App(-, B)>A: *^P    Γ ⊢ x: <App(-, C)><App(-, B)>A    Γ ⊢ <App(-, C)>B: *^P    Γ ⊢ y: <App(-, C)>B    Γ ⊢ C: *^P
    ————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ App(App(S, x), y): <App(-, z: C)>App(App(<App(-, C)><App(-, B)>A, C), App(<App(-, C)>B, C))
    ———————————————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ App(App(S, x), y): <App(-, z: C)>App(◊<App(-, B)>A, ◊B)    Γ, ρ: S ~> T ⊢ head:App(S, Q) ~> App(T, Q)
    ———————————————————————————————————————————————————————————————————————————————————————————————————————————— // what's this rule?  Need conversion rule that uses K.
    Γ ⊢ App(App(S, x), y): <App(-, z: C)>◊◊A

  - E.g. Ambient `in: n[ in m.Q | R ] | m[ S ] ~> m[ n[ Q | R ] | S ]`
                     `A     B C   D     B  E`

    Γ ⊢ A: s^N    Γ ⊢ m: A    Γ ⊢ B: s^N    Γ ⊢ n: B    Γ ⊢ C: s^P    Γ ⊢ Q: C    Γ ⊢ D: s^P    Γ ⊢ R: D    Γ ⊢ E: s^P
    ——————————————————————————————————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ n[ in m.Q | R ]: < - | (m: A)[ S: E ]>(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ m: A    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ D: s^P    Γ ⊢ E: s^P    Γ ⊢ S: E
    ——————————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ m[ S ]: < (n: B)[ in (m: A).(Q: C) | (R: D) ] | ->(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ Q: C    Γ ⊢ D: s^P    Γ ⊢ E: s^P
    ————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ Q: <(n: B)[ in (m: A).- | (R: D) ] | (m: A)[ S: E ]>(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ D: s^P    Γ ⊢ R: D    Γ ⊢ E: s^P
    ————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ R: <(n: B)[ in (m: A).(Q: C) | - ] | (m: A)[ S: E ]>(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ D: s^P    Γ ⊢ E: s^P    Γ ⊢ S: E
    ——————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ S: <(n: B)[ in (m: A).(Q: C) | (R: D) ] | (m: A)[ - ]>(m: A)[(n: B)[ C | D ] | E ]

  - What about ones where there's an exponential in the context?  E.g. Lambda `β: App(Lam(λx.C), D) ~> ev(λx.C, D)`.  Here we can put x into the context for B and C.  For example, suppose that A is bool, B is `[true, int] + [false, string]` (existential type).  Then ev(λx.B, D) will be either int or string.  But bool might be a subset of the values that we could put in the second slot to get one of those results, so the inference rule ends up weakening the type of D.  That seems OK.

    Γ ⊢ A: s^P    Γ, x: A ⊢ B: s^P    Γ, x: A ⊢ C: B    Γ ⊢ D: A
    ————————————————————————————————————————————————————————————
    Γ ⊢ D: <App(Lam(λx.C: ∏x:A.B), -)>ev(λx.B, D)
    Γ ⊢ D: <β>(A, λx.C, λx.B, D)

- Conv can be used in any modality context:

    Γ ⊢ A: ◊B    Γ ⊢ ρ: B ~> B'
    —————————————————————————————
    Γ ⊢ A: ◊◊B'

    Γ ⊢ A: <B>C    Γ ⊢ ρ: C ~> C'
    —————————————————————————————
    Γ ⊢ A: <B>◊C'

  - E.g. SKI

    Γ ⊢ K: s^P    Γ ⊢ K: K    Γ ⊢ K: s^P    Γ ⊢ K: K    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————— modality
    Γ ⊢ App(App(S, K), K): <App(-, z: C)>App(App(K, C), App(K, C))    Γ ⊢ κ(C, App(K, C): App(App(K, C), App(K, C)) ~> C
    ———————————————————————————————————————————————————————————————————————————————————————————————————————————————————— conv
    Γ ⊢ App(App(S, K), K): <App(-, z: C)>◊C

- App-like rules for rewrites using ev

  - E.g. RHO.

      Γ ⊢ A: Pi(x, B, C, λQ.D)          Γ ⊢ x: B    Γ ⊢ S: C    Γ ⊢ λQ.D: ∏(C, λQ.s)
      Γ ⊢ A: < - | x: B ! (Q: C) > D    Γ ⊢ x: B    Γ ⊢ S: C    Γ ⊢ λQ.D: ∏_{Q: C}.s
      ——————————————————————————————————————————————————————————————————————————————
      Γ ⊢ A | x!(S): ◊(D {S / Q})
      Γ ⊢ A | x!(S): ◊ev(λQ.D, S)

- Implicit rewrites due to equations.  If A = A', A' ~> B', B' = B, then A ~> B.

  - E.g. RHO

      par1: R x P ~> R together with commutativity imply par1': P x R ~> R and par1' = par1 o swap.
      This can be turned into equations among terms by s(par1'(p, r)) = s(par1(r, p)) and t(par1'(p, r)) = t(par1(r, p)).

- Later: Cut-like rules for each rewrite target with a use of ev on an exponential object.  TODO: express extraction from wrapper in terms of coalgebraic structure of free GSLT.

    for(chan, cont)
    For(Chan, Pi)  Pi type holds lambda Pi(L) and in the consequent we could write ev(L, @E) instead of using sugar

    Γ ⊢ for(x, K): ⟨|x:B!(Q:C)⟩D    Γ ⊢ E: C
    ———————————————————————————————————————— cut-like = target of trace, compare app
    Γ ⊢ ev(K, @E): ev(\Q.D, E)

    From CILL: "Note that terms generated by cut-free proofs are in normal form; in particular, terms generated by the left rules have variables in the head position, so no redexes are created. Redexes only arise as a result of the substitutions performed by applications of the cut rule. Thus all computation is concentrated into the process of cut elimination."
