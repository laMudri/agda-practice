-- First steps in Agda: more on logic.

module E5 where

  -- This will be a long ramble as I try to firm up some things that have been left rather vague
  -- until now…

  -- Until now, we have been fairly hand-wavy about how we can encode logical connectives
  -- and quantifiers in Agda's type theory, in order to build some intuition without
  -- pushing the theory too hard.  Indeed, you may have noticed that some familiar aspects
  -- of logic have been elided altogether (for instance the existential quantifier).
  --
  -- Further, we've also been hand-wavy about what exactly you are doing when you are proving
  -- some theorem in Agda.  Let's first discuss that.  Agda is at heart, a dependent type
  -- theory.  You may have noticed (or been bludgeoned over the head with the fact) that types
  -- are rather important to Agda --- `everything' has a type, and Agda is only too keen to
  -- declare that some term is ill-typed if you make a mistake.  Simplified, Agda's type-checking
  -- algorithm is based around a typing relation between contexts (lists of variables with an
  -- assigned type), terms (for example, `λx. x', `true', `Set', and so forth) and types (`Set',
  -- `Bool → Bool', `ℕ', and so forth).  You may note with interest that some terms are also
  -- types (for instance, `Set').  We write `Γ ⊢ M : φ' (where Γ is ranging over contexts,
  -- M is ranging over terms, and φ over types) for `Agda's typing relation asserts that term
  -- M has type φ in context Γ'.  The type checking algorithm then merely checks that for some
  -- term M, context Γ, and type φ, that `Γ ⊢ M : φ' holds, raising a type error if it does
  -- not.  I won't go into the details of this typing relation (the rules are not entirely
  -- well-specified by the Agda implementors, for a start), but there's some fairly obvious
  -- rules that Agda implements below, to give you an idea:
  --
  -- How to type a variable:
  --
  --   (lookup x Γ = φ)
  --  ------------------
  --      Γ ⊢ x : φ
  --
  -- How to type Setᵢ:
  --
  --      j = i + 1
  --  ------------------        so that Set₁ : Set₂ : Set₃ : Set₄ : …
  --    Γ ⊢ Setᵢ : Setⱼ
  --
  -- How to type a λ-abstraction:
  --
  --      Γ, x : φ ⊢ M : ψ
  --  -------------------------
  --    Γ ⊢ λx : φ. M : φ → ψ
  --
  -- plus dozens more complex typing rules…
  --
  -- We call a term a type if it appears to the right hand side of the colon in the rules above.  As
  -- mentioned above, Agda makes no clear distinction between terms and types, other than via usage
  -- and the rules of the typing relation, and indeed it's perfectly possible in Agda to construct
  -- functions that take types as arguments (as you have already seen), and also produce types as
  -- results (you haven't already seen this, but soon will).
  --
  -- Anyway, if you aren't familiar with these sorts of rules, then you can read them as stating
  -- `assuming the hypotheses above the line hold, we can obtain the conclusion below by applying the
  -- rule'.  They're basically instructions for creating trees, but if they're confusing to you
  -- don't worry, you'll learn more about them in the Part II course on Types.
  --
  -- So what is it that you are doing when you are filling in holes in Agda?  Well, first
  -- note that every hole has a type and a context in which it lives.  If you cast your mind back to
  -- what an Agda proof state looked like, it was something of the form:
  --
  -- Goal: φ
  -- ---------------------------
  -- x : ψ
  -- y : ξ
  -- ψ : Set
  -- ξ : Set
  --
  -- Here we can now make a connection between a proof state and the typing relation:
  --
  --     ψ : Set, ξ : Set, x : ψ, y : ξ ⊢ <?₁> : φ
  --
  -- Where <?₁> is the hole, appearing in place of a term.  `Filling in a hole' is therefore providing a
  -- term to stand in place of that <?₁> that satisfies Agda's typing relation (i.e. that has type φ in
  -- the context above).  That is, we say we must find some M to `inhabit' the type φ.
  --
  -- But what about `logic'?  I've only been talking about types, not logic!  Well, in Agda and other
  -- similar systems, there is a close connection between the two.  Propositions, for example
  --
  --         ∀x. P x    ∃!x. P x ⇒ Q x     False ∨ (∀x. ∃y. P x y ⇒ False)    …
  --
  -- can be encoded as types.  We have already seen how some of these may be encoded in our informal
  -- introduction to Agda in exercises 1-4, but now we make these connections explicit, as well as what
  -- what constitutes a proof of, say P ∨ Q, in the following table:
  --
  --   |  Proposition  |  Agda type        |  Inhabitant       |  Notes                             |
  --   +---------------+-------------------+-------------------+------------------------------------+
  --   |    True       |  Unit type  (𝟙)   |  Unit value (it)  |                                    |
  --   |    False      |  Empty type (𝟘)   |  N/A              |  No inhabitant!                    |
  --   |    φ ⇒ ψ      |  φ → ψ            |  λ-abstraction    |                                    |
  --   |    ¬ φ        |  φ → 𝟘            |  λ-abstraction    |  Function must return 𝟘            |
  --   |    ∀x. P x    |  (x : Set) → P x  |  λ-abstraction    |  ∀, ⇒ both encoded as function     |
  --   |               |                   |                   |  arrows                            |
  --   |    φ ‌∧ ψ      |  φ × ψ            |  Pair             |                                    |
  --   |    φ ∨ ψ      |  φ ⊎ ψ            |  inj₁ or inj₂     |  Must explicitly show one or the   |
  --   |               |                   |                   |  other holds                       |
  --   |    φ = ψ      |  φ ≡ ψ            |  _≡_, Identity    |  e.g. refl                         |
  --   |    ∃x. P x    |  Σ Set (λx → P x) |  Dependent-pair   |  See below                         |
  --   +---------------+-------------------+-------------------+------------------------------------+
  --
  -- The last line you have not encountered (yet), but will below.
  --
  -- Some observations about the table above now follow.  You'll note that 𝟘 is marked as having no
  -- inhabitant.  This is very important.  𝟘 is the encoding of False, and finding an inhabitant of 𝟘 is
  -- akin to finding a proof of False, which we surely do not want.  You'll also note, however, that
  -- ¬ φ is captured by the type φ → 𝟘, which is inhabited by λ(x : φ). M, where M is a term of type 𝟘,
  -- i.e. a proof of False.  But if we cannot inhabit 𝟘, how can we construct such an M?  Well, we have to
  -- make use of x : φ somehow in order to do it.  The restriction against finding a proof of False is
  -- only valid in the empty context.  If we are given some inconsistent assumptions, we can of course
  -- find such a proof.
  --
  -- You'll also note that φ ⇒ ψ and ∀x. P x are both encoded as forms of function space, and both inhabited
  -- by λ-abstractions, albeit the latter is encoded as the more general Π-type (dependent function space,
  -- (x : Set) → …).  As mentioned earlier, in Agda the types φ → ψ and (x : φ) → ψ are equivalent, with
  -- φ → ψ being merely a special case of the latter when x doesn't appear in ψ.
  --
  -- Further, note that disjunction in Agda is something slightly different to what you are used to from
  -- classical mathematics.  In Agda, to prove a disjunction, φ ⊎ ψ, you must show that φ or ψ holds
  -- explicitly, i.e. you must explcitly `construct' an inhabitant of φ or ψ.  In classical mathematics,
  -- one may show that φ ∨ ψ holds by demonstrating that it is impossible for either not to hold.  Not so
  -- in Agda!
  --
  -- You'll note from the table above that proving anything in Agda requires one to explicitly construct
  -- something, whether it be an inhabitant of 𝟙 to prove True, or a function that accepts a proof of φ
  -- and constructs a proof of 𝟘 to prove ¬ φ.  In short, Agda's internal logic is constructive, and
  -- differs from classical mathematics.  An immediate consequence of working with constructive logic is
  -- that some familiar reasoning principles are no longer valid.  Try to prove the following, for
  -- example:

  -- Some familiar infrastructure without importing Exercise 1-4:

  data 𝟘 : Set where

  data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

  ¬_ : Set → Set
  ¬ φ = φ → 𝟘

  double-negation-elimination : (φ : Set) → ¬ (¬ φ) → φ
  double-negation-elimination φ = {!!} -- may take a while to close!

  -- This is valid classically (it's equivalent to the law of excluded middle), but cannot be proved in
  -- Agda's intuitionistic logic.  You can, however, prove the weaker

  triple-negation-to-single-negation : (φ : Set) → ¬ (¬ (¬ φ)) → ¬ φ
  triple-negation-to-single-negation φ prf = λ x → prf (λ y → y x)

  -- Ho hum, some things we normally take for granted we no longer can.  But in exchange for that, Agda's
  -- proofs are much more informative.  Merely by virtue of constructivity, if we manage to prove φ, we
  -- automatically get a program that inhabits φ for free.  That is, Agda's proofs, unlike proofs in
  -- general in classical mathematics, have some computational content.  This becomes especially interesting
  -- where φ is some complex specification of say, a C compiler.  Then proving φ in Agda is akin to
  -- explicitly constructing a C compiler that matches its specification φ.  Very nice (but quite a lot of
  -- work)!

  -- Now, back to existential quantification.  We previously noted that proving φ ∨ ψ in Agda requires an
  -- explicit construction of either φ or ψ.  What about existential quantification?  In classical
  -- mathematics we can prove `∃x. P x' by instead proving that, for every x, it is instead impossible for
  -- `P x' not to hold.  That is, we can prove `∃x. P x' by instead proving `¬ ∀x. ¬(P x)', its
  -- De Morgan dual.  But, if we are trying to explicitly build terms that inhabit types, this
  -- indirect form of proof is horrible!  We've established `∃x. P x' but we cannot get our hands on any
  -- construction of `x' that satisfies `P'.
  --
  -- Constructive mathematics therefore interprets existential quantification differently from classical
  -- mathematics, to show `∃x. P x' constructively we must explicitly construct an `x' that satisfies `P'.
  -- Proofs of `∃x. P x' are therefore pairs consisting of an x and a proof.  In Agda, this notion is
  -- captured as a dependent pair, or Σ-type, where the second element of the pair `depends' on the first
  -- element.  The definition is below:

  data Σ (A : Set) (P : A → Set) : Set where
    _,_ : (x : A) → P x → Σ A P

  -- Of course, like Π-types and the function space arrow →, our existing notion of Cartesian product type,
  -- _×_ is really just a special case of Σ:

  _×_ : Set → Set → Set
  A × B = Σ A (λ x → B)

  -- We can recover our previous definitions on _×_ easily:

  fst : (A B : Set) → A × B → A
  fst A B (x , y) = x

  snd : (A B : Set) → A × B → B
  snd A B (x , y) = y

  -- And we therefore no longer need our old definition of _×_ any more.
  --
  -- Let us see how to use Σ.  First, we'll make use of Agda's ability to infer types to make using Σ a little
  -- bit nicer, so we don't have to clutter up our types any more than we strictly have to:

  ∃ : {A : Set} → (A → Set) → Set
  ∃ {A} P = Σ A P

  -- Now, let's again define the Booleans and some operations over them, as well as propositional equality:

  data Bool : Set where
    true false : Bool -- can put multiple constructors on the same line if they have the same type

  _∧_ : Bool → Bool → Bool
  true  ∧ x = x
  false ∧ x = false

  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  -- Let's use ∃ to prove something very trivial:

  silly-example₁ : (b : Bool) → ∃ λ b′ → (b ∧ b′) ≡ b′
  silly-example₁ true = {!!}
  silly-example₁ false = {!!}

  -- Take a look at the goal state above.  We must inhabit `∃ λ b′ → (b ∧ b′) ≡ b′' given `b : Bool'.
  -- We proceed by case analysis on b:

  silly-example₂ : (b : Bool) → ∃ λ b′ → (b ∧ b′) ≡ b′
  silly-example₂ true  = {!!}
  silly-example₂ false = {!!}

  -- The first hole requires us to construct some b′ such that b′ ≡ b′.  But any b′ will do here, as
  -- everything is equal to itself via `refl'.  The second hole requires us to exhibit some b′ such
  -- that false ≡ b′.  It does not take a genius to conclude that b′ must therefore be false.  We
  -- can refine our two holes further, using <Ctrl> + <c> + <r> to obtain:

  silly-example₃ : (b : Bool) → ∃ λ b′ → (b ∧ b′) ≡ b′
  silly-example₃ true  = {!!} , {!!}
  silly-example₃ false = {!!} , {!!}

  -- As an inhabitant of ∃ is a pair, as previously discussed.  Let's fill in our guesses for the first
  -- components of each pair:

  silly-example₄ : (b : Bool) → ∃ λ b′ → (b ∧ b′) ≡ b′
  silly-example₄ true  = true  , {!!}
  silly-example₄ false = false , {!!}

  -- Look at the types of the holes again.  In the first we have `true ≡ true' and in the second we have
  -- `false ≡ false'.  Both of these holes can therefore be replaced with refl, to obtain:

  silly-example : (b : Bool) → ∃ λ b′ → (b ∧ b′) ≡ b′
  silly-example true  = true  , refl
  silly-example false = false , refl

  -- And we are done!  In summary, to inhabit `∃ λ x → P x' we must explicitly construct a pair `x , p'
  -- where `x' satisfies `P', as witnessed by the second component `p' (of type `P x').

  -- EXERCISE: complete the following:

  ∃-exercise₁ : ∃ λ b → (b ∧ b) ≡ b
  ∃-exercise₁ = false , refl

  -- we can talk about the existence of functions, too!
  ∃-exercise₂ : (b : Bool) → ∃ λ (f : Bool → Bool → Bool) → f b b ≡ b
  ∃-exercise₂ b = (λ x y → x) , refl
