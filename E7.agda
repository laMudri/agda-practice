-- First steps in Agda: using the Standard Library.

module E7 where

  -- Let's get serious.  Agda has a fairly well-developed Standard Library that, with
  -- the exception of the Level module, we have been ignoring to date.  Let's now use
  -- some of the definitions in that library to push our understanding further:

  -- For universe levels
  open import Level

  -- For functions that combine other functions in useful ways, for example composition,
  -- generalised curry and uncurry functions, the identity combinator, and so on.
  open import Function

  -- The Booleans, naturals and lists.
  open import Data.Bool
  open import Data.Nat
  open import Data.List

  -- Propositional equality, and related notions.
  open import Relation.Binary.PropositionalEquality
    hiding ([_]) -- this clashes with the definition of singleton list in Data.List

  -- You can, as always, inspect the contents of these modules by middle mouse-clicking
  -- on their names after Agda has type-checked and syntax highlighted the files.

  -- Let's write a function that removes duplicate elements from a list.  In Haskell, this
  -- function is called `nub'.  We'll use the same name here.
  --
  -- Naturally, we have a problem when writing `nub'.  How do we decide if two elements of
  -- a list are equal?  In Haskell, this problem is solved by adding a type-class constraint
  -- to the type of `nub', ensuring we can compare elements of the list.  We will avoid using
  -- Agda's equivalent of type classes for the moment, though (they're strictly less powerful
  -- than Haskell's, for a start, and I try not to use them myself), in favour of using some
  -- other techniques.  However, we can start by taking as argument to the `nub' function
  -- another function that compares elements for equality:

  member₁ : {ℓ : Level} → {A : Set ℓ} → (A → A → Bool) → A → List A → Bool
  member₁ comp e []       = false
  member₁ comp e (x ∷ xs) = if comp e x then true else member₁ comp e xs

  nub₁ : {ℓ : Level} → {A : Set ℓ} → (A → A → Bool) → List A → List A
  nub₁ comp xs = go comp [] xs
    where
      go : {ℓ : Level} → {A : Set ℓ} → (A → A → Bool) → List A → List A → List A
      go comp buffer []       = buffer
      go comp buffer (x ∷ xs) =
        if member₁ comp x buffer then
          go comp buffer xs
        else
          go comp (buffer ++ [ x ]) xs

  -- Here _++_ is list append, what we called _⊕_ in our previous exercises.
  --
  -- As you can see, Agda allows local function and constant definitions in a function clause
  -- via the use of the `where' keyword, similar to Haskell.
  --
  -- Let's test nub₁:

  _≈_ : Bool → Bool → Bool
  true  ≈ c = c
  false ≈ c = not c

  nub-test : _
  nub-test = {!nub₁ _≈_ (true ∷ true ∷ false ∷ [])!}

  -- Put your cursor in the hole above and type <Ctrl> + <c> + <n>.  This `normalises' the term
  -- in the hole (i.e. it fully executes nub₁ on the given arguments) and prints the result in
  -- a window below.  You should see something like true ∷ false ∷ [] as a result.  You could
  -- alternatively just press <Ctrl> + <c> + <n> at any time and type in what you want to normalise
  -- without creating a dummy hole like nub-test above to do it.
  --
  -- But that passing around a function between nub₁ and member isn't particularly nice.  The
  -- function never is changed, it's just passed between the two functions in an act of book-
  -- keeping.  It would be nicer if we could just assume its presence and use it.
  --
  -- Agda has a mechanism for achieving this, via nested, parameterised modules.  Let's rewrite
  -- member and nub to make use of these:

  module AssumesComparison {ℓ : Level} {A : Set ℓ} (_≈_ : A → A → Bool) where

    _∈₂_ : A → List A → Bool
    e ∈₂ []       = false
    e ∈₂ (x ∷ xs) = if e ≈ x then true else e ∈₂ xs

    nub₂ : List A → List A
    nub₂ xs = go [] xs
      where
        go : List A → List A → List A
        go buffer []       = buffer
        go buffer (x ∷ xs) =
          if x ∈₂ buffer then
            go buffer xs
          else
            go (buffer ++ [ x ]) xs

  -- Much neater.  But now how do we use nub₂ and _∈₂_?  We must open the AssumesComparison module,
  -- providing the fixed comparison function when we do so.  For example:

  open AssumesComparison _≈_ -- where _≈_ is the Bool comparison defined above

  nub-test₂ : _
  nub-test₂ = {!nub₂ (true ∷ true ∷ false ∷ [])!}

  -- And everything works once more.
  --
  -- However, there is still something unsatisfying about our definitions.  Recall that
  -- PropositionalEquality is able to test whether two elements of *any* type are equal.  Using
  -- PropositionalEquality, we'd be able to dispense with type-specific comparison functions
  -- altogether in favour of a uniform treatment of comparison across all types.  In short, we'd
  -- be able to write nub₃ that worked for any and every type.
  --
  -- However, note what we are doing in the definition of nub₁ and nub₂: we are branching on the
  -- result of the comparison function _≈_, doing one thing if it returns true, and another thing
  -- if it is not, using if_then_else_.  To be able to use _≡_ instead of _≈_ we need to be able
  -- to branch on whether e ≡ x or not in the definition of _∈_.  We cannot use if_then_else_, as
  -- that is for Bool, so what can we use?
  --
  -- Let's experiment:

  -- First, we'll show that at type Bool, _≡_ is decidable.  What does decidable mean?  It means
  -- that for every b, c of type Bool, it is either the case that b ≡ c, or it is the case that
  -- b ≢ c.

  -- The definition of decidability resides in the following module.  Middle mouse-click to take
  -- a look:
  open import Relation.Binary
  -- The definition of Dec, which is also used to define decidability, is in the following module:
  open import Relation.Nullary  -- JDW: current stdlib (2.5.1) has no Relation.Nullary.Core.
                                -- See 3264b9e in agda-stdlib.
  -- This is the empty type, what we previously called 𝟘.  In the Agda standard library, this type
  -- is now called ⊥.  What we also previously called ex-falso is called ⊥-elim.  Both will be
  -- needed below.
  open import Data.Empty

  Bool-Decidable₁ : Decidable (_≡_ {A = Bool})
  Bool-Decidable₁ = {!!}

  -- Take a look at the type of the hole above, and see what we need to supply.  At the moment the
  -- type is `Decidable _≡_'.  This is a synonym for (b : Bool) → (c : Bool) → Dec (b ≡ c).  Let's
  -- further refine Bool-Decidable:

  Bool-Decidable₂ : Decidable (_≡_ {A = Bool})
  Bool-Decidable₂ b c = {!!}

  -- We must now show Dec (b ≡ c).  Dec is a data type with two constructors, yes, which will be used
  -- to signal that b ≡ c, and no, which will be used to signal b ≢ c.  Let's proceed by pattern
  -- matching on b and c:

  Bool-Decidable₃ : Decidable (_≡_ {A = Bool})
  Bool-Decidable₃ true  true  = {!!}
  Bool-Decidable₃ true  false = {!!}
  Bool-Decidable₃ false true  = {!!}
  Bool-Decidable₃ false false = {!!}

  -- You'll note that now the types have changed in the holes, in light of us revealing more information
  -- about b and c to the typechecker via pattern matching.  In the first hole, we now have to show that
  -- Dec (true ≡ true).  Clearly true ≡ true, via refl, so we can use `yes', here:

  Bool-Decidable₄ : Decidable (_≡_ {A = Bool})
  Bool-Decidable₄ true  true  = yes refl
  Bool-Decidable₄ true  false = {!!}
  Bool-Decidable₄ false true  = {!!}
  Bool-Decidable₄ false false = {!!}

  -- A little note about what we are doing, now: we are being asked to consider all cases and construct
  -- proofs that either b ≡ c, or b ≢ c, embedding these proofs in the constructors of a datatype called
  -- Dec.  But, as Dec is just another data type, we will be free later to pattern match on elements of
  -- type Dec and retrieve these proofs.  That is, Dec is not merely a way of performing branching like
  -- if_then_else_, but it is also informative, providing documentary evidence, in the form of proofs,
  -- of why we should branch one way or the other.  This will be useful later when we come to prove things
  -- about various functions --- the more information we know, the better!
  --
  -- Back to Bool-Decidable: the last case asks us to show Dec (false ≡ false).  Clearly false ≡ false, so
  -- we will use `yes' again here to close the hole.  However, the middle two holes ask us to show
  -- Dec (true ≡ false) (and its symmetrical counterpart), respectively.  Clearly true ≢ false, so we will
  -- use instead the `no' constructor this time:

  Bool-Decidable₅ : Decidable (_≡_ {A = Bool})
  Bool-Decidable₅ true  true  = yes refl
  Bool-Decidable₅ true  false = no {!!}
  Bool-Decidable₅ false true  = no {!!}
  Bool-Decidable₅ false false = yes refl

  -- Look at the types of the holes.  We are now asked to show ¬ true ≡ false (and symmetrically, ¬ false ≡ true).
  -- Remember how ¬ is encoded in Agda: ¬ true ≡ false is a synonym for true ≡ false → ⊥, where ⊥ is the
  -- empty type, what we suggestively called 𝟘 in our previous exercises.  We can therefore refine our holes
  -- further, as λ-abstractions:

  Bool-Decidable₆ : Decidable (_≡_ {A = Bool})
  Bool-Decidable₆ true  true  = yes refl
  Bool-Decidable₆ true  false = no (λ x → {!!})
  Bool-Decidable₆ false true  = no (λ x → {!!})
  Bool-Decidable₆ false false = yes refl

  -- Look at the goal states again.  We have to construct an element of ⊥ given a variable of type false ≡ true
  -- or true ≡ false.  Clearly true ≡ false is absurd, so we should be able to deduce anything from it,
  -- including ⊥.  Let's introduce a lemma:

  true-false-absurd₁ : {ℓ : Level} → {A : Set ℓ} → true ≡ false → A
  true-false-absurd₁ true≡false = {!!}

  -- true ≡ false is indeed absurd, and Agda can recognise this.  Pattern matching on true≡false, Agda replaces
  -- the pattern variable with the absurd pattern, closing the proof obligation, and we are done:

  true-false-absurd : {ℓ : Level} → {A : Set ℓ} → true ≡ false → A
  true-false-absurd ()

  -- We can now complete Bool-Decidable:

  Bool-Decidable : Decidable (_≡_ {A = Bool})
  Bool-Decidable true  true  = yes refl
  Bool-Decidable true  false = no (λ x → true-false-absurd x)
  Bool-Decidable false true  = no (λ x → true-false-absurd (sym x))
  Bool-Decidable false false = yes refl

  -- Let's try to write a variant of nub that makes use of the decidability of _≡_ at a given
  -- type:

  module AssumesDecidability {ℓ : Level} {A : Set ℓ} (≡-decidable : Decidable (_≡_ {A = A})) where

    -- The unit type, which we previously called 𝟙, is called ⊤ in Agda's standard library.  We'll
    -- need it for what follows.  Note you can import other modules inside nested modules:
    open import Data.Unit

    -- Define list membership:

    _∈_ : A → List A → Set
    e ∈ []       = ⊥
    e ∈ (x ∷ xs) with ≡-decidable e x
    ... | yes e≡x = ⊤
    ... | no  e≢x = e ∈ xs

    -- Note that we are no longer using Bool to signal membership.  Rather, we are using Set, and using
    -- ⊥ and ⊤ for True and False (recall our previous discussions on how to embed logic in Agda's types)!

    nub₃ : List A → List A
    nub₃ xs = go [] xs
      where
        go : List A → List A → List A
        go buffer []       = {!!}
        go buffer (x ∷ xs) = {!!}

    -- Hmm, we are stuck.  We now need to test whether x ∈ buffer, but now _∈_ is in Set, not Bool, and
    -- therefore we cannot use if_then_else_.  The answer…

    ∈-decidable₁ : Decidable _∈_
    ∈-decidable₁ e []       = {!!}
    ∈-decidable₁ e (x ∷ xs) = {!!}

    -- First hole asks us for `Dec (e ∈ [])', which reduces to `Dec ⊥'.  We use the `no' constructor:

    ∈-decidable₂ : Decidable _∈_
    ∈-decidable₂ e []       = no {!!}
    ∈-decidable₂ e (x ∷ xs) = {!!}

    -- First hole now requires us show that ¬ ⊥.  This is a synonym for ⊥ → ⊥.  This is the type of the
    -- id combinator:

    ∈-decidable₃ : Decidable _∈_
    ∈-decidable₃ e []       = no id
    ∈-decidable₃ e (x ∷ xs) = {!!}

    -- Now the hole above has some wacky type.  Why?  Because further reduction is dependent on the results
    -- of ≡-decidable e x (the latter part of the type).  We must use with to inspect that, as follows:

    ∈-decidable₄ : Decidable _∈_
    ∈-decidable₄ e []       = no id
    ∈-decidable₄ e (x ∷ xs) with ≡-decidable e x
    ... | yes e≡x = {!!}
    ... | no  e≢x = {!!}

    -- The first hole now has type `Dec ⊤'.  We use `yes', which then requires we produce a value of type `⊤'.
    -- This is easy --- it's just the unit value, which we previously called it, but which is called `tt' in
    -- the Agda standard library:

    ∈-decidable₅ : Decidable _∈_
    ∈-decidable₅ e []       = no id
    ∈-decidable₅ e (x ∷ xs) with ≡-decidable e x
    ... | yes e≡x = yes tt
    ... | no  e≢x = {!!}

    -- The final hole requires that we construct some value of type `Dec (e ∈ xs)'.  But we know how to do this
    -- by making a recursive call to ∈-decidable itself, and with that we are done:

    ∈-decidable : Decidable _∈_
    ∈-decidable e []       = no id
    ∈-decidable e (x ∷ xs) with ≡-decidable e x
    ... | yes e≡x = yes tt
    ... | no  e≢x = ∈-decidable e xs

    -- We can now make use of ∈-decidable to define nub:

    nub₅ : List A → List A
    nub₅ xs = go [] xs
      where
        go : List A → List A → List A
        go buffer []       = buffer
        go buffer (x ∷ xs) with ∈-decidable x buffer
        ... | yes x∈buffer = go buffer xs
        ... | no  x∉buffer = go (buffer ++ [ x ]) xs

    -- And we are done

  -- Let's now use nub₅ by opening AssumesDecidability:

  open AssumesDecidability Bool-Decidable

  nub-test₃ : _
  nub-test₃ = {!nub₅ (true ∷ true ∷ false ∷ [])!}

  -- And it seems to compute the correct result…

  -- Now, at first sight all of the decidability results above seem like much more work than working
  -- with Boolean functions to perform tests.  But, as mentioned, Booleans are very uninformative.
  -- A Boolean result will only tell you whether some test has succeeded or not --- it will never be
  -- able to tell you why that result has succeeded.  Using the Dec datatype, we not only get the
  -- ability to tell when a test has succeeded (i.e. whether e ∈ xs, or whether b ≡ c, and so on),
  -- but we get a concrete proof that asserts or denies that fact which we can use further.  As a result
  -- Booleans and Boolean-valued functions are almost always eschewed in Agda in favour of working with
  -- decidable fragments of various relations.

  -- EXERCISE: complete the following:

  -- Even though there are no inhabitants of ⊥ we can still talk in the abstract as if there were…
  ⊥-Decidable : Decidable (_≡_ {A = ⊥})
  ⊥-Decidable () f

  -- Note how the contents of Data.Unit is not in scope here as we imported it in a submodule, AssumesDecidability,
  -- above and not at the top level.  We import it again at the top level.
  open import Data.Unit

  ⊤-Decidable : Decidable (_≡_ {A = ⊤})
  ⊤-Decidable tt tt = yes refl

  ℕ-Decidable : Decidable (_≡_ {A = ℕ})
  ℕ-Decidable ℕ.zero ℕ.zero = yes refl
  ℕ-Decidable ℕ.zero (ℕ.suc n) = no (λ ())
  ℕ-Decidable (ℕ.suc m) ℕ.zero = no (λ ())
  ℕ-Decidable (ℕ.suc m) (ℕ.suc n) with ℕ-Decidable m n
  ... | yes p = yes (cong ℕ.suc p)
  ... | no ¬p = no (¬p ∘ suc-injective)
    where
    suc-injective : ∀ {m n} → ℕ.suc m ≡ ℕ.suc n → m ≡ n
    suc-injective refl = refl

  -- A little harder, and requires you to lift a decidability result on elements to a decidability result
  -- on lists of elements…
  List-A-Decidable : {ℓ : Level} → {A : Set ℓ} → (≡-decidable : Decidable (_≡_ {A = A})) → Decidable (_≡_ {A = List A})
  List-A-Decidable ≡-decidable [] [] = yes refl
  List-A-Decidable ≡-decidable [] (x ∷ ys) = no (λ ())
  List-A-Decidable ≡-decidable (x ∷ xs) [] = no (λ ())
  List-A-Decidable ≡-decidable (x ∷ xs) (y ∷ ys) with ≡-decidable x y
  List-A-Decidable ≡-decidable (x ∷ xs) (y ∷ ys) | yes x≡y with List-A-Decidable ≡-decidable xs ys
  List-A-Decidable ≡-decidable (x ∷ xs) (y ∷ ys) | yes x≡y | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
  List-A-Decidable ≡-decidable (x ∷ xs) (y ∷ ys) | yes _ | no ¬p = no (¬p ∘ tails-≡)
    where
    tails-≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
    tails-≡ refl = refl
  List-A-Decidable ≡-decidable (x ∷ xs) (y ∷ ys) | no ¬p = no (¬p ∘ heads-≡)
    where
    heads-≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
    heads-≡ refl = refl

  -- How about lifting two such results?

  -- This is Agda's implementation of the disjoint union type that we defined in exercises 1-5.  It has the same
  -- name as we used.
  open import Data.Sum

  ⊎-A-B-Decidable : {ℓ : Level} → {A B : Set ℓ} → (≡-A-decidable : Decidable (_≡_ {A = A})) →
                      (≡-B-Decidable : Decidable (_≡_ {A = B})) → Decidable (_≡_ {A = A ⊎ B})
  ⊎-A-B-Decidable ≡-A-decidable ≡-B-decidable (inj₁ x) (inj₁ y) with ≡-A-decidable x y
  ... | yes p = yes (cong inj₁ p)
  ... | no ¬p = no (¬p ∘ inj₁-injective)
    where
    inj₁-injective : ∀ {a b} {A : Set a} {B : Set b} {x y : A} → inj₁ {b = b} {B = B} x ≡ inj₁ y → x ≡ y
    inj₁-injective refl = refl
  ⊎-A-B-Decidable ≡-A-decidable ≡-B-decidable (inj₁ _) (inj₂ _) = no (λ ())
  ⊎-A-B-Decidable ≡-A-decidable ≡-B-decidable (inj₂ _) (inj₁ _) = no (λ ())
  ⊎-A-B-Decidable ≡-A-decidable ≡-B-decidable (inj₂ x) (inj₂ y) with ≡-B-decidable x y
  ... | yes p = yes (cong inj₂ p)
  ... | no ¬p = no (¬p ∘ inj₂-injective)
    where
    inj₂-injective : ∀ {a b} {A : Set a} {B : Set b} {x y : B} → inj₂ {a = a} {A = A} x ≡ inj₂ y → x ≡ y
    inj₂-injective refl = refl
