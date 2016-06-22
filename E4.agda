-- First steps with Agda: simple proof.

module E4 where

  -- As always, uncomment the following when ready:
  --
  open import E1
    renaming (¬_ to ¬Bool_)
  open import E2
  open import E3

  -- Note how we can rename functions when we import a module.  This is to avoid name
  -- clashes, either with functions from other modules we are importing, or with functions
  -- that we are going to define in this module.  Note also we can hide functions when
  -- importing modules using the following syntax:
  --
  -- open import Exercise1
  --   hiding (¬_)
  --
  -- Or we can pick a subset of the available functions from a module to import using the
  -- following syntax:
  --
  -- open import Exercise1
  --   using (Bool ; true ; false)
  --
  -- Note how importing a type does not automatically import its constructors!  We have to
  -- import true and false as well explicitly, if we wish to use them.

  -- Let us now use everything that we have defined so far to prove some simple
  -- properties of our functions.  Let's start with showing that _+_ is commutative:

  +-commutative₁ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₁ m n = {!!}

  -- Inspect the goal state above.  Recall how _+_ was defined: it was a recursive function
  -- that recursed on its first argument.  We will therefore also establish +-commutative
  -- holds by recursion.  Let's examine m first:

  +-commutative₂ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₂ zero     n = {!!}
  +-commutative₂ (succ m) n = {!!}

  -- Inspect the goal states above.  Neither is directly solvable yet.  Let's now inspect n
  -- too:

  +-commutative₃ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₃ zero     zero     = {!!}
  +-commutative₃ zero     (succ n) = {!!}
  +-commutative₃ (succ m) n        = {!!}

  -- Aha!  The first goal is zero ≡ zero, which can be solved using refl.  The second goal is
  -- more complicated and looks like we need to establish another property first, using a lemma,
  -- before we can close this one.  Here's the relevant lemma below, which states that zero is
  -- a right neutral for _+_.

  +-zero₁ : (n : ℕ) → n ≡ (n + zero)
  +-zero₁ zero     = refl
  +-zero₁ (succ n) = {!!}

  -- Examine the proof state above.  Note how we have succ n ≡ succ (n + zero) as our goal.  The
  -- type of +-zero₁ is n ≡ (n + zero).  To be able to make a recursive call we need to get rid
  -- of that succ.  Recall the type of cong: … → x ≡ y → f x ≡ f y, where f ≈ succ here.  Let's
  -- use cong to shift that succ then:

  +-zero₂ : (n : ℕ) → n ≡ (n + zero)
  +-zero₂ zero     = refl
  +-zero₂ (succ n) = cong succ {!!}

  -- Inspect the proof state above.  We can now make a recursive call (corresponding to an application
  -- of the inductive hypothesis --- we are doing a proof by induction on the first argument, here):

  +-zero : (n : ℕ) → n ≡ (n + zero)
  +-zero zero     = refl
  +-zero (succ n) = cong succ (+-zero n)

  -- Note in Agda proof by induction is carried out by writing a recursive function.  Induction and
  -- recursion are one and the same.  We can now use +-zero to close another goal in our +-commutative
  -- proof, using cong again:

  +-commutative₄ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₄ zero     zero     = refl
  +-commutative₄ zero     (succ n) = cong succ (+-zero n)
  +-commutative₄ (succ m) n        = {!!}

  -- We now do another case analysis on n, in the succ m case:

  +-commutative₅ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₅ zero     zero     = refl
  +-commutative₅ zero     (succ n) = cong succ (+-zero n)
  +-commutative₅ (succ m) zero     = {!!}
  +-commutative₅ (succ m) (succ n) = {!!}

  -- Examine the proof state again.  What do we have?  Something that looks remarkably familiar, and 
  -- should be solvable using +-zero again, but the goal is reversed.  Recall the type of sym:
  --
  --    … → x ≡ y → y ≡ x
  --
  -- We will need to use sym, cong, and +-zero here to close the first hole:

  +-commutative₆ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₆ zero     zero     = refl
  +-commutative₆ zero     (succ n) = cong succ (+-zero n)
  +-commutative₆ (succ m) zero     = cong succ (sym (+-zero m))
  +-commutative₆ (succ m) (succ n) = {!!}

  -- Examine the proof state above.  We can use cong to get rid of those top-level succs, but that still
  -- leaves us with the two succs on the right-hand sides of the additions.  Looks like we need yet
  -- another lemma, which allows us to shift them!

  +-succ : (m n : ℕ) → (m + succ n) ≡ succ (m + n)
  +-succ zero     n = refl
  +-succ (succ m) n = cong succ (+-succ m n)

  -- Let's try again:

  +-commutative₇ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₇ zero     zero     = refl
  +-commutative₇ zero     (succ n) = cong succ (+-zero n)
  +-commutative₇ (succ m) zero     = cong succ (sym (+-zero m))
  +-commutative₇ (succ m) (succ n) = cong succ {!!}

  -- Examine the proof state above.  Looks like we need trans:

  +-commutative₈ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₈ zero     zero     = refl
  +-commutative₈ zero     (succ n) = cong succ (+-zero n)
  +-commutative₈ (succ m) zero     = cong succ (sym (+-zero m))
  +-commutative₈ (succ m) (succ n) = cong succ (trans (+-succ m n) {!!})

  -- Examine the proof state above.  Trans again, with cong too?

  +-commutative₉ : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative₉ zero     zero     = refl
  +-commutative₉ zero     (succ n) = cong succ (+-zero n)
  +-commutative₉ (succ m) zero     = cong succ (sym (+-zero m))
  +-commutative₉ (succ m) (succ n) = cong succ (trans (+-succ m n) (trans (cong succ {!!}) {!!}))

  -- Examine the proof states above.  The first is now a recursive call to +-commutative, whilst
  -- the second is another application of +-succ reversed using sym.  Note the canary yellow above
  -- where Agda is telling you that there are types it cannot infer (because there's bits of terms
  -- missing).  Let's try to finish off +-commutative now.

  +-commutative : (m n : ℕ) → (m + n) ≡ (n + m)
  +-commutative zero     zero     = refl
  +-commutative zero     (succ n) = cong succ (+-zero n)
  +-commutative (succ m) zero     = cong succ (sym (+-zero m))
  +-commutative (succ m) (succ n) = cong succ (trans (+-succ m n) (trans (cong succ (+-commutative m n)) (sym (+-succ n m))))

  -- That's an ugly proof.  The succ m, succ n case is much more complicated than it need be.  We'll
  -- discuss ways of making this much nicer later.

  -- EXERCISE: try to close the following.  You may need additional lemmas!

  map-length : {A B : Set} → (xs : List A) → (f : A → B) → length (map f xs) ≡ (length xs)
  map-length [] f = refl
  map-length (x ∷ xs) f = cong succ (map-length xs f)

  ⊕-[] : {A : Set} → (xs : List A) → (xs ⊕ []) ≡ xs
  ⊕-[] [] = refl
  ⊕-[] (x ∷ xs) = cong (_∷_ x) (⊕-[] xs)

  ⊕-length : {A : Set} → (xs ys : List A) → length (xs ⊕ ys) ≡ (length xs + length ys)
  ⊕-length [] ys = refl
  ⊕-length (x ∷ xs) ys = cong succ (⊕-length xs ys)

  -- What about negation?  We can define negation like so:

  ¬ : Set → Set
  ¬ A = A → 𝟘

  -- i.e. ¬ A is merely the same as stating that A implies False.  We can define not equal as:

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = ¬ (x ≡ y)

  -- EXERCISE: try to establish the following:

  succ-≢-zero : (m : ℕ) → succ m ≢ zero
  succ-≢-zero m = λ { () }
