-- First steps in Agda: more sophisticated techniques for proving properties of functions.

module E8 where

  -- Remember, somewhere in the first 5 exercises we proved that _+_ on ℕ is commutative.  The
  -- final proof that we came up with was a horrible mess of `trans', `sym', and so on.  Let's
  -- find a neater way of doing proof via Agda's built-in rewrite mechanism:

  -- For the definition of ℕ and _+_
  open import Data.Nat

  -- For _≡_ and friends
  open import Relation.Binary.PropositionalEquality

  -- Let's prove that _+_ is commutative again:

  +-commutative₁ : (m n : ℕ) → m + n ≡ n + m
  +-commutative₁ zero    n = {!!}
  +-commutative₁ (suc m) n = {!!}

  -- We need the same lemma as last time for the first hole:

  +-zero : (m : ℕ) → m ≡ m + zero
  +-zero zero    = refl
  +-zero (suc m) = cong suc (+-zero m)

  +-commutative₂ : (m n : ℕ) → m + n ≡ n + m
  +-commutative₂ zero    n = +-zero n
  +-commutative₂ (suc m) n = {!!}

  -- For the second hole we also need a familiar lemma:

  +-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  -- But now we will do something different to last time!  If we have an equality of the form
  -- x ≡ y, then we can ask Agda to replace all occurrences of x in our goal with y, via Agda's
  -- rewrite facility.  Watch how the types evolve in the following series of steps:

  +-commutative₃ : (m n : ℕ) → m + n ≡ n + m
  +-commutative₃ zero    n = +-zero n
  +-commutative₃ (suc m) n
    rewrite
      +-suc n m = {!!}

  +-commutative₄ : (m n : ℕ) → m + n ≡ n + m
  +-commutative₄ zero    n = +-zero n
  +-commutative₄ (suc m) n
    rewrite
      +-suc n m | +-commutative₄ m n = {!!}

  +-commutative : (m n : ℕ) → m + n ≡ n + m
  +-commutative zero    n = +-zero n
  +-commutative (suc m) n
    rewrite
      +-suc n m | +-commutative m n = refl

  -- Isn't that nicer than the previous proof?  We can chain together multiple rewrites one after
  -- the other using the bar | syntax.  After rewriting, we are left with a trivial proof obligation
  -- that can be closed using refl.  Let's try another one:

  *-commutative₁ : (m n : ℕ) → m * n ≡ n * m
  *-commutative₁ zero    n = {!!}
  *-commutative₁ (suc m) n = {!!}

  -- We need a lemma for the first hole:
  -- EXERCISE: complete the following lemma:

  *-zero : (m : ℕ) → m * zero ≡ zero
  *-zero zero    = {!!}
  *-zero (suc m) = {!!}

  *-commutative₂ : (m n : ℕ) → m * n ≡ n * m
  *-commutative₂ zero    n = sym (*-zero n)
  *-commutative₂ (suc m) n = {!!}

  -- EXERCISE: spot the lemma (or multiple lemmas) required to close the second hole above and
  -- complete the proof of *-commutative using rewrite.

  -- EXERCISE: complete the following using rewrite.  You may need additional lemmas!  State and
  -- prove them too.

  +-associative : (m n o : ℕ) → m + (n + o) ≡ (m + n) + o
  +-associative m n o = {!!}

  *-+-distributiveᵣ : (m n o : ℕ) → m * (n + o) ≡ (m * n) + (m * o)
  *-+-distributiveᵣ m n o = {!!}

  -- Definition of exponentiation on ℕ:
  pow : ℕ → ℕ → ℕ
  pow b zero    = suc zero
  pow b (suc e) = pow b e * b

  zero-pow : (m : ℕ) → pow zero m ≡ zero
  zero-pow m = {!!}

  +-pow : (b m n : ℕ) → pow b (m + n) ≡ pow b m * pow b n
  +-pow b m n = {!!}

  *-pow : (b c m : ℕ) → pow b m * pow c m ≡ pow (b * c) m
  *-pow b c m = {!!}
