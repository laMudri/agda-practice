module Division where

open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Nat.Properties using (m≤m+n; ≤-step; ≤⇒≤′)
open import Data.Nat.Properties.Simple
  using (*-right-zero; *-comm; +-right-identity)
open import Data.Unit using (⊤; tt)

open import Function

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no)

data _divides_ : ℕ → ℕ → Set where
  div : {m n : ℕ} (k : ℕ) (eq : n ≡ k * m) → m divides n

-- Basic lemmata about divisibility
zero-divides⇒is-zero : ∀ {n} → zero divides n → n ≡ zero
zero-divides⇒is-zero (div k eq) = trans eq (*-right-zero k)

m-divides-zero : ∀ {m} → m divides zero
m-divides-zero = div zero refl

-- I like proving this separately, and not relying on absurd patterns
suc≢zero : ∀ {n} → suc n ≢ zero
suc≢zero eq = subst P eq tt
  where
  P : ℕ → Set
  P zero = ⊥
  P (suc n) = ⊤

-- A helper type for bounded recursive checking of divisors
data divides≤′ : (l m n : ℕ) → Set where
  div≤′ : {l m n : ℕ} (k : ℕ) (le : k ≤′ l) (eq : n ≡ k * m) → divides≤′ l m n

dec-lemma : (l m n : ℕ) → Dec (divides≤′ l (suc m) (suc n))
dec-lemma zero m n = no (λ { (div≤′ .0 ≤′-refl eq) → suc≢zero eq })
dec-lemma (suc l) m n with dec-lemma l m n
dec-lemma (suc l) m n | yes (div≤′ k le eq) = yes (div≤′ k (≤′-step le) eq)
dec-lemma (suc l) m n | no ¬d with suc n ≟ suc l * suc m
dec-lemma (suc l) m n | no ¬d | yes eq = yes (div≤′ (suc l) ≤′-refl eq)
dec-lemma (suc l) m n | no ¬d | no ¬eq =
  no (λ { (div≤′ _ ≤′-refl      eq) → ¬eq eq
        ; (div≤′ k (≤′-step le) eq) → ¬d (div≤′ k le eq) })

-- The helper type gives us what we want
divides≤′⇒divides : ∀ {l m n} → divides≤′ l m n → m divides n
divides≤′⇒divides (div≤′ k le eq) = div k eq

divides⇒divides≤′ : ∀ {m n} → suc m divides n → divides≤′ n (suc m) n
divides⇒divides≤′ {m} {n} (div k eq) = div≤′ k (≤⇒≤′ (begin
  k          ≤⟨ m≤m+n k (m * k) ⟩
  k + m * k  ≡⟨⟩
  suc m * k  ≡⟨ sym (*-comm k (suc m)) ⟩
  k * suc m  ≡⟨ sym eq ⟩
  n          ∎)) eq
  where
  open ≤-Reasoning renaming (_≈⟨⟩_ to _≡⟨⟩_)

-- Main theorem: divisibility is decidable
_divides?_ : (m n : ℕ) → Dec (m divides n)
zero divides? zero = yes (div zero refl)
zero divides? suc n = no (suc≢zero ∘ zero-divides⇒is-zero)
suc m divides? zero = yes m-divides-zero
suc m divides? suc n with dec-lemma (suc n) m n
suc m divides? suc n | yes p = yes (divides≤′⇒divides p)
suc m divides? suc n | no ¬p = no (¬p ∘ divides⇒divides≤′)

-- Each number is divisible by 1 and itself
one-divides-n : ∀ n → 1 divides n
one-divides-n n = div n (begin
  n      ≡⟨ sym (+-right-identity n) ⟩
  n + 0  ≡⟨ refl ⟩
  1 * n  ≡⟨ *-comm 1 n ⟩
  n * 1  ∎)
  where
  open ≡-Reasoning

n-divides-n : ∀ n → n divides n
n-divides-n n = div 1 (begin
  n      ≡⟨ sym (+-right-identity n) ⟩
  n + 0  ≡⟨ refl ⟩
  1 * n  ∎)
  where
  open ≡-Reasoning

-- Division
≤-minus : ∀ {x y} → x ≤ y → ℕ
≤-minus {y = y} z≤n = y
≤-minus (s≤s x≤y) = ≤-minus x≤y

_/suc_ : ℕ → ℕ → ℕ
m /suc n with suc n ≤? m
m /suc n | yes sucn≤m = {!≤-minus sucn≤m /suc n!}
m /suc n | no _ = zero
-- The totality checker fails because it can't establish that `≤-minus sucn≤m`
-- is structurally smaller than `m`. We could deduce that `≤-minus sucn≤m` is
-- numerically less than `m`, but we'd still need to do some work to get this
-- into a form the totality checker would be happy with.
