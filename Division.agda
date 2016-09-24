module Division where


open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Maybe as M using (Maybe; nothing; just; drop-just)
open import Data.Nat
open import Data.Nat.Properties using (m≤m+n; ≤-step; ≤⇒≤′)
open import Data.Nat.Properties.Simple
  using (*-right-zero; *-comm; +-right-identity; +-suc; +-comm)
open import Data.Unit using (⊤; tt)

open import Function

open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality as PEq
  using (_≡_; _≢_; refl; sym; trans; subst; cong; module ≡-Reasoning)
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

--_/suc_ : ℕ → ℕ → ℕ
--m /suc n with suc n ≤? m
--m /suc n | yes sucn≤m = {!≤-minus sucn≤m /suc n!}
--m /suc n | no _ = zero
-- The totality checker fails because it can't establish that `≤-minus sucn≤m`
-- is structurally smaller than `m`. We could deduce that `≤-minus sucn≤m` is
-- numerically less than `m`, but we'd still need to do some work to get this
-- into a form the totality checker would be happy with.

-- A representation of natural numbers as a quotient and a remainder
data QuotRem (n : ℕ) : Set where
  _*n+_ : (q : ℕ) (r : Fin n) → QuotRem n

-- Opposite of inject₁
tighten : ∀ {n} (x : Fin (suc n)) → toℕ x ≢ n → Fin n
tighten {zero} zero neq = ⊥-elim (neq refl)
tighten {suc n} zero neq = zero
tighten {zero} (suc ()) neq
tighten {suc n} (suc x) neq = suc (tighten x (neq ∘ cong suc))

-- tighten preserves numerical value.
tighten-correct :
  ∀ {n} (x : Fin (suc n)) (neq : toℕ x ≢ n) → toℕ (tighten x neq) ≡ toℕ x
tighten-correct {zero} zero neq = ⊥-elim (neq refl)
tighten-correct {suc n} zero neq = refl
tighten-correct {zero} (suc ()) neq
tighten-correct {suc n} (suc x) neq =
  cong ℕ.suc (tighten-correct x (neq ∘ cong suc))

-- Successor function for Fin n, failing when there is no larger number
sucF : ∀ {n} → Fin n → Maybe (Fin n)
sucF {zero} ()
sucF {suc n} x with toℕ x ≟ n
sucF {suc n} x | yes p = nothing
sucF {suc n} x | no ¬p = just (suc (tighten x ¬p))

-- If sucF returns something, it is one larger than the number it was given
sucF-correct : ∀ {n} (x y : Fin n) → sucF x ≡ just y → suc (toℕ x) ≡ toℕ y
sucF-correct {suc zero} zero y eq = ⊥-elim (subst P eq tt)
  where
  P : ∀ {a} {A : Set a} → Maybe A → Set
  P (just x) = ⊥
  P nothing = ⊤
sucF-correct {suc (suc n)} zero y eq =
  let eq′ = drop-just (reflexive eq) in
  cong toℕ eq′
  where open Setoid (M.setoid (PEq.setoid _))
sucF-correct {suc n} (suc x) y eq with suc (toℕ x) ≟ n
sucF-correct {suc n} (suc x) y eq | yes p = ⊥-elim (subst P eq tt)
  where
  P : ∀ {a} {A : Set a} → Maybe A → Set
  P (just x) = ⊥
  P nothing = ⊤
sucF-correct {suc n} (suc x) y eq | no ¬p =
  let eq′ = drop-just (reflexive eq) in
  begin
    suc (suc (toℕ x))
  ≡⟨ cong suc (PEq.sym (tighten-correct (suc x) ¬p)) ⟩
    suc (toℕ (tighten (suc x) ¬p))
  ≡⟨⟩
    toℕ (suc (tighten (suc x) ¬p))
  ≡⟨ cong toℕ eq′ ⟩
    toℕ y
  ∎
  where open Setoid (M.setoid (PEq.setoid _))
        open ≡-Reasoning

-- Successor function for numbers represented as quotient and remainder
sucQR : ∀ {n} → QuotRem (suc n) → QuotRem (suc n)
sucQR (q *n+ r) with sucF r
sucQR (q *n+ r) | just r′ = q *n+ r′
sucQR (q *n+ r) | nothing = suc q *n+ zero

ℕ→QuotRem : ∀ {n} → ℕ → QuotRem (suc n)
ℕ→QuotRem zero = zero *n+ zero
ℕ→QuotRem (suc m) = sucQR (ℕ→QuotRem m)

QuotRem→ℕ : ∀ {n} → QuotRem n → ℕ
QuotRem→ℕ {n} (q *n+ r) = q * n + toℕ r

-- sucQR gives the representation of the successor of the number represented
-- by its argument.
QuotRem→ℕ-sucQR : ∀ {n} x → QuotRem→ℕ {suc n} (sucQR x) ≡ suc (QuotRem→ℕ x)
QuotRem→ℕ-sucQR {n} (q *n+ r) with toℕ r ≟ n
QuotRem→ℕ-sucQR {n} (q *n+ r) | yes p = cong suc $
  begin
    n + q * suc n + 0
  ≡⟨ +-right-identity _ ⟩
    n + q * suc n
  ≡⟨ +-comm n (q * suc n) ⟩
    q * suc n + n
  ≡⟨ cong (λ x → q * suc n + x) (sym p) ⟩
    q * suc n + toℕ r
  ∎
  where open ≡-Reasoning
QuotRem→ℕ-sucQR {n} (q *n+ r) | no ¬p =
  begin
    q * suc n + suc (toℕ (tighten r ¬p))
  ≡⟨ cong (λ x → q * suc n + suc x) (tighten-correct r ¬p) ⟩
    q * suc n + suc (toℕ r)
  ≡⟨ +-suc (q * suc n) (toℕ r) ⟩
    suc (q * suc n + toℕ r)
  ∎
  where open ≡-Reasoning

-- div
_/suc_ : ℕ → ℕ → ℕ
m /suc n with ℕ→QuotRem {n} m
m /suc n | q *n+ r = q

-- mod
_%suc_ : ℕ → ℕ → ℕ
m %suc n with ℕ→QuotRem {n} m
m %suc n | q *n+ r = toℕ r

test : ℕ
test = {!ℕ→QuotRem {3} 13!}  -- 13 / 4 = 3 + 1 / 4

-- Inverse in one direction
ℕ→QuotRem→ℕ : ∀ {n} m → QuotRem→ℕ (ℕ→QuotRem {n} m) ≡ m
ℕ→QuotRem→ℕ zero = refl
ℕ→QuotRem→ℕ (suc m) =
  begin
    QuotRem→ℕ (sucQR (ℕ→QuotRem m))
  ≡⟨ QuotRem→ℕ-sucQR (ℕ→QuotRem m) ⟩
    suc (QuotRem→ℕ (ℕ→QuotRem m))
  ≡⟨ cong suc (ℕ→QuotRem→ℕ m) ⟩
    suc m
  ∎
  where open ≡-Reasoning
