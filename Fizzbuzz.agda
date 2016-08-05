module Fizzbuzz where

open import Division using (_divides_; div; _divides?_)

open import Coinduction

open import Data.Empty
open import Data.Nat
open import Data.Nat.Show
open import Data.Product
open import Data.Stream
open import Data.String
open import Data.Vec using (Vec)

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Definition of fizzbuzz
data Fizzbuzz : ℕ → String → Set where
  n3n5 : ∀ {n} → ¬ 3 divides n → ¬ 5 divides n → Fizzbuzz n (showInBase 10 n)
  n3y5 : ∀ {n} → ¬ 3 divides n →   5 divides n → Fizzbuzz n "Buzz"
  y3n5 : ∀ {n} →   3 divides n → ¬ 5 divides n → Fizzbuzz n "Fizz"
  y3y5 : ∀ {n} →   3 divides n →   5 divides n → Fizzbuzz n "Fizzbuzz"

fizzbuzz : ℕ → String
fizzbuzz n =
  case 3 divides? n of λ
  { (yes _) →
    case 5 divides? n of λ
    { (yes _) → "Fizzbuzz"
    ; (no _) → "Fizz"
    }
  ; (no _) →
    case 5 divides? n of λ
    { (yes _) → "Buzz"
    ; (no _) → showInBase 10 n
    }
  }

-- Correctness of fizzbuzz
sound : ∀ n → Fizzbuzz n (fizzbuzz n)
sound n with 3 divides? n
sound n | yes y3 with 5 divides? n
sound n | yes y3 | yes y5 = y3y5 y3 y5
sound n | yes y3 | no n5 = y3n5 y3 n5
sound n | no n3 with 5 divides? n
sound n | no n3 | yes y5 = n3y5 n3 y5
sound n | no n3 | no n5 = n3n5 n3 n5

unambiguous : ∀ {n ss ts} → Fizzbuzz n ss → Fizzbuzz n ts → ss ≡ ts
unambiguous (n3n5 _ _) (n3n5 _ _) = refl
unambiguous (n3n5 _ n5) (n3y5 _ y5) = ⊥-elim (n5 y5)
unambiguous (n3n5 n3 _) (y3n5 y3 _) = ⊥-elim (n3 y3)
unambiguous (n3n5 n3 n5) (y3y5 y3 y5) = ⊥-elim (n3 y3)
unambiguous (n3y5 _ y5) (n3n5 _ n5) = ⊥-elim (n5 y5)
unambiguous (n3y5 _ _) (n3y5 _ _) = refl
unambiguous (n3y5 n3 y5) (y3n5 y3 n5) = ⊥-elim (n3 y3)
unambiguous (n3y5 n3 _) (y3y5 y3 _) = ⊥-elim (n3 y3)
unambiguous (y3n5 y3 _) (n3n5 n3 _) = ⊥-elim (n3 y3)
unambiguous (y3n5 y3 n5) (n3y5 n3 y5) = ⊥-elim (n3 y3)
unambiguous (y3n5 _ _) (y3n5 _ _) = refl
unambiguous (y3n5 _ n5) (y3y5 _ y5) = ⊥-elim (n5 y5)
unambiguous (y3y5 y3 y5) (n3n5 n3 n5) = ⊥-elim (n3 y3)
unambiguous (y3y5 y3 _) (n3y5 n3 _) = ⊥-elim (n3 y3)
unambiguous (y3y5 _ y5) (y3n5 _ n5) = ⊥-elim (n5 y5)
unambiguous (y3y5 _ _) (y3y5 _ _) = refl
-- I'm not happy with there being quadratically many cases, but I suspect that
-- there is no simple way around it (see finite sets).

complete : ∀ n ss → Fizzbuzz n ss → fizzbuzz n ≡ ss
complete n ss fb = unambiguous (sound n) fb

-- Stream of fizzbuzz
fizzbuzz-responses : Stream String
fizzbuzz-responses = go zero
  where
  go : ℕ → Stream String
  go n = (fizzbuzz n) ∷ ♯ (go (suc n))

test : Vec String 17
test = {!take 17 fizzbuzz-responses!}
