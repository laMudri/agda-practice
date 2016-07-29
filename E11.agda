module E11 where

  open import Level

  open import Data.Sum

  open import Relation.Binary.PropositionalEquality

  -- In this module we will develop the theory of ordered sets.  Ordered sets again form
  -- a hierarchy, like the algebraic structures of exercise 10.  We have:
  --
  --     A pre-order (or quasi-order) is a tuple ⟨M, <⟩ where M is a set and < is a binary
  --     relation on M.  < is reflexive and transitive.
  --
  --     A partial order is a tuple ⟨M, <⟩ where M is a set and < is a binary relation on M.
  --     < is reflexive, transitive and anti-symmetric.  A partial order is therefore
  --     necessarily a pre-order too.
  --
  --     A total order is a tuple ⟨M, <⟩ where M is a set and < is a binary relation on M.
  --     < is transitive, anti-symmetric and total.  It is a fact that these laws are enough
  --     to establish that < is also reflexive, and therefore a total order is necessarily
  --     a partial order too.
  --
  -- Given the following definitions:

  Rel₂ : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
  Rel₂ {ℓ} A = A → A → Set ℓ

  IsAntiSymmetric : ∀ {ℓ} → {A : Set ℓ} → Rel₂ A → Set ℓ
  IsAntiSymmetric _R_ = ∀ x y → x R y → y R x → x ≡ y

  IsReflexive : ∀ {ℓ} → {A : Set ℓ} → Rel₂ A → Set ℓ
  IsReflexive _R_ = ∀ x → x R x

  IsTransitive : ∀ {ℓ} → {A : Set ℓ} → Rel₂ A → Set ℓ
  IsTransitive _R_ = ∀ x y z → x R y → y R z → x R z

  IsTotal : ∀ {ℓ} → {A : Set ℓ} → Rel₂ A → Set ℓ
  IsTotal _R_ = ∀ x y → x R y ⊎ y R x

  -- Define the following records:
  --
  -- IsPreOrder and PreOrder
  --
  -- IsPartialOrder and PartialOrder
  --
  -- IsTotalOrder and TotalOrder
  --
  -- EXERCISE: complete the above.  Use whatever modules from the standard library (barring
  -- the existing implementations of these concepts) that you feel are necessary.  Follow the
  -- same pattern as in exercise 10: for each module M′ that sits above modules M₁ … Mₙ in the
  -- hierarchy, provide ways of obtaining an inhabitant of Mᵢ (for 1≤i≤n) via down-projection
  -- functions.

  -- Recall that an equivalence relation on a set is a binary relation that is reflexive,
  -- transitive and symmetric.  Equivalence relations are often used to quotient a set into
  -- equivalence classes.  For example, when working with the λ-calculus, it is often useful to
  -- work with λ-terms that have been quotiented by the α-equivalence relation.
  --
  -- How can we model an equivalence relation and quotienting in Agda?  We use a structure
  -- called a setoid, which is a record that packages up a type `Carrier' with an equivalence
  -- relation over that type.
  --
  -- Using the following definitions

  IsSymmetric : ∀ {ℓ} → {A : Set ℓ} → Rel₂ A → Set ℓ
  IsSymmetric _R_ = ∀ x y → x R y → y R x

  -- and whatever definitions you need from the previous set, define the following records:
  --
  -- IsSetoid and Setoid

  -- EXERCISE: complete the above.  Use whatever modules from the standard library (barring
  -- existing implementations of this concept) that you feel necessary.

  -- Given a pre-order ⟨M, <⟩ one may construct an induced equivalence relation on M, call
  -- it `≃' (type \simeq to obtain that symbol in Unicode), with the following definition:
  --
  --     x ≃ y  =  (x < y) ∧ (y < x)
  --
  -- Using a nested, parameterised module that takes an inhabitant of your PreOrder record as
  -- argument, construct an inhabitant of Setoid using the above definition.
  --
  -- EXERCISE: complete the above.  Use whatever modules from the standard library that you
  -- feel necessary.
