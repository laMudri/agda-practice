-- First steps in Agda: designing hierarchies with records

module E10 where

  open import Level
    renaming (zero to ℓzero ; suc to ℓsuc ; _⊔_ to _ℓ⊔_)
  
  open import Data.Nat
    hiding (fold)
  open import Data.List
    hiding (monoid)

  open import Relation.Binary.PropositionalEquality

  -- In the last exercise you were introduced to Agda's records and shown how to capture a
  -- single algebraic structure (the monoid).  In abstract algebra, monoids sit in a hierarchy
  -- of similar structures.  In particular, we have:
  --
  --   A magma ⟨M, •⟩ consists of a set M coupled with a binary operation • over that set.
  --
  --   A monoid ⟨M, •, ε⟩ consists of a set M coupled with a binary operation • over that set,
  --   as well as a distinguished element of M called ε.  • is associative and ε forms a left
  --   and right identity for •.
  --
  --   A commutative monoid ⟨M, •, ε⟩ consists of a set M coupled with a binary operation •
  --   over that set, as well as a distinguished element of M called ε.  • is commutative and
  --   associative and ε forms a left and right identity for •.
  --
  --   A group ⟨M, •, ε, inv⟩ consists of a set M coupled with a binary operation • over that
  --   set as well as a distinguished element of M called ε, and a unary operation inv over M.
  --   • is associative, ε forms a left and right identity for •, and for every e ∈ M we have
  --   that inv e is the inverse of e.
  --
  -- As can be seen above, monoid sits in the middle of a rather complex hierarchy.  There are
  -- other structures not mentioned that sit both below monoid in the hierarchy (e.g. semigroup),
  -- as well as above (e.g. ring, commutative group, and so forth).  We wish to design a
  -- hierarchy in Agda that captures these notions, as well as satisfies the following
  -- properties:
  --
  --   1. If I have access to a Monoid structure, I should also be able to obtain a Magma
  --      structure immediately from this.  For every structure below Monoid in the hierarchy,
  --      a similar property should hold.
  --
  --   2. If I prove a property about a Monoid structure, this property should also be applicable
  --      to every other structure that sits above Monoid in the hierarchy (for instance
  --      commutative monoids, or groups).  For example, I should only need to prove that identity
  --      elements are unique once --- for monoids.  After that, I should `inherit' the same
  --      property for groups for free.
  --
  -- The rest of this exercise tutorial demonstrates how to do that…

  -- Common definitions will go here:

  BinOp : ∀ {ℓ} → Set ℓ → Set ℓ
  BinOp S = S → S → S

  IsAssociative : ∀ {ℓ} → {A : Set ℓ} → BinOp A → Set ℓ
  IsAssociative _•_ = ∀ e f g → e • (f • g) ≡ (e • f) • g

  IsCommutative : ∀ {ℓ} → {A : Set ℓ} → BinOp A → Set ℓ
  IsCommutative _•_ = ∀ e f → e • f ≡ f • e

  IsLeftIdentity : ∀ {ℓ} → {A : Set ℓ} → A → BinOp A → Set ℓ
  IsLeftIdentity ε _•_ = ∀ f → ε • f ≡ f

  IsLeftInverse : ∀ {ℓ} → {A : Set ℓ} → A → BinOp A → (A → A) → Set ℓ
  IsLeftInverse ε _•_ inv = ∀ f → inv f • f ≡ ε

  IsRightIdentity : ∀ {ℓ} → {A : Set ℓ} → A → BinOp A → Set ℓ
  IsRightIdentity ε _•_ = ∀ e → e • ε ≡ e

  IsRightInverse : ∀ {ℓ} → {A : Set ℓ} → A → BinOp A → (A → A) → Set ℓ
  IsRightInverse ε _•_ inv = ∀ e → e • inv e ≡ ε

  -- First, we will define the structure at the bottom of our hierarchy: Magma.  This is a very
  -- simple structure consisting of a carrier set and binary operation:

  record Magma {ℓ ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier : Set ℓ
      _•_     : BinOp Carrier

  record IsSemigroup {ℓ} {A : Set ℓ} (_•_ : BinOp A) : Set ℓ where
    field
      •-associative : IsAssociative _•_

  record Semigroup {ℓ ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier      : Set ℓ
      _•_          : BinOp Carrier
      is-semigroup : IsSemigroup _•_

    open IsSemigroup is-semigroup public

    magma : Magma {ℓ} {ℓ′}
    magma = record { Carrier = Carrier ; _•_ = _•_ }

  record IsMonoid {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) : Set ℓ where
    field
      ε-left-identity  : IsLeftIdentity ε _•_
      ε-right-identity : IsRightIdentity ε _•_
      is-semigroup     : IsSemigroup _•_

  record Monoid {ℓ ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier   : Set ℓ
      ε         : Carrier
      _•_       : BinOp Carrier
      is-monoid : IsMonoid ε _•_

    open IsMonoid is-monoid public

    semigroup : Semigroup {ℓ} {ℓ′}
    semigroup = record { Carrier = Carrier ; _•_ = _•_ ; is-semigroup = is-semigroup }

    open Semigroup semigroup using (magma) public

  -- This adds an element of type Magma to the Monoid record.  Typing
  --
  --   Monoid.magma mon
  --
  -- where `mon' is of type `Monoid' will now give you a magma structure.  As there's no opening of
  -- modules (the entirety of the Monoid record is in scope when you make the definition), it is much
  -- neater.
  --
  -- Let's continue with the hierarchy.  A commutative monoid is a monoid whose binary operation is
  -- associative and commutative:

  record IsCommutativeMonoid {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) : Set ℓ where
    field
      •-commutative : IsCommutative _•_
      is-monoid     : IsMonoid ε _•_

    open IsMonoid is-monoid public

  -- The `open IsMonoid is-monoid public' line ensures that the contents of IsMonoid is automatically
  -- imported into IsCommutativeMonoid --- we have not just proofs of commutativity, but also associativity
  -- and neutrality.

  record CommutativeMonoid {ℓ ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier               : Set ℓ
      ε                     : Carrier
      _•_                   : BinOp Carrier
      is-commutative-monoid : IsCommutativeMonoid ε _•_

    -- Make the proofs accessible in this record

    open IsCommutativeMonoid is-commutative-monoid public

    -- Again, we project down, forgetting about commutativity to obtain a monoid:

    monoid : Monoid {ℓ} {ℓ′}
    monoid = record { Carrier = Carrier ; ε = ε ; _•_ = _•_ ; is-monoid = is-monoid }

    open Monoid monoid using (magma; semigroup) public

  -- Let's now extend monoid in a different direction, by adding inverse elements to form groups:

  record IsGroup {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) (inv : A → A) : Set ℓ where
    field
      inv-left-inverse  : IsLeftInverse ε _•_ inv
      inv-right-inverse : IsRightInverse ε _•_ inv
      is-monoid         : IsMonoid ε _•_

    -- Make the monoid proofs available in this record:

    open IsMonoid is-monoid public

  record Group {ℓ ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier  : Set ℓ
      ε        : Carrier
      _•_      : BinOp Carrier
      inv      : Carrier → Carrier
      is-group : IsGroup ε _•_ inv

    -- Make the proofs from IsGroup available in this record:

    open IsGroup is-group public

    -- And project down:

    monoid : Monoid {ℓ} {ℓ′}
    monoid = record { Carrier = Carrier ; ε = ε ; _•_ = _•_ ; is-monoid = is-monoid }

    open Monoid monoid using (magma; semigroup) public

  -- Now our hierarchy looks like this:
  --
  --                    Magma
  --                      |
  --                      |
  --                      |
  --                    Monoid
  --                      /\
  --                     /  \
  --                    /    \
  --                   /      \
  --                  /        \
  --                 /          \
  --       Commutative Monoid  Group
  --
  -- We can close the divergence with a commutative group --- a group whose binary operation • is
  -- commutative:

  record IsCommutativeGroup {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) (inv : A → A) : Set ℓ where
    field
      •-commutative : IsCommutative _•_
      is-group      : IsGroup ε _•_ inv

    -- Make the group proofs available in this record:

    open IsGroup is-group public

  record CommutativeGroup {ℓ ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier               : Set ℓ
      ε                     : Carrier
      _•_                   : BinOp Carrier
      inv                   : Carrier → Carrier
      is-commutative-group  : IsCommutativeGroup ε _•_ inv

    -- Make the proofs from IsGroup available in this record:

    open IsCommutativeGroup is-commutative-group public

    -- And project down again, though note now there are two ways we can go back down the hierarchy!
    -- In particular: in IsCommutativeGroup we extended an IsGroup record to an IsCommutativeGroup record via
    -- the addition of •-commutative.  It will therefore be easier to project down to Group, rather than say
    -- CommutativeMonoid, as we will have no is-commutative-monoid value available.  If we had instead
    -- extended the IsCommutativeRecord with proofs about the existence of inverses, we'd have faced the opposite
    -- problem, having an easier time projecting down to CommutativeMonoid as opposed to Group:

    group : Group {ℓ} {ℓ′}
    group = record { Carrier = Carrier ; ε = ε ; _•_ = _•_ ; inv = inv ; is-group = is-group }

    open Group group using (magma; semigroup; monoid) public

    -- Note the double expansion below:

    commutativeMonoid : CommutativeMonoid {ℓ} {ℓ′}
    commutativeMonoid = record { Carrier = Carrier ; ε = ε ; _•_ = _•_ ; is-commutative-monoid = record { •-commutative = •-commutative ; is-monoid = is-monoid } }

  -- Let's give some instances:

  +-associative : IsAssociative _+_
  +-associative zero    n o = refl
  +-associative (suc m) n o = cong suc (+-associative m n o)

  zero-+ : IsRightIdentity zero _+_
  zero-+ zero    = refl
  zero-+ (suc m) = cong suc (zero-+ m)

  suc-+ : ∀ m n → suc (m + n) ≡ m + suc n
  suc-+ zero    n = refl
  suc-+ (suc m) n = cong suc (suc-+ m n)

  +-commutative : IsCommutative _+_
  +-commutative zero    n
    rewrite zero-+ n = refl
  +-commutative (suc m) n
    rewrite +-commutative m n = suc-+ n m

  +-commutative-monoid : CommutativeMonoid {ℓzero} {ℓzero}
  +-commutative-monoid =
    record {
      Carrier = ℕ ;
      ε = zero ;
      _•_ = _+_ ;
      is-commutative-monoid = record {
        •-commutative = +-commutative ;
        is-monoid = record {
          ε-left-identity = λ f → refl ;
          ε-right-identity = zero-+ ;
          is-semigroup = record {
            •-associative = +-associative
          }
        }
      }
    }

  -- Now, let's use some of these structures!  From the definition of a monoid, we have enough information to show that
  -- identity elements are unique:

  module AssumesMonoid {ℓ ℓ′} (mon : Monoid {ℓ} {ℓ′}) where

    open Monoid mon

    -- Interestingly we only need to know that the imposter identity is a left (or right) identity.  We use the opposite
    -- property for the `real' identity element to obtain the result:

    ε-is-unique : ∀ ε′ → IsLeftIdentity ε′ _•_  → ε ≡ ε′
    ε-is-unique ε′ lft = trans (sym (lft ε)) (ε-right-identity ε′)

    -- And of course we can redefine fold and friends:

    fold : List Carrier → Carrier
    fold []       = ε
    fold (x ∷ xs) = x • fold xs

    exp : Carrier → ℕ → Carrier
    exp b zero    = ε
    exp b (suc m) = b • exp b m

  -- Let's use them with our commutative monoid:

  open AssumesMonoid (CommutativeMonoid.monoid +-commutative-monoid) public

  foo : _
  foo = ε-is-unique zero -- works on commutative monoids despite being defined on monoids

  -- Can use numerals for elements of ℕ via some syntactic sugar that Data.Nat provides:
  goo : _
  goo = fold (1 ∷ 2 ∷ []) -- works on commutative monoids despite being defined on monoids

  hoo : _
  hoo = exp 1 5 -- works on commutative monoids despite being defined on monoids

  -- Etc. etc.
  --
  -- EXERCISE:
  --
  -- A semigroup is a structure ⟨M, •⟩ where • is an associative binary operation.
  --
  -- An element `e' is idempotent when e • e ≡ e.
  --
  -- Extend the hierarchy defined above in two ways: first add a semigroup structure above Magma
  -- but below Monoid, changing the types of the rest of the hierarchy as is necessary for this to work.
  -- Second: add the following structures: IdempotentMonoid, IdempotentGroup and
  -- CommutativeIdempotentGroup again changing whatever is necessary to get this to work.

  IsIdempotent : ∀ {ℓ} {A : Set ℓ} → BinOp A → Set ℓ
  IsIdempotent _•_ = ∀ a → a • a ≡ a

  record IsIdempotentMonoid {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) : Set ℓ where
    field
      •-idempotent : IsIdempotent _•_
      is-monoid    : IsMonoid ε _•_

    open IsMonoid is-monoid public

  record IdempotentMonoid {ℓ} {ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier              : Set ℓ
      ε                    : Carrier
      _•_                  : BinOp Carrier
      is-idempotent-monoid : IsIdempotentMonoid ε _•_

    open IsIdempotentMonoid is-idempotent-monoid public

    monoid : Monoid {ℓ} {ℓ′}
    monoid = record { Carrier = Carrier ; ε = ε ; _•_ = _•_ ; is-monoid = is-monoid }

    open Monoid monoid using (magma; semigroup) public

  record IsIdempotentGroup {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) (inv : A → A) : Set ℓ where
    field
      •-idempotent : IsIdempotent _•_
      is-group     : IsGroup ε _•_ inv

    open IsGroup is-group public

  record IdempotentGroup {ℓ} {ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier             : Set ℓ
      ε                   : Carrier
      _•_                 : BinOp Carrier
      inv                 : Carrier → Carrier
      is-idempotent-group : IsIdempotentGroup ε _•_ inv

    open IsIdempotentGroup is-idempotent-group public

    group : Group {ℓ} {ℓ′}
    group = record { Carrier = Carrier ; ε = ε ; _•_ = _•_ ; inv = inv ; is-group = is-group }

    open Group group using (magma; semigroup; monoid) public

    idempotentMonoid : IdempotentMonoid {ℓ} {ℓ′}
    idempotentMonoid = record { Carrier = Carrier ; ε = ε ; _•_ = _•_ ; is-idempotent-monoid = record { •-idempotent = •-idempotent ; is-monoid = is-monoid } }

  record IsCommutativeIdempotentGroup {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) (inv : A → A) : Set ℓ where
    field
      •-idempotent         : IsIdempotent _•_
      is-commutative-group : IsCommutativeGroup ε _•_ inv

    open IsCommutativeGroup is-commutative-group public

  record CommutativeIdempotentGroup {ℓ} {ℓ′} : Set (ℓsuc (ℓ ℓ⊔ ℓ′)) where
    field
      Carrier                         : Set ℓ
      ε                               : Carrier
      _•_                             : BinOp Carrier
      inv                             : Carrier → Carrier
      is-commutative-idempotent-group : IsCommutativeIdempotentGroup ε _•_ inv

    open IsCommutativeIdempotentGroup is-commutative-idempotent-group public

    commutativeGroup : CommutativeGroup {ℓ} {ℓ′}
    commutativeGroup = record
                         { Carrier = Carrier
                         ; ε = ε
                         ; _•_ = _•_
                         ; inv = inv
                         ; is-commutative-group = is-commutative-group
                         }

    open CommutativeGroup commutativeGroup using (magma; semigroup; monoid; group; commutativeMonoid)

    idempotentGroup : IdempotentGroup {ℓ} {ℓ′}
    idempotentGroup = record
                        { Carrier = Carrier
                        ; ε = ε
                        ; _•_ = _•_
                        ; inv = inv
                        ; is-idempotent-group = record { •-idempotent = •-idempotent ; is-group = is-group }
                        }

    open IdempotentGroup idempotentGroup using (idempotentMonoid) public
