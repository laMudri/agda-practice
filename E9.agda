-- First steps in Agda: records, and expressing algebraic structures

module E9 where

  open import Level

  open import Relation.Binary.PropositionalEquality

  -- Consider the last exercise.  We showed that both _*_ and _+_ were commutative.
  -- Each time, we wrote out by hand either (m n : ℕ) → m * n ≡ n * m or
  -- (m n : ℕ) → m + n ≡ n + m.  But both of these types are similar, and only differ
  -- in the particular function being considered.  Can we abstract these using a function
  -- that returns a type?  Yes:

  IsCommutative : {ℓ : Level} → {A : Set ℓ} → (A → A → A) → Set ℓ
  IsCommutative {ℓ} {A} _•_ = (x y : A) → x • y ≡ y • x

  -- The syntax {ℓ} {A} allows us to refer explicitly to a type that has been marked implicit.
  --
  -- We can now use IsCommutative, as before:

  open import Data.Nat
    hiding (fold)

  +-commutative : IsCommutative _+_
  +-commutative zero    n = {!!}
  +-commutative (suc m) n = {!!}

  *-commutative : IsCommutative _*_
  *-commutative zero    n = {!!}
  *-commutative (suc m) n = {!!}

  -- Much nicer, and this ensures that all lemmas that state the commutativity of some function
  -- are stated in exactly the same way.

  -- Onward.  Let's introduce records and show how they can be used to capture `structured sets'
  -- from mathematics like algebraic structures (monoids, rings, groups, etc.) as well as ordered
  -- structures (lattices, partial orders, etc.)

  -- Here is a record:

  record 𝟙 : Set where
    constructor
      it

  -- It's the familiar 𝟙 type from the first 5 exercises.  We have provided a way to construct the
  -- record via the `constructor' keyword, and an explicit constructor name.
  --
  -- We can use records like any other bit of data:

  silly-example₁ : {A : Set} → A → (𝟙 → A)
  silly-example₁ e = λ x → e

  silly-example₂ : {A : Set} → (𝟙 → A) → A
  silly-example₂ f = f it

  -- Records may also have fields.  Here's the dependent-pair type (Σ-type) expressed as a record:

  record Σ {ℓ : Level} (A : Set ℓ) (P : A → Set ℓ) : Set ℓ where
    constructor
      _,_
    field
      fst : A
      snd : P fst

  -- Note how the types of later fields may depend on earlier fields.  Here snd has type `P fst',
  -- where `fst' itself is a field that appeared in the record prior to `snd'.  Using this style of
  -- definition for Σ-types we need not explicitly define the `fst' and `snd' projection functions
  -- separately --- we can define them as part of the type itself.
  --
  -- Naturally, the definition of Σ above satisfies the same properties as our old definition:

  _×_ : Set → Set → Set
  A × B = Σ A (λ x → B)

  curry-example : (A B C : Set) → (A → B → C) → A × B → C
  curry-example A B C f A×B = f (Σ.fst A×B) (Σ.snd A×B)

  -- Here we use the _,_ constructor of Σ to make a dependent pair type:
  uncurry-example : (A B C : Set) → (A × B → C) → A → B → C
  uncurry-example A B C f a b = f (a , b)

  -- You'll note that `fst' and `snd' are namespaced --- we have to refer to them using a hierarchical
  -- identifier, using Σ.fst and Σ.snd instead of fst and snd as we did before.  We can change that by
  -- opening the record as soon as we have defined it:

  open Σ public

  -- Now `fst' and `snd' are available as top-level identifiers:

  foo : _
  foo = fst

  -- And all is well again.
  --
  -- Records need not have explicit constructors.  The following record captures the notion of a point
  -- in ℕ³:

  record Point : Set where
    field
      x y z : ℕ

  -- We can construct such a record as follows:

  origin : Point
  origin = record { x = ℕ.zero ; y = ℕ.zero ; z = ℕ.zero }

  -- Here zero is qualified as the Level module also exports a constant called zero, and Agda complains about
  -- name clashes.
  --
  -- Records with constructors can also be constructed using the above syntax, by the way.  Using the refine
  -- key combination (<Ctrl> + <c> + <r>) in a hole with record type will automatically introduce the above
  -- expansion.  EXERCISE: Try it yourself:

  one-one-one : Point
  one-one-one = record { x = 1 ; y = 1 ; z = 1 }

  -- So, what are records?  Records are Σ-types that are built in to the Agda language itself, albeit with
  -- one key difference, namely the entries are given an explicit name that we can refer to, rather than a
  -- position.  A record of the form:

  record NotZero : Set where
    constructor
      mkNotZero
    field
      • : ℕ
      •-not-zero : • ≢ ℕ.zero
  
  -- Is translated into something akin to:

  NotZero′ : Set
  NotZero′ = Σ ℕ (λ x → x ≢ ℕ.zero)

  mkNotZero′ : (• : ℕ) → • ≢ ℕ.zero → NotZero′
  mkNotZero′ • •-not-zero = • , •-not-zero

  -- inside Agda.  If you have more fields in a record, then Agda will automatically nest the Σ-types.  Fields
  -- then refer to positions within this `telescope' of nested Σ's.  There are other slight differences between
  -- record declarations and data declarations relating to type-checking and reduction that are not
  -- important and we will not discuss here.
  --
  -- Records are for `bundling' up pieces of related data.  Some of this data, as we have seen in the case of
  -- NotZero above, can be proofs relating to other pieces of data in a record.  In Agda, one of the main uses of
  -- records are for modelling structured sets, such as monoids, groups, rings, lattices, partial orders, and
  -- so on.
  --
  -- Recall that a monoid ⟨M, •, ε⟩ is a tuple consisting of a set M, a binary operation on M called •, and a
  -- left- and right- identity for • called ε.  This tuple is accompanied by a series of laws that it must satisfy
  -- in order to be a monoid, namely:
  --
  --                           ε ∈ M
  --   ∀e ∈ M. ∀f ∈ M.         e • f ∈ M,                 (CLOSURE OF •)
  --   ∀e ∈ M. ∀f ∈ M. ∀g ∈ M. e • (f • g) = (e • f) • g  (ASSOCIATIVITY)
  --   ∀e ∈ M.                 e • ε = ε • e = e          (IDENTITY)
  --
  -- From the first two laws we get automatically that e • (f • g), (e • f) • g, e • ε and ε • e are all in M.
  --
  -- The question arises: how can we best model this in Agda?  We can use a record, like so:

  record Monoid₁ : Set₁ where
    field
      Carrier       : Set
      _•_           : Carrier → Carrier → Carrier
      ε             : Carrier
      ε-identityₗ   : (f : Carrier) → ε • f ≡ f
      ε-identityᵣ   : (e : Carrier) → e • ε ≡ e
      •-associative : (e f g : Carrier) → e • (f • g) ≡ (e • f) • g

  -- Note here that we have explicitly named the carrier set M from ⟨M, •, ε⟩ above as Carrier.  Note also that
  -- as Carrier is of type Set, the entire record must be in a larger universe, Set₁, to be able to contain it.
  --
  -- Now, recalling all of our previous discussion, we can start to make this definition more sophisticated.
  -- First, let's deal with the issue of universe levels:

  record Monoid₂ {ℓ ℓ′ : Level} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
    field
      Carrier       : Set ℓ
      _•_           : Carrier → Carrier → Carrier
      ε             : Carrier
      ε-identityₗ   : (f : Carrier) → ε • f ≡ f
      ε-identityᵣ   : (e : Carrier) → e • ε ≡ e
      •-associative : (e f g : Carrier) → e • (f • g) ≡ (e • f) • g

  -- You'll note that there's no name clashes here with fields previously declared in Monoid₁ because we didn't
  -- open the Monoid₁ record using `open Monoid₁ public', therefore all fields are still qualified.
  --
  -- Here, we've done a little trick with the universe levels: ℓ is the universe that Monoid₂.Carrier sits in.
  -- However, we may want Carrier to remain in Set ℓ, for some reason, but the entire Monoid₂ record to be
  -- lifted into Set (suc (suc ℓ)).  To allow this, we parameterise Monoid₂ by two levels and tell Agda to
  -- automatically try to infer them.  We then have Monoid₂ reside in `suc (ℓ ⊔ ℓ′)' which both guarantees that
  -- Monoid₂ resides in a universe level at least one above that of Carrier (the `suc' part) and can move
  -- up the universe hierarchy freely as required (the max, `_⊔_' part).
  --
  -- Let's make Monoid₂ even more sophisticated.  The notion of binary operation on a type seems like a common
  -- notion for algebraic structures.  Let's abstract that:

  BinOp : ∀ {ℓ} → Set ℓ → Set ℓ
  BinOp S = S → S → S

  record Monoid₃ {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
    field
      Carrier       : Set ℓ
      _•_           : BinOp Carrier
      ε             : Carrier
      ε-identityₗ   : (f : Carrier) → ε • f ≡ f
      ε-identityᵣ   : (e : Carrier) → e • ε ≡ e
      •-associative : (e f g : Carrier) → e • (f • g) ≡ (e • f) • g

  -- We've now abstracted the notion of binary operation out into its own definition, BinOp.  You may notice two
  -- things about this definition and the Monoid₃ record.  The first is the type of BinOp.  Instead of
  --
  --    {ℓ : Level} → Set ℓ → Set ℓ
  --
  -- I have used:
  --
  --    ∀ {ℓ} → Set ℓ → Set ℓ
  --
  -- Which are equivalent, when Agda can work out what the type of ℓ is (it can't always, in which case you will
  -- get canary yellow highlighting everywhere).  Clearly ℓ must be of type Level, Agda can infer this, and therefore
  -- we can use the ∀ {ℓ} → … syntax instead.
  --
  -- The types
  --
  --     (ℓ : Level) → Set ℓ → Set ℓ
  --
  -- and
  --
  --     ∀ ℓ → Set ℓ → Set ℓ
  --
  -- are equivalent too.  Notice the use of braces `{' and `}' in the first pair of types to indicate the type should
  -- be inferred, and the lack of them in the second pair, indicating that the type will be given explicitly by the
  -- programmer.  Keep in mind that in
  --
  --     ∀ {ℓ} → Set ℓ → Set ℓ
  --
  -- Agda is being asked to infer *two* things.  First, right now, Agda is being asked to infer that ℓ is of type Level
  -- from how ℓ is used in the type signature --- this is the `∀' part.  Second, later, when BinOp is used, Agda is
  -- being asked to infer the universe level ℓ itself from the surrounding context of `BinOps' usage.  This is the
  -- `{' and `}' part.
  --
  -- You'll see a similar pattern in the header of Monoid₃.  Instead of using the syntax
  --
  --     record Monoid₃ {ℓ ℓ′ : Level} : Set … where
  --
  -- I have used instead
  --
  --     record Monoid₃ {ℓ ℓ′} : Set … where
  --
  -- which has a similar effect on Agda as the use of `∀ {…} → …' discussed above.
  --
  -- These features are used to reduce the complexity of type signatures and reduce the burden on the programmer
  -- when writing them.  You'll see them being used regularly in `real' Agda code.
  --
  -- Let's press on: the definitions of identity (both left and right) and associativity look like they will be useful
  -- elsewhere, too, perhaps when defining other algebraic structures, later on.  Let's abstract those, too:

  IsLeftIdentity : ∀ {ℓ} → {A : Set ℓ} → A → BinOp A → Set ℓ
  IsLeftIdentity {ℓ} {A} ε _•_ = (f : A) → ε • f ≡ f

  IsRightIdentity : ∀ {ℓ} → {A : Set ℓ} → A → BinOp A → Set ℓ
  IsRightIdentity {ℓ} {A} ε _•_ = (e : A) → e • ε ≡ e

  IsAssociative : ∀ {ℓ} → {A : Set ℓ} → BinOp A → Set ℓ
  IsAssociative {ℓ} {A} _•_ = (e f g : A) → e • (f • g) ≡ (e • f) • g

  record Monoid₄ {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
    field
      Carrier       : Set ℓ
      _•_           : BinOp Carrier
      ε             : Carrier
      ε-identityₗ   : IsLeftIdentity ε _•_
      ε-identityᵣ   : IsRightIdentity ε _•_
      •-associative : IsAssociative _•_

  -- Looking better.  But what if we want to write a function where we are given some _•_ and ε and wish to assume
  -- that these functions form a monoid structure on some type without having to explicitly package them up with a
  -- Carrier type in a Monoid record?  The answer is to split the Monoid₄ record into two: one that captures the
  -- laws that binary operations on, and elements of, Carrier must satisfy to form a monoid, and the other that
  -- bundles Carrier up with _•_ and ε, like so:

  record IsMonoid {ℓ} {A : Set ℓ} (ε : A) (_•_ : BinOp A) : Set ℓ where
    field
      ε-identityₗ   : IsLeftIdentity ε _•_
      ε-identityᵣ   : IsRightIdentity ε _•_
      •-associative : IsAssociative _•_

  record Monoid₅ {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
    field
      Carrier   : Set ℓ
      _•_       : BinOp Carrier
      ε         : Carrier
      is-monoid : IsMonoid ε _•_

  -- All that is left to do now is to open `is-monoid' within the Monoid record itself so that we have access to
  -- the proofs that it contains within that record:

  record Monoid {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
    field
      Carrier   : Set ℓ
      _•_       : BinOp Carrier
      ε         : Carrier
      is-monoid : IsMonoid ε _•_

    open IsMonoid is-monoid public

  -- Note the indentation here.  The `open IsMonoid is-monoid public' is still within the body of the Monoid
  -- record declaration.  It is not a top level declaration like:

  -- open Monoid public
  --
  -- (commented to avoid name clashes below)

  -- That brings the contents of the Monoid record into scope for all code following that declaration!
  --
  -- Let's now try to use the Monoid record.  First we will provide some proof that the Monoid record actually
  -- has captured something useful (i.e. it is not describing something that doesn't exist) by demonstrating
  -- that ⟨ℕ, _+_, 0⟩ is a monoid:

  -- EXERCISE: complete the following:

  zero-+-IsLeftIdentity : IsLeftIdentity ℕ.zero _+_
  zero-+-IsLeftIdentity f = refl

  zero-+-IsRightIdentity : IsRightIdentity ℕ.zero _+_
  zero-+-IsRightIdentity ℕ.zero = refl
  zero-+-IsRightIdentity (ℕ.suc e) = cong ℕ.suc (zero-+-IsRightIdentity e)

  +-IsAssociative : IsAssociative _+_
  +-IsAssociative ℕ.zero f g = refl
  +-IsAssociative (ℕ.suc e) f g = cong ℕ.suc (+-IsAssociative e f g)

  ℕ-zero-+-IsMonoid : IsMonoid ℕ.zero _+_
  ℕ-zero-+-IsMonoid = record { ε-identityₗ = zero-+-IsLeftIdentity ; ε-identityᵣ = zero-+-IsRightIdentity ; •-associative = +-IsAssociative }

  ℕ-zero-+-Monoid : ∀ {ℓ′} → Monoid {ℓ′ = ℓ′}
  ℕ-zero-+-Monoid = record { Carrier = ℕ ; _•_ = _+_ ; ε = ℕ.zero ; is-monoid = ℕ-zero-+-IsMonoid }

  -- Great, so we now know that there exists at least one inhabitant of the Monoid type (in fact, List along with _++_ and []
  -- also form a monoid, as does ℕ along with _*_ and 1, and perhaps you'd like to demonstrate that fact by creating two
  -- more inhabitants of Monoid below), what can we do with it?

  one-*-IsLeftIdentity : IsLeftIdentity (ℕ.suc ℕ.zero) _*_
  one-*-IsLeftIdentity f = zero-+-IsRightIdentity f

  one-*-IsRightIdentity : IsRightIdentity (ℕ.suc ℕ.zero) _*_
  one-*-IsRightIdentity ℕ.zero = refl
  one-*-IsRightIdentity (ℕ.suc e) = cong ℕ.suc (one-*-IsRightIdentity e)

  +-*-distrib : ∀ x y z → (x + y) * z ≡ x * z + y * z
  +-*-distrib ℕ.zero y z = refl
  +-*-distrib (ℕ.suc x) y z rewrite sym (+-IsAssociative z (x * z) (y * z)) =
    cong (_+_ z) (+-*-distrib x y z)

  *-IsAssociative : IsAssociative _*_
  *-IsAssociative ℕ.zero f g = refl
  *-IsAssociative (ℕ.suc e) f g
    rewrite +-*-distrib f (e * f) g
          | *-IsAssociative e f g = refl

  ℕ-one-*-IsMonoid : IsMonoid (ℕ.suc ℕ.zero) _*_
  ℕ-one-*-IsMonoid = record { ε-identityₗ = one-*-IsLeftIdentity
                            ; ε-identityᵣ = one-*-IsRightIdentity
                            ; •-associative = *-IsAssociative
                            }

  ℕ-one-*-Monoid : ∀ {ℓ′} → Monoid {ℓ′ = ℓ′}
  ℕ-one-*-Monoid = record { Carrier = ℕ
                          ; _•_ = _*_
                          ; ε = ℕ.suc ℕ.zero
                          ; is-monoid = ℕ-one-*-IsMonoid
                          }

  -- Recall (or perhaps, be made aware), that we can make some very general definitions using monoids.  We can interpret
  -- _•_ as being a multiplication, and define a general version of exponentiation, that works for all monoids.  Similarly,
  -- we could interpret _•_ as some accumulation function and derive a general notion of fold over lists, that works for
  -- all monoids.  Let's do that now using another familiar Agda feature: nested parameterised modules:

  -- We'll need this below:
  open import Data.List

  module AssumesMonoid {ℓ ℓ′} (monoid : Monoid {ℓ} {ℓ′}) where

    -- This lets us refer to `monoid's contents without having to qualify everything through the entirety of this
    -- nested module:
    open Monoid monoid public

    -- Let's define a general monoidal fold, first:

    fold : List Carrier → Carrier
    fold []       = ε
    fold (x ∷ xs) = x • fold xs

    -- Let's show some properties of this function…
    -- EXERCISE: complete the following:

    ++-fold : ∀ xs ys → fold (xs ++ ys) ≡ fold xs • fold ys
    ++-fold [] ys = sym (ε-identityₗ _)
    ++-fold (x ∷ xs) ys rewrite ++-fold xs ys =
      •-associative x (fold xs) (fold ys)

    -- Remember, you have access to all of the proofs such as ε-identityᵣ…

    -- Now, let's define a general exponentiation function:

    exp : Carrier → ℕ → Carrier
    exp e zero    = ε
    exp e (suc m) = e • exp e m

    -- And show some properties of that…
    -- EXERCISE: complete the following:

    exp-+ : ∀ e m n → exp e (m + n) ≡ exp e m • exp e n
    exp-+ e ℕ.zero n = sym (ε-identityₗ _)
    exp-+ e (ℕ.suc m) n rewrite exp-+ e m n = •-associative e _ _

    ε-exp : ∀ m → exp ε m ≡ ε
    ε-exp ℕ.zero = refl
    ε-exp (ℕ.suc m) rewrite ε-identityₗ (exp ε m) = ε-exp m

    -- Perhaps there's some other properties you can spot about these functions and prove.  Most of the
    -- laws of exponents hold, in a more general form, for the `exp' function, though one, interestingly, requires
    -- commutativity of _•_, which isn't true in general for plain monoids.  We'll discuss this in the next
    -- exercise.

    exp-one : ∀ e → exp e 1 ≡ e
    exp-one e = ε-identityᵣ e

  -- Let's test our general folds and exponentiation:

  open AssumesMonoid {Level.zero} {Level.zero} ℕ-zero-+-Monoid public
  -- We provided explicit universe levels to stop the annoying yellow highlighting!

  fold-test : _
  fold-test = {!fold (ℕ.zero ∷ ℕ.suc ℕ.zero ∷ ℕ.suc (ℕ.suc ℕ.zero) ∷ [])!}

  -- Normalise the above with <Ctrl> + <c> + <n> --- what happens?  How about:

  exp-test : _
  exp-test = {!exp (ℕ.suc (ℕ.suc ℕ.zero)) (ℕ.suc (ℕ.suc ℕ.zero))!}

  -- Normalise the above with <Ctrl> + <c> + <n> --- what happens?

  -- These functions now work on *any* monoid.  We just need to open the AssumesMonoid module with a concrete
  -- implementation of a monoid to get fold and exponentiation functions that are tailored specifically to that
  -- monoid.  For the ⟨ℕ, +, 0⟩ monoid that we provided above, fold is the equivalent of summing a list of natural
  -- numbers, whilst exponentiation is the equivalent of summing a given number a certain number of times.  If you
  -- provided a concrete implementation of the ⟨List, _++_, []⟩ monoid, as suggested above, then fold is akin to
  -- concatenating a list of lists (i.e. it is the familiar `flatten' operation on lists), whilst exp is akin to
  -- appending a list to itself a given number of times (i.e. replicating a list n-times).
