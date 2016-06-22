-- First steps with Agda: propositional equality.

module E3 where

  -- In Exercise1 and Exercise2 we have defined types and functions that, with minor
  -- changes, could have easily been defined in Haskell or Standard ML.  In particular
  -- we now have a clutch of simple types and potentially recursive functions over
  -- those types that satisfy certain properties, but we have no way to demonstrate
  -- that those properties do in fact hold.  This is leaving one of the key benefits of
  -- dependently typed languages like Agda by the wayside: namely the ability to not only
  -- define functions, but prove properties about them.
  --
  -- For example, we have a definition of addition on natural numbers from Exercise2.
  -- Addition on the naturals is known to satisfy many properties, amongst them commutativity.
  -- We wish to establish that m + n gives the same result as n + m, for any m and n.
  --
  -- However, to do this, we need some notion of equality that we do not yet have.  We will
  -- define propositional equality in this exercise, and show that some useful properties
  -- hold.

  -- Propositional equality looks complicated, but really isn't:

  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  -- Type \equiv to obtain the equivalence ≡ Unicode glyph.
  --
  -- First, note that equality _≡_ is a data type just like ℕ, Bool or List.  There is nothing
  -- particularly special about _≡_'s definition, but it does demonstrate some interesting
  -- features of Agda (it has a more complex type than previously mentioned types).  Note also
  -- that it has a single constructor that states every element of A is equal to itself.
  --
  -- We can pattern match on refl to reveal information to the type system.  For example, in
  -- the following series of definition, watch how the proof state evolves:

  sym₁ : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym₁ refl = refl

  -- Use <Ctrl> + <c> + <,> to inspect the proof state above and compare it with the proof state
  -- below:

  sym₂ : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym₂ refl = refl

  -- Note how Agda now knows that x and y are the same thing by pattern matching on x≡y and
  -- obtaining refl.  We can of course complete the definition of sym by using refl again,
  -- as we have a goal .x ≡ .x which is of course refl's type for any x.  Automation should
  -- also close this automatically:

  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  -- We have established that _≡_ is reflexive, symmetric (above) and now transitive:

  trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl y≡z = y≡z

  -- (Do the same trick as above, replacing refl with pattern variables in the arguments, or the
  -- body with a hole, to see how the types evolve).

  -- So far, so good.  _≡_ is reflexive, transitive and symmetric, i.e. an equivalence relation.
  -- However, what makes _≡_ really useful is that it's an equality, i.e. can be used to replace
  -- like-for-like elements in a given context:

  subst : {A : Set} → {x y : A} → (P : A → Set) → x ≡ y → P x → P y
  subst P refl Px = Px

  -- (Complete the definition of subst...)

  -- subst states that, given some predicate P uses x somehow, if we know x and y are equal, then
  -- P could use y instead.

  -- We will also need one more property of _≡_, which describes how functions behave when applied
  -- to equal elements:

  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- (Complete the definition of cong...)

  -- i.e. cong states that functions should not be able to distinguish between elements that we have
  -- established are equal.

  -- These are all the properties we need for the time being.
