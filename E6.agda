-- First steps in Agda: universe levels and floating definitions.

module E6 where

  -- We will now start working towards writing more idiomatic Agda code.  In the next
  -- few exercises, we will abandon our definitions from exercises 1-5 in favour of the
  -- definitions that Agda provides in its standard library.  These definitions have now
  -- served their purpose in demonstrating how various concepts can be capture in type
  -- theory, and we will therefore move to standard definitions of the same concepts.
  --
  -- First, however, we must discuss universe levels.

  -- Recall how we previously described `Set'.  `Set' is a synonym for Set₀, the type of
  -- small types.  A type of types is also called a `universe' in the type theory community.
  -- All of the types that we have talked about so far have been `small', in that they can
  -- fit inside Set₀.  For instance, Bool, ℕ, 𝟘, 𝟙 and so forth all reside in Set₀.  But
  -- what about a type such as Set₀ → Set₀?  Where should something like that reside?
  --
  -- One potential answer to this question is that Set₀ itself should have type Set₀.  This
  -- seems perfectly reasonable at first, but we quickly run into problems, and in fact any
  -- sufficiently powerful type system that has Set₀ : Set₀, or similar, is in fact inconsistent,
  -- via Girard's paradox.  The type of all small types is in fact `too big' to be a small type
  -- itself, and so therefore is a type like Set₀ → Set₀.  So we must introduce Set₁, where
  -- types like Set₀ → Set₀ reside.  But then what is the type of Set₁ → Set₁?  Set₂ of
  -- course!  But what is the type of Set₂ → Set₂?  Err, Set₃, and so on and so forth to
  -- infinity, where each Setᵢ resides in Setⱼ where j = i + 1.
  --
  -- But, now we have a problem.  Recall the definition of the identity combinator:

  id₁ : (A : Set) → A → A
  id₁ A x = x

  -- This is a polymorphic function, but the polymorphism involved is now looking much less
  -- liberal than it did initially.  Rather than being able to use id₁ at any type, we can
  -- now only use id₁ at small types, such as Bool.  Whereas `id₁ Bool true' is perfectly
  -- fine, `id₂ (Set₀ → Set₀) (λ x → x)' isn't, as we have restricted our id₁ function to
  -- `small types'.
  --
  -- We can fix this by introducing a new combinator, as follows:

  id₂ : (A : Set₁) → A → A
  id₂ A x = x

  -- And it works as expected:

  id₂-test : Set₀ → Set₀
  id₂-test = id₂ (Set₀ → Set₀) (λ x → x)

  -- And all is well.  But do we really need to copy every definition like this?  In some
  -- similar systems to Agda, the answer is `yes', but Agda provides a way of working around
  -- this.
  --
  -- First, we'll note that the problem with id₁ and id₂ are that they are not polymorphic enough.
  -- Languages like Standard ML and Haskell removed the need to write a version of id at every
  -- type by introducing type polymorphism.  What, therefore, is needed here in Agda is a version
  -- of universe polymorphism so that we need not write a new version of every function for each
  -- universe.  Agda's method for achieving this is via explicit universe levels, which may be
  -- quantified over.
  --
  -- To see them in action, we first import the Level module from the Agda standard library:

  open import Level

  -- If you middle mouse-click on the module name above, emacs will automatically open the module
  -- and show you the contents.  You can see that there is not much in the module, just the
  -- importation of Agda.Primitive and a few other definitions.  Agda.Primitive itself postulates
  -- the existence of a Level type, as well as a few other operations.  There's not really much
  -- going on, as Level is a fairly primitive feature of Agda, and all the magic is hidden away
  -- inside Agda's internals.  The middle mouse-click trick works on any function or identifier
  -- in your files.  Clicking will immediately jump to the definition of the identifier you clicked
  -- on.
  --
  -- However, having opened Level, we can start quantifying over universe levels.  Here's more
  -- general type for id:

  id : {ℓ : Level} → (A : Set ℓ) → A → A
  id A x = x

  -- Type \ell to obtain the curly-L ℓ Unicode glyph.
  --
  -- Intuitively, the quantification over ℓ is allowing id to `float' up and down the universe
  -- hierarchy.  It is no longer fixed at one particular universe.  Naturally, functions aren't
  -- the only things that are permitted to float.  What about data types?  Let's introduce some
  -- data to play with:

  -- At a fixed level
  data 𝟙₀ : Set₀ where
    it₀ : 𝟙₀

  -- At another fixed level
  data 𝟙₁ : Set₁ where
    it₁ : 𝟙₁

  -- Floating
  data 𝟙 {ℓ : Level} : Set ℓ where
    it : 𝟙

  -- Let's test id with this data:

  id-test₁ : 𝟙₀
  id-test₁ = id 𝟙₀ it₀

  id-test₂ : 𝟙₁
  id-test₂ = id 𝟙₁ it₁

  id-test₃ : 𝟙
  id-test₃ = id 𝟙 it

  -- In the last test Agda cannot successfully infer the level of 𝟙.  Why?  Well, both 𝟙 and id are
  -- quantifying over levels, and therefore there is no concrete universe level to instantiate them
  -- at, unlike in the first two tests.  We must therefore help Agda out a little, as follow:

  id-test₄ : {ℓ : Level} → 𝟙 {ℓ}
  id-test₄ = id 𝟙 it

  -- Note that id-test₄ is itself `floating'.
  --
  -- We may now ask the following: for a fixed universe level ℓ, what is the type of Set ℓ?  Well,
  -- before the type of Setᵢ was Setⱼ where j = i + 1.  Similarly now, the type of Set ℓ is
  -- Set (suc ℓ), where suc is a primitive constant provided by the Level module, which `bumps' ℓ up
  -- one universe level.  But what happens if we need to merge two different universe levels?  Say,
  -- if we have a function that has two parameters that live in different universes, where should
  -- the result live?  Agda has a solution for this too, via _⊔_:

  sillyFunctionOnTypes : {ℓ ℓ′ : Level} → Set ℓ → Set ℓ′ → Set (suc (ℓ ⊔ ℓ′))
  sillyFunctionOnTypes A B = Lift B

  -- Type \sqcup to obtain the square union ⊔ Unicode glyph.

  -- _⊔_ takes the maximum of two universe levels.  Applying suc to this maximum level bumps us up
  -- one more level.  `sillyFunctionOnTypes' takes two types as parameters and returns another type.
  -- However, B is in the universe Set ℓ′, but we need it to be in the universe Set (suc (ℓ ⊔ ℓ′)).
  -- Agda does not do this lifting from one universe level to a higher universe level automatically,
  -- so we must use the Lift construct from the Level module to do it manually.  Using this, everything
  -- typechecks, and all is well.

  -- EXERCISE: define a `floating' variant of the disjoint union _⊎_ type.  Define a floating variant
  -- of its elimination procedure:
  --
  --     (A ⊎ B) → (A → C) → (B → C) → C
  --
  -- Make sure you use _⊔_ and succ to obtain the most general type possible.

  data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

  ⊎-elim :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
    A ⊎ B → (A → C) → (B → C) → C
  ⊎-elim (inj₁ a) f g = f a
  ⊎-elim (inj₂ b) f g = g b
