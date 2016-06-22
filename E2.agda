-- First steps with Agda.  Defining more complex types and functions over those
-- types by pattern matching.

module E2 where

  -- When you have completed Exercise1, uncomment this line.  If you like, try to
  -- uncomment the line before completing all the previous exercises.  Agda will
  -- complain about `unsolved metas', i.e. there's still bits of the Exercise1 file
  -- that you have not completely refined into complete types or terms.

  open import E1

  -- We start by defining a list type.  This should look entirely familiar.

  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  -- Type \:: to obtain the cons ∷ Unicode glyph.
  --
  -- Unlike the types we defined in E1, List is recursive.  Naturally, then, a lot of the
  -- functions in this file are also going to be recursive.  One thing that you must
  -- learn quite quickly is that Agda is very picky about recursive functions and
  -- recursive types: a type like List above must be `strictly positive', and any
  -- recursive function must be terminating.  This is to ensure the soundness of the
  -- logic --- without these restrictions we could inhabit 𝟘 from Exercise1, and then
  -- use ex-falso to prove anything that we want.
  --
  -- We will leave `strictly positive' undefined for now, but note that if we had changed
  -- the type of _∷_ to (List A → List A) → List A then this would fall foul of Agda's
  -- restriction.

  -- Let's write some simple functions:

  [_] : {A : Set} → A → List A
  [ e ] = e ∷ []

  -- This is the `singleton' list, i.e. the list containing only one element.  Note
  -- again how I have marked the {A : Set} → … as being inferrable like at the end
  -- of Exercise1.

  -- Let's write out first recursive function, something hopefully familiar.  Note I
  -- have refined the body of the x ∷ xs case to add a little more structure.
  --
  -- EXERCISE: complete the definition of map:

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  -- Agda has a small collection of rather limited automation tools compared to its more
  -- complex brethren like Coq.  However, these automated tools can be used to close
  -- simple goals like those appearing in the cons case of map above.  Let's try to
  -- use them:

  map′ : {A B : Set} → (A → B) → List A → List B
  map′ f []        = []
  map′ f (x ∷ xs) = f x ∷ map′ f xs

  -- Again, there are two holes in the body of the cons case of map′'s definition.  Put your
  -- cursor in the first and bring up the proof state with <Ctrl> + <c> + <,>.  You should
  -- see something akin to this:
  --
  -- Goal: List .B
  -- ----------------------------
  -- xs : List .A
  -- x : .A
  -- f : .A → .B
  -- .B : Set
  -- .A : Set
  --
  -- The dotted type variables indicate that these type variables are left implicit (inferrable).
  -- We have to construct something of type .B, but we have something of type .A (x) and something
  -- of type .A → .B.  Easy.  But why do this by hand?  With your cursor in the hole, press
  -- <Ctrl> + <c> + <a> to invoke Agda's automated proof search.  What happens?  Hopefully the
  -- hole is replaced by f x --- if not, something has gone wrong.  Agda should have successfully
  -- found a term of type .B.
  --
  -- Do the same in the second hole.  Hopefully Agda finds map′ f xs has type List .B and closes
  -- that hole too.
  --
  -- Note these are very simple goals and within the reach of Agda's automation.  On more complex
  -- goals, automation will struggle.  Note also: you must be very careful using automation.
  -- There's no guarantee that just because something has the correct type it's correct!

  -- We can stick two lists together to create a larger list with append:

  _⊕_ : {A : Set} → List A → List A → List A
  []       ⊕ ys = ys
  (x ∷ xs) ⊕ ys = x ∷ (xs ⊕ ys)

  -- Type \oplus to obtain the oplus ⊕ Unicode glyph.
  -- ⊕
  -- Using both append and singleton we can define a naïve reversing function.  To refine a goal
  -- using e.g. ⊕ type `? ⊕ ?' inside the hole and press <Ctrl> + <c> + <r>.
  -- EXERCISE: complete the following:

  reverse : {A : Set} → List A → List A
  reverse [] = []
  reverse (x ∷ xs) = xs ⊕ [ x ]

  -- To define the length of a list we need some notion of number.  Note there are no numbers
  -- built in to the language.  We have to define them!
  -- Let's define the naturals:

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  -- Type \bN to obtain the natural number ℕ Unicode glyph.
  --
  -- We can define some familiar functions on ℕ via recursion, too:

  _+_ : ℕ → ℕ → ℕ
  zero     + n = n
  (succ m) + n = succ (m + n)

  -- Some constants:

  one : ℕ
  one = succ zero

  two : ℕ
  two = succ one

  -- Using _+_ we can define multiplication, using the intuition that multiplication
  -- is merely repeated addition.
  -- EXERCISE, complete the following:

  _*_ : ℕ → ℕ → ℕ
  zero * n = zero
  succ m * n = n + (m * n)

  -- Using ℕ, We now have enough to define the length of a list:
  -- EXERCISE: complete the following:

  length : {A : Set} → List A → ℕ
  length [] = zero
  length (x ∷ xs) = succ (length xs)

-- Good…
