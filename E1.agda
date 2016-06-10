-- First steps with Agda.  Defining simple types and functions over those types
-- by pattern matching.

-- Note the name of the module must match the name of the file.  Note
-- indentation is significant in Agda, like in Haskell, too.
--
-- Load this file by pressing <Ctrl> + <c> + <l>.

module E1 where

-- Begin by definining the 𝟙 (Unit) type.  The 𝟙 type has exactly one
-- `canonical element', called it:

data 𝟙 : Set where
  it : 𝟙

-- Type \b1 to obtain the Unicode 𝟙 glyph.
--
-- Canonical elements are the values of a given type (i.e. they cannot β-reduce any further).
-- Note that `(λ x → x) it' and `it' both inhabit type `𝟙' but `it' is canonical whereas
-- `(λ x → x) it' is not as we can still β-reduce further.
--
-- Note the syntax for declaring/defining inductive types in Agda is
-- remarkably similar to that for declaring/defining algebraic
-- types in Haskell.  Note also that type ascription is a single colon
-- in Agda compared to Haskell's :: device.  Note also that it is prevailing
-- Agda style to use lowercase constructor names, and when types are written
-- in ASCII, to use Uppercase type names.
--
-- However, there is one difference between the declarations in Haskell
-- and Agda: we must add much more type information to help Agda's type
-- checking algorithm.
--
-- Here Set is a universe, or a type of types.  Set is a shorthand for
-- Set₀, the `universe of small types'.  Set₀ itself has type Set₁, which
-- has type Set₂, which has type Set₃, and so on.  Why this is so will be
-- explained later, but for now make a note that everything, including
-- types, has a type in Agda.

-- What can we do with 𝟙?  Not much, it's pretty useless!

-- Does 𝟙 have the fewest elements out of all possibly definable types?
-- No, we can define a type with 0 `canonical' elements, called 𝟘, or the
-- empty type:

data 𝟘 : Set where

-- Type \b0 to obtain the Unicode 𝟘 glyph.
--
-- Note how this really is the 𝟘 (empty, void) type due to Agda being especially
-- picky about termination of functions.  Haskell and OCaml have no equivalent
-- to this type, despite claiming that they do.  In particular, the Haskell
-- Void type:
--
--   data Void
--
-- Does indeed have inhabitants:
--
--   inhabitantOfVoid :: Void
--   inhabitantOfVoid = inhabitantOfVoid
--
-- Due to Haskell permitting general recursion, which as you will see later, Agda
-- refuses to permit.
--
-- In particular, note how there is no constructor above!  There's no way to
-- introduce a value of type 𝟘 by invoking a constructor, and there's no way to introduce
-- an inhabitant by playing tricks with recursion.  This motivates our next definition:

ex-falso : (A : Set) → 𝟘 → A
ex-falso A ()

-- Type \r to obtain the rightarrow → Unicode glyph.
--
-- What does ex-falso say?  Informally, it says if we can ever conjure up an
-- element of type 𝟘 then we can deduce anything (i.e. we can conclude A, for
-- any A).

-- Why is this useful?  Well, consider 𝟘 to correspond to False in logic.
-- ex-falso then corresponds to the familiar inference rule
--
--              ⊢ False
--            ------------
--                ⊢ φ
--
-- from logic (i.e., if we derive False, then we can conclude anything).
-- You may have guessed that if 𝟘 corresponds to False, then 𝟙 also
-- corresponds to True.  You may also have noted that there's a close connection
-- between the types of constructors and introduction rules in logic.  In
-- both classical and intuitionistic logic True can be introduced trivially:
--
--           ----------
--             ⊢ True
--
-- and there is no introduction rule for False.  Similarly, with 𝟙 and 𝟘 above,
-- we can introduce 𝟙 trivially with `it' and have no way of introducing 𝟘, as
-- there are no constructors in the type!
--
-- If constructors correspond to introduction rules, then `eliminators' correspond to
-- elimination rules.  Eliminators are functions with a type that follows the `shape' of
-- a given type producing some other type and can be viewed as functions that perform case
-- analysis over a type.  We've already seen one eliminator: ex-falso.  Here's another
-- one, the eliminator for 𝟙:

unit-removal : (A : Set) → (𝟙 → A) → A
unit-removal A f = f it

-- Or, in logical form:
--
--           ⊢ True → φ
--          ------------
--              ⊢ φ

-- Looking at the declarations of 𝟙 and 𝟘, and the definitions of `unit-removal' and `ex-falso'
-- you may see that there is a common shape to both of these functions.
                  
-- Note in the definition of `ex-falso' above, ex-falso A (), we have two
-- interesting things going on.
--
-- First, we have passed a type, A, as a parameter.  In Agda, definitions
-- and functions may be polymorphic in their type like in Haskell or
-- Standard ML, but the polymorphism is no longer implicit.  Rather, types
-- must be passed around as arguments to functions instead of being inferred
-- by the compiler.  In some limited places Agda can infer types, but as a general rule,
-- you're going to have to do a lot more work than you do in Haskell or OCaml.
--
-- Second, the second parameter of ex-falso has been replaced by ().  This is
-- known as the absurd pattern, and may be used to replace any pattern whose
-- type Agda deduces cannot be inhabited.  We know that 𝟘 doesn't have any
-- elements, therefore we are justified in giving () as an answer when asked
-- to provide one (Agda will check that the pattern is indeed absurd and
-- complain if not).

-- We now have two basic types.  How can we form new types out of these?
                                                                  
-- The first method is built in to Agda itself, and has already been seen in
-- the type of `ex-falso' and `unit-removal' above, and it is the function arrow →.
-- If A and B are valid types in Agda, so is A → B.  For instance:
                                              
id₀ : 𝟘 → 𝟘
id₀ x = x

-- Type \_0 to obtain the underscore ₀ Unicode glyph.
--
-- Note how, despite 𝟘 having no elements, we can still write the identity
-- function at type 𝟘.  The function doesn't inspect its argument, it just
-- passes it straight through, as an output---we never have to rely on there
-- being a value of type 𝟘 that way!
                                
-- There's also another way of forming new types, and that's with the generalised
-- function space, which again we have seen in the type of ex-falso above.
-- For instance, the following is also correctly typed:

idₐ : (A : Set) → A → A
idₐ A x = x

-- Type \_a to obtain the underscore ₐ Unicode glyph.
--
-- The (A : Set) → … portion of the type above should be read as `for any small type
-- A, …'.  In fact, the function arrow → is a special case of the generalised
-- function space constructor, and we could have written idₐ instead in the
-- following form:

idₐ′ : (A : Set)(y : A) → A
idₐ′ A x = x

-- Type \' to obtain the dash ′ Unicode glyph.
--
-- Which in turn could have been written:

idₐ″ : (A : Set)(_ : A) → A
idₐ″ A x = x

-- Type \'2 to obtain the double-dash ″ Unicode glyph.
--
-- As `y' is not used in the remainder of the type so it can be replaced with the wildcard.

-- We can of course define new ways of combining existing types to form new ones.
-- Here is a familiar one: the Cartesian product.

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- Type \x to obtain the × Unicode glyph.
--
-- Note the use of mixfix syntax above: _×_ indicates that × should be written infix
-- between two types, where _ can be thought of as a `hole' in an identifier.
-- Similarly in the constructor _,_, where the comma will appear infix between two
-- terms.

-- Example:

×-example₁ : 𝟙 × 𝟙
×-example₁ = it , it

-- We can use pattern matching to pull apart elements of a product type.  For example,
-- in the following function that swaps the components of a tuple around:

×-example₂ : (A B : Set) → A × B → B × A
×-example₂ A B (x , y) = y , x

-- Note, the spacing between y , x is important above.  Agda will parse y,x as a single
-- identifier.  Similarly for A×B and all other mixfix syntax.

-- EXERCISE: Try it yourself:

×-exercise₁ : (A : Set) → A × A → A
×-exercise₁ A (x , y) = x

-- Above, the green region is a metavariable, or hole.  These correspond to bits of a
-- function or type that have yet to be completed.  Agda allows you to construct terms
-- and types incrementally, via a process of refinement, where you gradually add more
-- and more structure until you have a complete term or type.

-- Put your cursor inside the hole above.  Press <Ctrl> + <c> + <,>.  A small window
-- should pop up below with something like the following:
--
-- Goal: A
-- ----------------------------------
-- x : A × A
-- A : Set
--
-- This is known as the current proof state.  Above the line, you are being told what you
-- need to construct (i.e. you need to provide something of type A).  Below the line, you
-- are being told what it is you are given, i.e. x of type A × A where A is of type Set.
--
-- We therefore need to get something of type A to satisfy Agda.  What we have is something
-- of type A × A.  By pattern matching, we can therefore extract two things of type A,
-- using one of them to complete our task.  With your cursor in the hole, type
-- <Ctrl> + <c> + <c>.  A small dialogue will open below asking you what pattern variable
-- you wish to case.  Type in x and press enter.  (Alternatively, type x into the hole
-- above and press <Ctrl> + <c> + <c>).  What happens?
--
-- Agda recognises that the variable x has type A × A and is in a pattern position.  It must
-- be the case then that x is a pair, built using the _,_ constructor above, and can be
-- replaced with a pair pattern instead.  Rechecking the goal state (<Ctrl> + <c> + <,> in
-- the hole), we now see x and x₁ both of type A.
--
-- Type x into the hole.  Press <Ctrl> + <c> + <r> (for `refine').  Agda replaces the hole
-- with x (making sure it has the correct type, first), and we are done!

-- EXERCISE: try the following:

fst : (A B : Set) → A × B → A
fst A B (x , _) = x

snd : (A B : Set) → A × B → B
snd A B (_ , y) = y

-- If 𝟘 corresponds to False, and 𝟙 corresponds to True, can you guess what _×_ corresponds
-- to?  Recall the inference rules for conjunction from logic:
--
--      ⊢ A ∧ B       ⊢ A ∧ B       ⊢ A   ⊢ B
--     ---------     ---------     ----------
--        ⊢ A           ⊢ B          ⊢ A ∧ B
--
-- Can you see any analogue in the types of various functions and constructors above?
--
-- Note how `fst' and `snd' above act as elimination rules for _∧_.  There's a more general
-- elimination rule that subsumes both of those and is the `natural' elimination rule if you
-- follow the recipe from `unit-removal' and `ex-falso' above:

×-elimination : (A B C : Set) → A × B → (A → B → C) → C
×-elimination A B C (x , y) f = f x y

-- Or in logical form:
--
--        ⊢ A ∧ B    ⊢ A → B → C
--      --------------------------
--                ⊢ C

-- You may recognise this type: it's the type of the currying function (and the type of the _,_
-- constructor is the type of the uncurry function)!  Curry and uncurry correspond to intro and
-- elimination of conjunction.

-- A note about `canonical' elements.  If 𝟘 has zero canonical elements and 𝟙 has one, how many
-- canonical elements does 𝟙 × 𝟘 have?  Well, to construct a canonical element of 𝟙 × 𝟘 we must
-- use the _,_ constructor, and to use that we need to rustle up a canonical element of 𝟙 and 𝟘.
-- As the latter task is impossible, we deduce that 𝟙 × 𝟘 has zero canonical elements, too.
-- What about 𝟙 × 𝟙?  That's easy: there's only one canonical element, `it , it'.  Examining other
-- cases, we have:
--
--                 | 𝟘 × 𝟘 | 𝟙 × 𝟘 | 𝟘 × 𝟙 | 𝟙 × 𝟙
--       -------------------------------------------
--       Elements: |   0   |   0   |   0   |   1
--
-- Which looks suspiciously like you just need to multiply the number of canonical elements of
-- the types φ and ψ to obtain the number of canonical elements of φ × ψ.  Perhaps _×_ is
-- suggestively named…

-- There are naturally other ways of combining types to form more complicated one.  For
-- example, the disjoint union type:

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Type \uplus to obtain the disjoint union ⊎ Unicode glyph.
--
-- This is the moral equivalent of the Either type in Haskell.
--
-- EXERCISE: Complete the following:

⊎-exercise₁ : (A B : Set) → A ⊎ B → B ⊎ A
⊎-exercise₁ A B (inj₁ x) = inj₂ x
⊎-exercise₁ A B (inj₂ x) = inj₁ x

⊎-exercise₂ : (A B C : Set) → (A → C) → (B → C) → A ⊎ B → C
⊎-exercise₂ A B C l r (inj₁ x) = l x
⊎-exercise₂ A B C l r (inj₂ x) = r x

-- The following is harder and requires a function that has been defined previously:

⊎-exercise₃ : (A : Set) → 𝟘 ⊎ A → A
⊎-exercise₃ A (inj₁ x) = ex-falso A x
⊎-exercise₃ A (inj₂ x) = x

-- Recall that `ex-falso' allows us to deduce anything if we are handed something of type 𝟘.
-- In the exercise above, you will eventually come across a proof state similar to
-- the following:
--
-- Goal: A
-- ---------------------------
-- x : 𝟘
-- A : Set
--
-- Can you see how to close it using `ex-falso'?

 -- Can you guess what logical connective _⊎_ corresponds to?  Write down the inference rules
-- for that logical connective and see if they match the types of any functions/constructors
-- above.

--         ⊢ A              ⊢ B            ⊢ A → C    ⊢ B → C    ⊢ A ∨ B
--      ---------inj₁    ---------inj₂    -------------------------------⊎-exercise₂
--       ⊢ A ∨ B          ⊢ A ∨ B                        C

-- How many canonical elements does 𝟙 ⊎ 𝟙 have?  To construct a canonical element of 𝟙 ⊎ 𝟙 we
-- must identify a canonical element of 𝟙 (easy: `it') and use either inj₁ or inj₂ to construct
-- an element of 𝟙 ⊎ 𝟙.  This gives us two canonical elements of 𝟙 ⊎ 𝟙.  What about 𝟘 ⊎ 𝟙?
-- We have no way to construct a canonical element of 𝟘, but we can construct a canonical element
-- of 𝟘 ⊎ 𝟙 with `inj₂ it', which leaves us with one canonical element of 𝟘 ⊎ 𝟙.  Again, it
-- seems like _⊎_ has been suggestively named, with its hidden `+' symbol.

-- We can also define the Maybe type, a la Standard ML's option type, or Haskell's eponymous
-- type:

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

-- EXERCISE: complete the following:

maybe-exercise₁ : (A : Set) → Maybe A → A → A
maybe-exercise₁ A nothing d = d
maybe-exercise₁ A (just x) d = x

-- Let's define another familiar type.  If 𝟙 has one canonical element, 𝟘 has zero canonical
-- elements, then what type has two canonical elements?  The Boolean type:


data Bool : Set where
  true : Bool
  false : Bool

-- We can easily define negation:
                        
¬_ : Bool → Bool
¬ true  = false
¬ false = true

-- EXERCISE: define conjunction.

_∧_ : Bool → Bool → Bool
true ∧ q = q
false ∧ q = false

-- Type \and to obtain the conjunction ∧ Unicode glyph.
  
-- What other functions can we define on Bool?  What about branching?

if_then_else_ : {A : Set} → Bool → A → A → A
if true then t else f = t
if false then t else f = f

-- Note how if_then_else_ is defined in Agda, whereas in most other programming
-- languages control structures such as if_then_else_ are built in to the
-- language as primitives.

-- But what is the {A : Set} → … syntax?  It is a variant of (A : Set) → … syntax, i.e.
-- the dependent product type, where the programmer (i.e. me) is telling Agda to go
-- ahead and infer the type A from how if_then_else_ is used.  For instance, if we were to
-- use if_then_else_ as
--
--     if b then it else it
--
-- Then Agda will infer that A ≈ 𝟙 and therefore the whole term above has type 𝟙, i.e. Unit.
--
-- We can of course explicitly tell Agda that A is.  If we wrote
--
-- if_then_else_ {A = 𝟙} b it it
--
-- then we are telling Agda that A is 𝟙 explicitly.  Incidentally, the example above also
-- demonstrates that mixfix functions can be applied to arguments like any other function
-- --- there's no need to always supply arguments in mixfix position.
--
-- Agda is quite good at inferring some things, but struggles with others.  Experience
-- tells you when Agda will be able to successfully infer something.  If Agda fails to
-- infer a type, then the place where inference failed will be highlighted in canary
-- yellow, and a warning about metavariables will be displayed in a window below.

-- Thinking back to our declaration of the `Bool' type, we've also met another type that has two
-- canonical elements further up the file, which seems to suggest that our declaration of
-- Bool is superfluous.  Indeed, it is:

 -- Could also be called 𝟚:
Bool′ : Set
Bool′ = 𝟙 ⊎ 𝟙

true′ : Bool′
true′ = inj₁ it

false′ : Bool′
false′ = inj₂ it

¬′_ : Bool′ → Bool′
¬′ inj₁ x = inj₂ x
¬′ inj₂ x = inj₁ x

-- EXERCISE: complete the following:
if_then_else′_ : {A : Set} → Bool′ → A → A → A
if inj₁ x then t else′ f = t
if inj₂ x then t else′ f = f

_∧′_ : Bool′ → Bool′ → Bool′
inj₁ x ∧′ q = q
inj₂ x ∧′ q = inj₂ x

-- Back to counting elements of types.  If 𝟙 and 𝟘 are base types, _⊎_ adds the number of elements
-- and _×_ takes the product, what does _→_ do?  Let's see:
--
--   𝟘 → 𝟘    is inhabited by    (λ x → x)
--   𝟙 → 𝟙    is inhabited by    (λ x → x)
--   𝟙 → 𝟘    is not inhabited
--   𝟘 → 𝟙    is inhabited by    (λ x → it)
--   Bool → 𝟙 is inhabited by   (λ x → it)
--   𝟙 → Bool is inhabited by   (λ x → true) and (λ x → false)
--
--  Which seems to suggest that _→_ corresponds to exponentiation (where 0⁰ = 1).
