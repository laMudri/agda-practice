module Intuitionistic where

open import Category.Functor using (module RawFunctor)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; length)
open import Data.List.Any using (module Membership-≡; here; there)
open Membership-≡ using (_∈_; _⊆_; module ⊆-Reasoning)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality as PEq
  using (_≡_; refl; sym; trans; subst; subst₂; cong; inspect)

open import Function
--open import Level

infixr 50 _∨s_ _∧s_
infixr 40 _→s_

-- Propositional logic terms
data Syntax (A : Set) : Set where
  vars : A → Syntax A
  ⊥s ⊤s : Syntax A
  _∨s_ _∧s_ _→s_ : Syntax A → Syntax A → Syntax A

infixr 60 ¬s_

¬s_ : {A : Set} → Syntax A → Syntax A
¬s s = s →s ⊥s

infix 4 _⊢_ _⇒_

-- Natural deduction rules
data _⊢_ {A : Set} : List (Syntax A) → Syntax A → Set where
  var : ∀ {x} → [ x ] ⊢ x

  ⊥e : ∀ {hs r} → hs ⊢ ⊥s → hs ⊢ r

  ⊤i : [] ⊢ ⊤s

  ∨il : ∀ {hs r s} → hs ⊢ r → hs ⊢ r ∨s s
  ∨ir : ∀ {hs r s} → hs ⊢ s → hs ⊢ r ∨s s
  ∨e : ∀ {hs r s t} → r ∷ hs ⊢ t → s ∷ hs ⊢ t → hs ⊢ r ∨s s → hs ⊢ t

  ∧i : ∀ {hs r s} → hs ⊢ r → hs ⊢ s → hs ⊢ r ∧s s
  ∧el : ∀ {hs r s} → hs ⊢ r ∧s s → hs ⊢ r
  ∧er : ∀ {hs r s} → hs ⊢ r ∧s s → hs ⊢ s

  →i : ∀ {h hs r} → h ∷ hs ⊢ r → hs ⊢ h →s r
  →e : ∀ {hs h r} → hs ⊢ h →s r → hs ⊢ h → hs ⊢ r

  weaken : ∀ {hs hs′ r} → hs ⊆ hs′ → hs ⊢ r → hs′ ⊢ r

-- Sequent calculus rules
data _⇒_ {A : Set} : List (Syntax A) → Syntax A → Set where
  initial : ∀ {p} → p ∷ [] ⇒ p

  ⊥l : ∀ {p} → ⊥s ∷ [] ⇒ p

  ⊤r : [] ⇒ ⊤s

  ∨l : ∀ {pl pr ps q} → pl ∷ ps ⇒ q → pr ∷ ps ⇒ q → pl ∨s pr ∷ ps ⇒ q
  ∨rl : ∀ {ps ql qr} → ps ⇒ ql → ps ⇒ ql ∨s qr
  ∨rr : ∀ {ps ql qr} → ps ⇒ qr → ps ⇒ ql ∨s qr

  ∧l : ∀ {pl pr ps q} → pl ∷ pr ∷ ps ⇒ q → pl ∧s pr ∷ ps ⇒ q
  ∧r : ∀ {ps ql qr} → ps ⇒ ql → ps ⇒ qr → ps ⇒ ql ∧s qr

  →l : ∀ {p ps q r} → ps ⇒ q → p ∷ ps ⇒ r → q →s p ∷ ps ⇒ r
  →r : ∀ {p ps q} → p ∷ ps ⇒ q → ps ⇒ p →s q

  weaken : ∀ {ps ps′ q} → ps ⊆ ps′ → ps ⇒ q → ps′ ⇒ q

  cut : ∀ {ps} q {r} → ps ⇒ q → q ∷ ps ⇒ r → ps ⇒ r

{-
Some syntax intended to mimic proof trees.

--- a  becomes  A
 A                - a

 :
 A              B
--- f  becomes    > f
 B                ∣ A ...

 :   :              C
 A   B                >> g
------- g  becomes    ∣ A ...
   C                  ∣ B ...

 :   :   :              D
 A   B   C                >>> h
----------- h  becomes    ∣ A ...
     D                    ∣ B ...
                          ∣ C ...
-}

∣_ : ∀ {a} {A : Set a} → A → A
∣ a = a

_-_ : ∀ {a} (A : Set a) → A → A
A - a = a

_>_∣_ : ∀ {a b} {A : Set a} (B : Set b) → (A → B) → A → B
B > f ∣ a = f a

_>>_∣_∣_ : ∀ {a b c} {A : Set a} {B : Set b} (C : Set c) → (A → B → C) → A → B → C
C >> f ∣ a ∣ b = f a b

_>>>_∣_∣_∣_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} (D : Set d) → (A → B → C → D) → A → B → C → D
D >>> f ∣ a ∣ b ∣ c = f a b c

infixr 2 ∣_ _-_ _>_∣_ _>>_∣_∣_ _>>>_∣_∣_∣_

example :
  let A = vars 0 in
  let B = vars 1 in
  let C = vars 2 in
  [ A ∨s B →s C ] ⊢ A →s C
example =
  let A = vars 0 in
  let B = vars 1 in
  let C = vars 2 in
  ∣ [ A ∨s B →s C ] ⊢ A →s C
    > →i
    ∣ A ∷ [ A ∨s B →s C ] ⊢ C
      >> →e {h = A ∨s B}
      ∣ A ∷ [ A ∨s B →s C ] ⊢ A ∨s B →s C
        > weaken (λ { (here px) → there (here px) ; (there ()) })
        ∣ [ A ∨s B →s C ] ⊢ A ∨s B →s C
          - var
      ∣ A ∷ [ A ∨s B →s C ] ⊢ A ∨s B
        > weaken (λ { (here px) → here px ; (there ()) })
        ∣ [ A ] ⊢ A ∨s B
          > ∨il
          ∣ [ A ] ⊢ A
            - var

singleton-⊆ : ∀ {a} {A : Set a} {x : A} {xs : List A} → x ∈ xs → [ x ] ⊆ xs
singleton-⊆ {xs = xs} z (here px) = subst (λ x → x ∈ xs) (sym px) z
singleton-⊆ z (there ())

-- Theorem 1:
-- Each natural deduction proof has a corresponding sequent calculus proof.
nd→seq : ∀ {A} {hs : List (Syntax A)} {r : Syntax A} → hs ⊢ r → hs ⇒ r
nd→seq (var {p}) =
  ∣ [ p ] ⇒ p
    - initial
nd→seq {hs = hs} {r} (⊥e t) =
  ∣ hs ⇒ r
    >> cut ⊥s
    ∣ hs ⇒ ⊥s
      - nd→seq t
    ∣ ⊥s ∷ hs ⇒ r
      > weaken (singleton-⊆ (here refl))
      ∣ [ ⊥s ] ⇒ r
        - ⊥l
nd→seq ⊤i = ⊤r
nd→seq {hs = hs} {r ∨s s} (∨il t) =
  ∣ hs ⇒ r ∨s s
    > ∨rl
    ∣ hs ⇒ r
      - nd→seq t
nd→seq {hs = hs} {r ∨s s} (∨ir t) =
  ∣ hs ⇒ r ∨s s
    > ∨rr
    ∣ hs ⇒ s
      - nd→seq t
nd→seq {hs = hs} {q} (∨e {r = r} {s} rt st t) =
  ∣ hs ⇒ q
    >> cut (r ∨s s)
    ∣ hs ⇒ r ∨s s
      - nd→seq t
    ∣ r ∨s s ∷ hs ⇒ q
      >> ∨l
      ∣ r ∷ hs ⇒ q
        - nd→seq rt
      ∣ s ∷ hs ⇒ q
        - nd→seq st
nd→seq {hs = hs} {r ∧s s} (∧i rt st) =
  ∣ hs ⇒ r ∧s s
    >> ∧r
    ∣ hs ⇒ r
      - nd→seq rt
    ∣ hs ⇒ s
      - nd→seq st
nd→seq {hs = hs} (∧el {r = r} {s} t) =
  ∣ hs ⇒ r
    >> cut (r ∧s s)
    ∣ hs ⇒ r ∧s s
      - nd→seq t
    ∣ r ∧s s ∷ hs ⇒ r
      > ∧l
      ∣ r ∷ s ∷ hs ⇒ r
        > weaken (singleton-⊆ (here refl))
        ∣ [ r ] ⇒ r
          - initial
nd→seq {hs = hs} (∧er {r = r} {s} t) =
  ∣ hs ⇒ s
    >> cut (r ∧s s)
    ∣ hs ⇒ r ∧s s
      - nd→seq t
    ∣ r ∧s s ∷ hs ⇒ s
      > ∧l
      ∣ r ∷ s ∷ hs ⇒ s
        > weaken (singleton-⊆ (there (here refl)))
        ∣ [ s ] ⇒ s
          - initial
nd→seq {hs = hs} {h →s r} (→i t) =
  ∣ hs ⇒ h →s r
    > →r
    ∣ h ∷ hs ⇒ r
      - nd→seq t
nd→seq {hs = hs} (→e {h = h} {r} t ht) =
  ∣ hs ⇒ r
    >> cut h
    ∣ hs ⇒ h
      - nd→seq ht
    ∣ h ∷ hs ⇒ r
      >> cut (h →s r)
      ∣ h ∷ hs ⇒ h →s r
        > weaken there
        ∣ hs ⇒ h →s r
          - nd→seq t
      ∣ h →s r ∷ h ∷ hs ⇒ r
        >> →l
        ∣ h ∷ hs ⇒ h
          > weaken (singleton-⊆ (here refl))
          ∣ [ h ] ⇒ h
            - initial
        ∣ r ∷ h ∷ hs ⇒ r
          > weaken (singleton-⊆ (here refl))
          ∣ [ r ] ⇒ r
            - initial
nd→seq (weaken {hs = hs} {hs′} {r} sub t) =
  ∣ hs′ ⇒ r
    > weaken sub
    ∣ hs ⇒ r
      - nd→seq t

-- Theorem 2:
-- Each sequent calculus proof has a corresponding natural deduction proof.
seq→nd : ∀ {A} {ps : List (Syntax A)} {q} → ps ⇒ q → ps ⊢ q
seq→nd (initial {p}) =
  ∣ [ p ] ⊢ p
    - var
seq→nd (⊥l {q}) =
  ∣ [ ⊥s ] ⊢ q
    > ⊥e
    ∣ [ ⊥s ] ⊢ ⊥s
      - var
seq→nd ⊤r =
  ∣ [] ⊢ ⊤s
    - ⊤i
seq→nd (∨l {pl} {pr} {ps} {q} lt rt) =
  ∣ pl ∨s pr ∷ ps ⊢ q
    >>> ∨e
    ∣ pl ∷ pl ∨s pr ∷ ps ⊢ q
      > weaken (λ { (here px) → here px ; (there z) → there (there z) })
      ∣ pl ∷ ps ⊢ q
        - seq→nd lt
    ∣ pr ∷ pl ∨s pr ∷ ps ⊢ q
      > weaken (λ { (here px) → here px ; (there z) → there (there z) })
      ∣ pr ∷ ps ⊢ q
        - seq→nd rt
    ∣ pl ∨s pr ∷ ps ⊢ pl ∨s pr
      > weaken (singleton-⊆ (here refl))
      ∣ [ pl ∨s pr ] ⊢ pl ∨s pr
        - var
seq→nd (∨rl {ps} {ql} {qr} t) =
  ∣ ps ⊢ ql ∨s qr
    > ∨il
    ∣ ps ⊢ ql
      - seq→nd t
seq→nd (∨rr {ps} {ql} {qr} t) =
  ∣ ps ⊢ ql ∨s qr
    > ∨ir
    ∣ ps ⊢ qr
      - seq→nd t
seq→nd (∧l {pl} {pr} {ps} {q} t) =
  ∣ pl ∧s pr ∷ ps ⊢ q
    >> →e
    ∣ pl ∧s pr ∷ ps ⊢ pl →s q
      >> →e
      ∣ pl ∧s pr ∷ ps ⊢ pr →s pl →s q
        > weaken there
        ∣ ps ⊢ pr →s pl →s q
          > →i
          ∣ pr ∷ ps ⊢ pl →s q
            > →i
            ∣ pl ∷ pr ∷ ps ⊢ q
              - seq→nd t
      ∣ pl ∧s pr ∷ ps ⊢ pr
        > weaken (singleton-⊆ (here refl))
        ∣ [ pl ∧s pr ] ⊢ pr
          > ∧er
          ∣ [ pl ∧s pr ] ⊢ pl ∧s pr
            - var
    ∣ pl ∧s pr ∷ ps ⊢ pl
      > weaken (singleton-⊆ (here refl))
      ∣ [ pl ∧s pr ] ⊢ pl
        > ∧el
        ∣ [ pl ∧s pr ] ⊢ pl ∧s pr
          - var
seq→nd (∧r {ps} {ql} {qr} lt rt) =
  ∣ ps ⊢ ql ∧s qr
    >> ∧i
    ∣ ps ⊢ ql
      - seq→nd lt
    ∣ ps ⊢ qr
      - seq→nd rt
seq→nd (→l {p} {ps} {q} {r} qt t) =
  ∣ q →s p ∷ ps ⊢ r
    >> →e
    ∣ q →s p ∷ ps ⊢ p →s r
      > →i
      ∣ p ∷ q →s p ∷ ps ⊢ r
        > weaken (λ { (here px) → here px ; (there z) → there (there z) })
        ∣ p ∷ ps ⊢ r
          - seq→nd t
    ∣ q →s p ∷ ps ⊢ p
      >> →e
      ∣ q →s p ∷ ps ⊢ q →s p
        > weaken (singleton-⊆ (here refl))
        ∣ [ q →s p ] ⊢ q →s p
          - var
      ∣ q →s p ∷ ps ⊢ q
        > weaken there
        ∣ ps ⊢ q
          - seq→nd qt
seq→nd (→r {p} {ps} {q} t) =
  ∣ ps ⊢ p →s q
    > →i
    ∣ p ∷ ps ⊢ q
      - seq→nd t
seq→nd (weaken {ps} {ps′} {q} sub t) =
  ∣ ps′ ⊢ q
    > weaken sub
    ∣ ps ⊢ q
      - seq→nd t
seq→nd (cut {ps} q {r} ptq qtr) =
  ∣ ps ⊢ r
    >> →e
    ∣ ps ⊢ q →s r
      > →i
      ∣ q ∷ ps ⊢ r
        - seq→nd qtr
    ∣ ps ⊢ q
      - seq→nd ptq

-- Very good!  Now a term assignment from ND for the λ-calculus?  Here's a trick you may like to consider:

infix 40 case_of_⇒_or_⇒_ caset_of_or_
infixr 50 _,,_ _,,t_
infixl 60 _·_ _·t_

data LambdaTerm (A : Set) : Set where
  ↑ : ℕ → LambdaTerm A

  void-elim : LambdaTerm A → LambdaTerm A

  unit : LambdaTerm A

  inl inr : LambdaTerm A → LambdaTerm A
  case_of_⇒_or_⇒_ :
    LambdaTerm A →
    Syntax A → LambdaTerm A → Syntax A → LambdaTerm A → LambdaTerm A

  _,,_ : (f s : LambdaTerm A) → LambdaTerm A
  fst snd : LambdaTerm A → LambdaTerm A

  ƛ : Syntax A → LambdaTerm A → LambdaTerm A
  _·_ : LambdaTerm A → LambdaTerm A → LambdaTerm A

∈-index : ∀ {a} {A : Set a} {x : A} {xs} → x ∈ xs → ℕ
∈-index (here px) = zero
∈-index (there z) = suc (∈-index z)

infix 4 _⊢_∈_

data _⊢_∈_ {A} (Γ : List (Syntax A)) : LambdaTerm A → Syntax A → Set where
  ↑t : ∀ {τ} (v : τ ∈ Γ) → Γ ⊢ ↑ (∈-index v) ∈ τ

  void-elimt : ∀ {v τ} → Γ ⊢ v ∈ ⊥s → Γ ⊢ void-elim v ∈ τ

  unitt : Γ ⊢ unit ∈ ⊤s

  inlt : ∀ {a τ τ′} → Γ ⊢ a ∈ τ → Γ ⊢ inl a ∈ τ ∨s τ′
  inrt : ∀ {b τ τ′} → Γ ⊢ b ∈ τ′ → Γ ⊢ inr b ∈ τ ∨s τ′
  caset_of_or_ :
    ∀ {c l r τ τ′ ρ} → Γ ⊢ c ∈ τ ∨s τ′ → τ ∷ Γ ⊢ l ∈ ρ → τ′ ∷ Γ ⊢ r ∈ ρ →
    Γ ⊢ case c of τ ⇒ l or τ′ ⇒ r ∈ ρ

  _,,t_ : ∀ {a b τ τ′} → Γ ⊢ a ∈ τ → Γ ⊢ b ∈ τ′ → Γ ⊢ a ,, b ∈ τ ∧s τ′
  fstt : ∀ {p τ τ′} → Γ ⊢ p ∈ τ ∧s τ′ → Γ ⊢ fst p ∈ τ
  sndt : ∀ {p τ τ′} → Γ ⊢ p ∈ τ ∧s τ′ → Γ ⊢ snd p ∈ τ′

  _·t_ : ∀ {l r τ τ′} → Γ ⊢ l ∈ (τ →s τ′) → Γ ⊢ r ∈ τ → Γ ⊢ l · r ∈ τ′
  ƛt : ∀ {b τ τ′} → (τ ∷ Γ) ⊢ b ∈ τ′ → Γ ⊢ ƛ τ b ∈ (τ →s τ′)

infixr 5 _∷-⊆_

_∷-⊆_ : ∀ {a} {A : Set a} (x : A) {xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
(x ∷-⊆ sub) (here px) = here px
(x ∷-⊆ sub) (there z) = there (sub z)

ℕ-to-∈? : ∀ {a} {A : Set a} → ℕ → (xs : List A) → Maybe (∃ λ x → x ∈ xs)
ℕ-to-∈? i [] = nothing
ℕ-to-∈? zero (x ∷ xs) = just (x , here refl)
ℕ-to-∈? (suc i) (x ∷ xs) =
  (λ { (y , y∈xs) → y , there y∈xs }) <$> ℕ-to-∈? i xs
  where open RawFunctor Maybe.functor

substitute :
  ∀ {A} {Γ Γ′ : List (Syntax A)} → Γ ⊆ Γ′ → LambdaTerm A → LambdaTerm A
substitute {Γ = Γ} {Γ′} sub (↑ x) with ℕ-to-∈? x Γ
substitute sub (↑ x) | just (v , v∈Γ) =
  let v∈Γ′ = sub v∈Γ in
  ↑ (∈-index v∈Γ′)
substitute sub (↑ x) | nothing = ↑ x  -- dummy - shouldn't be well-typed
substitute sub (void-elim l) = void-elim (substitute sub l)
substitute sub unit = unit
substitute sub (inl l) = inl (substitute sub l)
substitute sub (inr l) = inr (substitute sub l)
substitute sub (case cl of τ ⇒ ll or τ′ ⇒ rl) =
  case substitute sub cl
    of τ ⇒ substitute (τ ∷-⊆ sub) ll
    or τ′ ⇒ substitute (τ′ ∷-⊆ sub) rl
substitute sub (ll ,, rl) = substitute sub ll ,, substitute sub rl
substitute sub (fst l) = fst (substitute sub l)
substitute sub (snd l) = snd (substitute sub l)
substitute {Γ = Γ} {Γ′} sub (ƛ τ l) = ƛ τ (substitute (τ ∷-⊆ sub) l)
substitute sub (l · hl) = substitute sub l · substitute sub hl

extract : ∀ {A} {Γ : List (Syntax A)} {p} → Γ ⊢ p → LambdaTerm A
extract var = ↑ zero
extract (⊥e t) = void-elim (extract t)
extract ⊤i = unit
extract (∨il t) = inl (extract t)
extract (∨ir t) = inr (extract t)
extract (∨e {r = τ} {τ′} rt st t) =
  case extract t
    of τ ⇒ extract rt
    or τ′ ⇒ extract st
extract (∧i rt st) = extract rt ,, extract st
extract (∧el t) = fst (extract t)
extract (∧er t) = snd (extract t)
extract (→i {h = h} t) = ƛ h (extract t)
extract (→e t ht) = extract t · extract ht
extract (weaken sub t) = substitute sub (extract t)

∈-ℕ-∈ :
  ∀ {a} {A : Set a} {x : A} {xs} (z : x ∈ xs) →
  ℕ-to-∈? (∈-index z) xs ≡ just (x , z)
∈-ℕ-∈ (here refl) = refl
∈-ℕ-∈ (there z) = cong (_<$>_ λ { (y , y∈xs) → y , there y∈xs }) (∈-ℕ-∈ z)
  where open RawFunctor Maybe.functor

just-injective :
  ∀ {a} {A : Set a} {x y : A} → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
just-injective refl = refl

substitute-correct :
  ∀ {A} {Γ Γ′ : List (Syntax A)} (sub : Γ ⊆ Γ′) {l τ} →
  Γ ⊢ l ∈ τ → Γ′ ⊢ substitute sub l ∈ τ
substitute-correct {Γ = Γ} sub (↑t v)
  with ℕ-to-∈? (∈-index v) Γ | inspect (ℕ-to-∈? (∈-index v)) Γ
substitute-correct {Γ′ = Γ′} sub {τ = τ} (↑t v) | just (τ′ , v′) | PEq.[ eq ] =
  let eq′ = trans (sym eq) (∈-ℕ-∈ v) in
  let τeq = cong proj₁ (just-injective eq′) in
  subst (λ ττ → Γ′ ⊢ ↑ (∈-index (sub v′)) ∈ ττ) τeq (↑t (sub v′))
substitute-correct sub (↑t v) | nothing | PEq.[ eq ] =
  ⊥-elim (subst P (trans (sym eq) (∈-ℕ-∈ v)) tt)
  where
  P : ∀ {a} {A : Set a} → Maybe A → Set
  P nothing = ⊤
  P (just _) = ⊥
substitute-correct sub (void-elimt j) = void-elimt (substitute-correct sub j)
substitute-correct sub unitt = unitt
substitute-correct sub (inlt j) = inlt (substitute-correct sub j)
substitute-correct sub (inrt j) = inrt (substitute-correct sub j)
substitute-correct sub (caset_of_or_ {τ = τ} {τ′} cj lj rj) =
  caset substitute-correct sub cj
    of substitute-correct (τ ∷-⊆ sub) lj
    or substitute-correct (τ′ ∷-⊆ sub) rj
substitute-correct sub (lj ,,t rj) =
  substitute-correct sub lj ,,t substitute-correct sub rj
substitute-correct sub (fstt j) = fstt (substitute-correct sub j)
substitute-correct sub (sndt j) = sndt (substitute-correct sub j)
substitute-correct sub (j ·t hj) =
  substitute-correct sub j ·t substitute-correct sub hj
substitute-correct sub (ƛt {τ = τ} j) =
  ƛt (substitute-correct (τ ∷-⊆ sub) j)

extract-correct :
  ∀ {A} {Γ : List (Syntax A)} {p} (t : Γ ⊢ p) → Γ ⊢ extract t ∈ p
extract-correct var = ↑t (here refl)
extract-correct (⊥e t) = void-elimt (extract-correct t)
extract-correct ⊤i = unitt
extract-correct (∨il t) = inlt (extract-correct t)
extract-correct (∨ir t) = inrt (extract-correct t)
extract-correct (∨e rt st t) =
  caset extract-correct t
    of extract-correct rt
    or extract-correct st
extract-correct (∧i rt st) = extract-correct rt ,,t extract-correct st
extract-correct (∧el t) = fstt (extract-correct t)
extract-correct (∧er t) = sndt (extract-correct t)
extract-correct (→i t) = ƛt (extract-correct t)
extract-correct (→e t ht) = extract-correct t ·t extract-correct ht
extract-correct (weaken sub t) = substitute-correct sub (extract-correct t)
