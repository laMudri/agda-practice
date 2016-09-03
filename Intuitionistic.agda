module Intuitionistic where

open import Data.Empty using (⊥)

open import Data.List using (List; []; _∷_; [_])
open import Data.List.Any using (module Membership-≡; here; there)
open Membership-≡ using (_∈_; _⊆_; module ⊆-Reasoning)

open import Data.Product using (∃; _×_; _,_)

open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Function
open import Level

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
