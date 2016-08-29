module Classical where

open import Data.Empty using (⊥)

open import Data.List using (List; []; _∷_; [_]; _++_; foldr; take)
open import Data.List.Any using (module Membership-≡; here; there)
open Membership-≡ using (_∈_; _⊆_; module ⊆-Reasoning)

open import Data.Product using (∃; _×_; _,_)

open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

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

-- Natural deduction rules + double-negation elimination
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

  ¬¬e : ∀ {hs r} → hs ⊢ ¬s ¬s r → hs ⊢ r

  weaken : ∀ {hs hs′ r} → hs ⊆ hs′ → hs ⊢ r → hs′ ⊢ r

-- Sequent calculus rules
data _⇒_ {A : Set} : List (Syntax A) → List (Syntax A) → Set where
  initial : ∀ {p} → p ∷ [] ⇒ p ∷ []

  ⊥l : ⊥s ∷ [] ⇒ []

  ⊤r : [] ⇒ ⊤s ∷ []

  ∨l : ∀ {pl pr ps qs} → pl ∷ ps ⇒ qs → pr ∷ ps ⇒ qs → pl ∨s pr ∷ ps ⇒ qs
  ∨r : ∀ {ps ql qr qs} → ps ⇒ ql ∷ qr ∷ qs → ps ⇒ ql ∨s qr ∷ qs

  ∧l : ∀ {pl pr ps qs} → pl ∷ pr ∷ ps ⇒ qs → pl ∧s pr ∷ ps ⇒ qs
  ∧r : ∀ {ps ql qr qs} → ps ⇒ ql ∷ qs → ps ⇒ qr ∷ qs → ps ⇒ ql ∧s qr ∷ qs

  →l : ∀ {p ps q qs} → ps ⇒ q ∷ qs → p ∷ ps ⇒ qs → q →s p ∷ ps ⇒ qs
  →r : ∀ {p ps q qs} → p ∷ ps ⇒ q ∷ qs → ps ⇒ p →s q ∷ qs

  weaken : ∀ {ps ps′ qs qs′} → ps ⊆ ps′ → qs ⊆ qs′ → ps ⇒ qs → ps′ ⇒ qs′

  cut : ∀ {ps} q {rs} → ps ⇒ q ∷ rs → q ∷ ps ⇒ rs → ps ⇒ rs

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

¬¬-elim-seq : ∀ {A} (P : Syntax A) → [ ¬s ¬s P ] ⇒ [ P ]
¬¬-elim-seq P =
  ∣ [ ¬s ¬s P ] ⇒ [ P ]
    >> →l
    ∣ [] ⇒ ¬s P ∷ [ P ]
      > →r
      ∣ [ P ] ⇒ ⊥s ∷ [ P ]
        > weaken id (singleton-⊆ (there (here refl)))
        ∣ [ P ] ⇒ [ P ]
          - initial
    ∣ [ ⊥s ] ⇒ [ P ]
      > weaken id (λ ())
      ∣ [ ⊥s ] ⇒ []
        - ⊥l

-- Theorem 1:
-- Each natural deduction proof has a corresponding sequent calculus proof.
nd→seq : ∀ {A} {hs : List (Syntax A)} {r : Syntax A} → hs ⊢ r → hs ⇒ [ r ]
nd→seq var = initial
nd→seq {hs = hs} {r} (⊥e t) =
  ∣ hs ⇒ [ r ]
    >> cut ⊥s
    ∣ hs ⇒ ⊥s ∷ [ r ]
      > weaken id (singleton-⊆ (here refl))
      ∣ hs ⇒ [ ⊥s ]
        - nd→seq t
    ∣ ⊥s ∷ hs ⇒ [ r ]
      > weaken (singleton-⊆ (here refl)) (λ ())
      ∣ [ ⊥s ] ⇒ []
        - ⊥l
nd→seq ⊤i = ⊤r
nd→seq {hs = hs} {r ∨s s} (∨il t) =
  ∣ hs ⇒ [ r ∨s s ]
    > ∨r
    ∣ hs ⇒ r ∷ s ∷ []
      > weaken id (singleton-⊆ (here refl))
      ∣ hs ⇒ [ r ]
        - nd→seq t
nd→seq {hs = hs} {r ∨s s} (∨ir t) =
  ∣ hs ⇒ [ r ∨s s ]
    > ∨r
    ∣ hs ⇒ r ∷ s ∷ []
      > weaken id (singleton-⊆ (there (here refl)))
      ∣ hs ⇒ [ s ]
        - nd→seq t
nd→seq {hs = hs} {q} (∨e {r = r} {s} rt st t) =
  ∣ hs ⇒ [ q ]
    >> cut (r ∨s s)
    ∣ hs ⇒ r ∨s s ∷ [ q ]
      > weaken id (singleton-⊆ (here refl))
      ∣ hs ⇒ [ r ∨s s ]
        - nd→seq t
    ∣ r ∨s s ∷ hs ⇒ [ q ]
      >> ∨l
      ∣ r ∷ hs ⇒ [ q ]
        - nd→seq rt
      ∣ s ∷ hs ⇒ [ q ]
        - nd→seq st
nd→seq {hs = hs} {r ∧s s} (∧i rt st) =
  ∣ hs ⇒ [ r ∧s s ]
    >> ∧r
    ∣ hs ⇒ [ r ]
      - nd→seq rt
    ∣ hs ⇒ [ s ]
      - nd→seq st
nd→seq {hs = hs} (∧el {r = r} {s} t) =
  ∣ hs ⇒ [ r ]
    >> cut (r ∧s s)
    ∣ hs ⇒ r ∧s s ∷ [ r ]
      > weaken id (singleton-⊆ (here refl))
      ∣ hs ⇒ [ r ∧s s ]
        - nd→seq t
    ∣ r ∧s s ∷ hs ⇒ [ r ]
      > ∧l
      ∣ r ∷ s ∷ hs ⇒ [ r ]
        > weaken (singleton-⊆ (here refl)) id
        ∣ [ r ] ⇒ [ r ]
          - initial
nd→seq {hs = hs} (∧er {r = r} {s} t) =
  ∣ hs ⇒ [ s ]
    >> cut (r ∧s s)
    ∣ hs ⇒ r ∧s s ∷ [ s ]
      > weaken id (singleton-⊆ (here refl))
      ∣ hs ⇒ [ r ∧s s ]
        - nd→seq t
    ∣ r ∧s s ∷ hs ⇒ [ s ]
      > ∧l
      ∣ r ∷ s ∷ hs ⇒ [ s ]
        > weaken (singleton-⊆ (there (here refl))) id
        ∣ [ s ] ⇒ [ s ]
          - initial
nd→seq {hs = hs} {h →s r} (→i t) =
  ∣ hs ⇒ [ h →s r ]
    > →r
    ∣ h ∷ hs ⇒ [ r ]
      - nd→seq t
nd→seq {hs = hs} (→e {h = h} {r} t ht) =
  ∣ hs ⇒ [ r ]
    >> cut h
    ∣ hs ⇒ h ∷ [ r ]
      > weaken id (singleton-⊆ (here refl))
      ∣ hs ⇒ [ h ]
        - nd→seq ht
    ∣ h ∷ hs ⇒ [ r ]
      >> cut (h →s r)
      ∣ h ∷ hs ⇒ h →s r ∷ [ r ]
        > weaken there (singleton-⊆ (here refl))
        ∣ hs ⇒ [ h →s r ]
          - nd→seq t
      ∣ h →s r ∷ h ∷ hs ⇒ [ r ]
        >> →l
        ∣ h ∷ hs ⇒ h ∷ [ r ]
          > weaken (singleton-⊆ (here refl)) (singleton-⊆ (here refl))
          ∣ [ h ] ⇒ [ h ]
            - initial
        ∣ r ∷ h ∷ hs ⇒ [ r ]
          > weaken (singleton-⊆ (here refl)) id
          ∣ [ r ] ⇒ [ r ]
            - initial
nd→seq {hs = hs} {r} (¬¬e t) =
  ∣ hs ⇒ [ r ]
    >> cut (¬s ¬s r)
    ∣ hs ⇒ ¬s ¬s r ∷ [ r ]
      > weaken id (singleton-⊆ (here refl))
      ∣ hs ⇒ [ ¬s ¬s r ]
        - nd→seq t
    ∣ ¬s ¬s r ∷ hs ⇒ [ r ]
      > weaken (singleton-⊆ (here refl)) id
      ∣ [ ¬s ¬s r ] ⇒ [ r ]
        - ¬¬-elim-seq r
nd→seq (weaken {hs = hs} {hs′} {r} sub t) =
  ∣ hs′ ⇒ [ r ]
    > weaken sub id
    ∣ hs ⇒ [ r ]
      - nd→seq t

⋁ : ∀ {A} → List (Syntax A) → Syntax A
⋁ = foldr _∨s_ ⊥s

⋁i : ∀ {A r} {hs rs : List (Syntax A)} → r ∈ rs → hs ⊢ r → hs ⊢ ⋁ rs
⋁i {hs = hs} {x ∷ rs} (here px) t =
  ∣ hs ⊢ x ∨s ⋁ rs
    > ∨il
    ∣ hs ⊢ x
      - subst (λ y → hs ⊢ y) px t
⋁i {hs = hs} {x ∷ rs} (there rrs) t =
  ∣ hs ⊢ x ∨s ⋁ rs
    > ∨ir
    ∣ hs ⊢ ⋁ rs
      - ⋁i rrs t

-- Lemma for the weaken case
weakening-⊢ : ∀ {A} {hs hs′ : List (Syntax A)} → hs ⊆ hs′ → [ ⋁ hs ] ⊢ ⋁ hs′
weakening-⊢ {hs = []} {hs′} sub =
  ∣ [ ⊥s ] ⊢ ⋁ hs′
    > ⊥e
    ∣ [ ⊥s ] ⊢ ⊥s
      - var
weakening-⊢ {hs = h ∷ hs} {hs′} sub =
  ∣ [ h ∨s ⋁ hs ] ⊢ ⋁ hs′
    >>> ∨e
    ∣ h ∷ [ h ∨s ⋁ hs ] ⊢ ⋁ hs′
      > weaken (singleton-⊆ (here refl))
      ∣ [ h ] ⊢ ⋁ hs′
        > ⋁i (sub (here refl))
        ∣ [ h ] ⊢ h
          - var
    ∣ ⋁ hs ∷ [ h ∨s ⋁ hs ] ⊢ ⋁ hs′
      > weaken (singleton-⊆ (here refl))
      ∣ [ ⋁ hs ] ⊢ ⋁ hs′
        - weakening-⊢ (sub ∘ there)
    ∣ [ h ∨s ⋁ hs ] ⊢ h ∨s ⋁ hs
      - var

lem-nd : ∀ {A} (P : Syntax A) → [] ⊢ P ∨s ¬s P
lem-nd P =
  ∣ [] ⊢ P ∨s ¬s P
    > ¬¬e
    ∣ [] ⊢ ¬s ¬s (P ∨s ¬s P)
      > →i
      ∣ [ ¬s (P ∨s ¬s P) ] ⊢ ⊥s
        >> →e
        ∣ [ ¬s (P ∨s ¬s P) ] ⊢ ¬s ¬s P
          > →i
          ∣ ¬s P ∷ [ ¬s (P ∨s ¬s P) ] ⊢ ⊥s
            >> →e
            ∣ ¬s P ∷ [ ¬s (P ∨s ¬s P) ] ⊢ ¬s (P ∨s ¬s P)
              > weaken (singleton-⊆ (there (here refl)))
              ∣ [ ¬s (P ∨s ¬s P) ] ⊢ ¬s (P ∨s ¬s P)
                - var
            ∣ ¬s P ∷ [ ¬s (P ∨s ¬s P) ] ⊢ P ∨s ¬s P
              > weaken (singleton-⊆ (here refl))
              ∣ [ ¬s P ] ⊢ P ∨s ¬s P
                > ∨ir
                ∣ [ ¬s P ] ⊢ ¬s P
                  - var
        ∣ [ ¬s (P ∨s ¬s P) ] ⊢ ¬s P
          > →i
          ∣ P ∷ [ ¬s (P ∨s ¬s P) ] ⊢ ⊥s
            >> →e
            ∣ P ∷ [ ¬s (P ∨s ¬s P) ] ⊢ ¬s (P ∨s ¬s P)
              > weaken (singleton-⊆ (there (here refl)))
              ∣ [ ¬s (P ∨s ¬s P) ] ⊢ ¬s (P ∨s ¬s P)
                - var
            ∣ P ∷ [ ¬s (P ∨s ¬s P) ] ⊢ P ∨s ¬s P
              > weaken (singleton-⊆ (here refl))
              ∣ [ P ] ⊢ P ∨s ¬s P
                > ∨il
                ∣ [ P ] ⊢ P
                  - var

-- Theorem 2:
-- Each sequent calculus proof has a corresponding natural deduction proof.
seq→nd : ∀ {A} {ps qs : List (Syntax A)} → ps ⇒ qs → ps ⊢ ⋁ qs
seq→nd (initial {p}) =
  ∣ [ p ] ⊢ p ∨s ⊥s
    > ∨il
    ∣ [ p ] ⊢ p
      - var
seq→nd ⊥l =
  ∣ [ ⊥s ] ⊢ ⊥s
    - var
seq→nd ⊤r =
  ∣ [] ⊢ ⊤s ∨s ⊥s
    > ∨il
    ∣ [] ⊢ ⊤s
      - ⊤i
seq→nd (∨l {pl} {pr} {ps} {qs} lt rt) =
  ∣ pl ∨s pr ∷ ps ⊢ ⋁ qs
    >>> ∨e
    ∣ pl ∷ pl ∨s pr ∷ ps ⊢ ⋁ qs
      > weaken (λ { (here px) → here px ; (there z) → there (there z) })
      ∣ pl ∷ ps ⊢ ⋁ qs
        - seq→nd lt
    ∣ pr ∷ pl ∨s pr ∷ ps ⊢ ⋁ qs
      > weaken (λ { (here px) → here px ; (there z) → there (there z) })
      ∣ pr ∷ ps ⊢ ⋁ qs
        - seq→nd rt
    ∣ pl ∨s pr ∷ ps ⊢ pl ∨s pr
      > weaken (singleton-⊆ (here refl))
      ∣ [ pl ∨s pr ] ⊢ pl ∨s pr
        - var
seq→nd (∨r {ps} {ql} {qr} {qs} t) =
  ∣ ps ⊢ ⋁ (ql ∨s qr ∷ qs)
    > ¬¬e
    ∣ ps ⊢ ¬s ¬s ⋁ (ql ∨s qr ∷ qs)
      > →i
      ∣ ¬s ⋁ (ql ∨s qr ∷ qs) ∷ ps ⊢ ⊥s
        >>> ∨e
        ∣ ql ∨s qr ∷ ¬s ⋁ (ql ∨s qr ∷ qs) ∷ ps ⊢ ⊥s
          >> →e
          ∣ ql ∨s qr ∷ ¬s ((ql ∨s qr) ∨s ⋁ qs) ∷ ps ⊢ ((ql ∨s qr) ∨s ⋁ qs) →s ⊥s
            > weaken (singleton-⊆ (there (here refl)))
            ∣ [ ¬s ((ql ∨s qr) ∨s ⋁ qs) ] ⊢ (ql ∨s qr) ∨s ⋁ qs →s ⊥s
              - var
          ∣ ql ∨s qr ∷ ¬s ⋁ (ql ∨s qr ∷ qs) ∷ ps ⊢ (ql ∨s qr) ∨s ⋁ qs
            > weaken (singleton-⊆ (here refl))
            ∣ [ ql ∨s qr ] ⊢ (ql ∨s qr) ∨s ⋁ qs
              > ∨il
              ∣ [ ql ∨s qr ] ⊢ ql ∨s qr
                - var
        ∣ ⋁ qs ∷ ¬s ⋁ (ql ∨s qr ∷ qs) ∷ ps ⊢ ⊥s
          >> →e
          ∣ ⋁ qs ∷ ¬s ⋁ (ql ∨s qr ∷ qs) ∷ ps ⊢ (ql ∨s qr) ∨s ⋁ qs →s ⊥s
            > weaken (singleton-⊆ (there (here refl)))
            ∣ [ ¬s ⋁ (ql ∨s qr ∷ qs) ] ⊢ (ql ∨s qr) ∨s ⋁ qs →s ⊥s
              - var
          ∣ ⋁ qs ∷ ¬s ⋁ (ql ∨s qr ∷ qs) ∷ ps ⊢ (ql ∨s qr) ∨s ⋁ qs
            > weaken (singleton-⊆ (here refl))
            ∣ [ ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
              > ∨ir
              ∣ [ ⋁ qs ] ⊢ ⋁ qs
                - var
        ∣ ¬s ⋁ (ql ∨s qr ∷ qs) ∷ ps ⊢ (ql ∨s qr) ∨s ⋁ qs
          > weaken there
          ∣ ps ⊢ (ql ∨s qr) ∨s ⋁ qs
            >> →e
            ∣ ps ⊢ ⋁ (ql ∷ qr ∷ qs) →s (ql ∨s qr) ∨s ⋁ qs
              > weaken (λ ())
              ∣ [] ⊢ ql ∨s qr ∨s ⋁ qs →s (ql ∨s qr) ∨s ⋁ qs
                > →i
                ∣ [ ql ∨s qr ∨s ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                  >>> ∨e
                  ∣ ql ∷ [ ql ∨s qr ∨s ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                    > weaken (singleton-⊆ (here refl))
                    ∣ [ ql ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                      > ∨il
                      ∣ [ ql ] ⊢ ql ∨s qr
                        > ∨il
                        ∣ [ ql ] ⊢ ql
                          - var
                  ∣ qr ∨s ⋁ qs ∷ [ ql ∨s qr ∨s ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                    > weaken (singleton-⊆ (here refl))
                    ∣ [ qr ∨s ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                      >>> ∨e
                      ∣ qr ∷ [ qr ∨s ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                        > weaken (singleton-⊆ (here refl))
                        ∣ [ qr ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                          > ∨il
                          ∣ [ qr ] ⊢ ql ∨s qr
                            > ∨ir
                            ∣ [ qr ] ⊢ qr
                              - var
                      ∣ ⋁ qs ∷ [ qr ∨s ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                        > weaken (singleton-⊆ (here refl))
                        ∣ [ ⋁ qs ] ⊢ (ql ∨s qr) ∨s ⋁ qs
                          > ∨ir
                          ∣ [ ⋁ qs ] ⊢ ⋁ qs
                            - var
                      ∣ [ qr ∨s ⋁ qs ] ⊢ qr ∨s ⋁ qs
                        - var
                  ∣ [ ql ∨s qr ∨s ⋁ qs ] ⊢ ql ∨s qr ∨s ⋁ qs
                    - var
            ∣ ps ⊢ ⋁ (ql ∷ qr ∷ qs)
              - seq→nd t
seq→nd (∧l {pl} {pr} {ps} {qs} t) =
  ∣ pl ∧s pr ∷ ps ⊢ ⋁ qs
    >> →e
    ∣ pl ∧s pr ∷ ps ⊢ pl →s ⋁ qs
      >> →e
      ∣ pl ∧s pr ∷ ps ⊢ pr →s pl →s ⋁ qs
        > weaken there
        ∣ ps ⊢ pr →s pl →s ⋁ qs
          > →i
          ∣ pr ∷ ps ⊢ pl →s ⋁ qs
            > →i
            ∣ pl ∷ pr ∷ ps ⊢ ⋁ qs
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
seq→nd (∧r {ps} {ql} {qr} {qs} lt rt) =
  ∣ ps ⊢ (ql ∧s qr) ∨s ⋁ qs
    >>> ∨e
    ∣ ql ∷ ps ⊢ (ql ∧s qr) ∨s ⋁ qs
      >>> ∨e
      ∣ qr ∷ ql ∷ ps ⊢ (ql ∧s qr) ∨s ⋁ qs
        > ∨il
        ∣ qr ∷ ql ∷ ps ⊢ ql ∧s qr
          >> ∧i
          ∣ qr ∷ ql ∷ ps ⊢ ql
            > weaken (singleton-⊆ (there (here refl)))
            ∣ [ ql ] ⊢ ql
              - var
          ∣ qr ∷ ql ∷ ps ⊢ qr
            > weaken (singleton-⊆ (here refl))
            ∣ [ qr ] ⊢ qr
              - var
      ∣ ⋁ qs ∷ ql ∷ ps ⊢ (ql ∧s qr) ∨s ⋁ qs
        > weaken (singleton-⊆ (here refl))
        ∣ [ ⋁ qs ] ⊢ (ql ∧s qr) ∨s ⋁ qs
          > ∨ir
          ∣ [ ⋁ qs ] ⊢ ⋁ qs
            - var
      ∣ ql ∷ ps ⊢ qr ∨s ⋁ qs
        > weaken there
        ∣ ps ⊢ qr ∨s ⋁ qs
          - seq→nd rt
    ∣ ⋁ qs ∷ ps ⊢ (ql ∧s qr) ∨s ⋁ qs
      > weaken (singleton-⊆ (here refl))
      ∣ [ ⋁ qs ] ⊢ (ql ∧s qr) ∨s ⋁ qs
        > ∨ir
        ∣ [ ⋁ qs ] ⊢ ⋁ qs
          - var
    ∣ ps ⊢ ql ∨s ⋁ qs
      - seq→nd lt
seq→nd (→l {p} {ps} {q} {qs} qt t) =
  ∣ q →s p ∷ ps ⊢ ⋁ qs
    >>> ∨e
    ∣ q ∷ q →s p ∷ ps ⊢ ⋁ qs
      >> →e
      ∣ q ∷ q →s p ∷ ps ⊢ p →s ⋁ qs
        > weaken (there ∘ there)
        ∣ ps ⊢ p →s ⋁ qs
          > →i
          ∣ p ∷ ps ⊢ ⋁ qs
            - seq→nd t
      ∣ q ∷ q →s p ∷ ps ⊢ p
        >> →e
        ∣ q ∷ q →s p ∷ ps ⊢ q →s p
          > weaken (singleton-⊆ (there (here refl)))
          ∣ [ q →s p ] ⊢ q →s p
            - var
        ∣ q ∷ q →s p ∷ ps ⊢ q
          > weaken (singleton-⊆ (here refl))
          ∣ [ q ] ⊢ q
            - var
    ∣ ⋁ qs ∷ q →s p ∷ ps ⊢ ⋁ qs
      > weaken (singleton-⊆ (here refl))
      ∣ [ ⋁ qs ] ⊢ ⋁ qs
        - var
    ∣ q →s p ∷ ps ⊢ q ∨s ⋁ qs
      > weaken there
      ∣ ps ⊢ q ∨s ⋁ qs
        - seq→nd qt
seq→nd (→r {p} {ps} {q} {qs} t) =
  ∣ ps ⊢ (p →s q) ∨s ⋁ qs
    >>> ∨e
    ∣ p ∷ ps ⊢ (p →s q) ∨s ⋁ qs
      >>> ∨e
      ∣ q ∷ p ∷ ps ⊢ (p →s q) ∨s ⋁ qs
        > ∨il
        ∣ q ∷ p ∷ ps ⊢ p →s q
          > →i
          ∣ p ∷ q ∷ p ∷ ps ⊢ q
            > weaken (singleton-⊆ (there (here refl)))
            ∣ [ q ] ⊢ q
              - var
      ∣ ⋁ qs ∷ p ∷ ps ⊢ (p →s q) ∨s ⋁ qs
        > ∨ir
        ∣ ⋁ qs ∷ p ∷ ps ⊢ ⋁ qs
          > weaken (singleton-⊆ (here refl))
          ∣ [ ⋁ qs ] ⊢ ⋁ qs
            - var
      ∣ p ∷ ps ⊢ q ∨s ⋁ qs
        - seq→nd t
    ∣ ¬s p ∷ ps ⊢ (p →s q) ∨s ⋁ qs
      > ∨il
      ∣ ¬s p ∷ ps ⊢ p →s q
        > →i
        ∣ p ∷ ¬s p ∷ ps ⊢ q
          >> →e
          ∣ p ∷ ¬s p ∷ ps ⊢ ⊥s →s q
            > weaken (λ ())
            ∣ [] ⊢ ⊥s →s q
              > →i
              ∣ [ ⊥s ] ⊢ q
                > ⊥e
                ∣ [ ⊥s ] ⊢ ⊥s
                  - var
          ∣ p ∷ ¬s p ∷ ps ⊢ ⊥s
            >> →e
            ∣ p ∷ ¬s p ∷ ps ⊢ ¬s p
              > weaken (singleton-⊆ (there (here refl)))
              ∣ [ ¬s p ] ⊢ ¬s p
                - var
            ∣ p ∷ ¬s p ∷ ps ⊢ p
              > weaken (singleton-⊆ (here refl))
              ∣ [ p ] ⊢ p
                - var
    ∣ ps ⊢ p ∨s ¬s p
      > weaken (λ ())
      ∣ [] ⊢ p ∨s ¬s p
        - lem-nd p
seq→nd (weaken {ps} {ps′} {qs} {qs′} psps qsqs t) =
  ∣ ps′ ⊢ ⋁ qs′
    > weaken psps
    ∣ ps ⊢ ⋁ qs′
      >> →e
      ∣ ps ⊢ ⋁ qs →s ⋁ qs′
        > weaken (λ ())
        ∣ [] ⊢ ⋁ qs →s ⋁ qs′
          > →i
          ∣ [ ⋁ qs ] ⊢ ⋁ qs′
            - weakening-⊢ qsqs
      ∣ ps ⊢ ⋁ qs
        - seq→nd t
seq→nd (cut {ps} q {rs} ptq qtr) =
  ∣ ps ⊢ ⋁ rs
    >>> ∨e
    ∣ q ∷ ps ⊢ ⋁ rs
      - seq→nd qtr
    ∣ ⋁ rs ∷ ps ⊢ ⋁ rs
      > weaken (singleton-⊆ (here refl))
      ∣ [ ⋁ rs ] ⊢ ⋁ rs
        - var
    ∣ ps ⊢ q ∨s ⋁ rs
      - seq→nd ptq
