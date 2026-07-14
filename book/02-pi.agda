{-# OPTIONS --without-K --exact-split --safe #-}

module book.02-pi where

import book.00-preamble
open book.00-preamble public

--------------------------------------------------------------------------------

--id_A type
id : {i : Level} {A : UU i} → A → A
id x = x

-- Definition 2.2.5
_∘_ :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B → C) → ((A → B) → (A → C))
(g ∘ f) a = g (f a)

-- Lemma 2.2.6 Composition is associate. That is, (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
---- We use the identity type that we planted in the preamble instead ----
associative-comp :
  {i j k l : Level} {A : UU i} {B : UU j} {C : UU k} {D : UU l} →
  (h : C → D) (g : B → C) (f : A → B) →
  (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
associative-comp h g f = refl
--------------------------------------------------------------------------------

-- Lemma 2.2.7 left and right unit laws
leftunit-comp : {i j : Level} {A : UU i} {B : UU j} →
  (f : A → B) →
  (id {j} {B} ∘ f) ≡ f
leftunit-comp f = refl

rightunit-comp : {i j : Level} {A : UU i} {B : UU j} →
  (f : A → B) →
  (f ∘ id {i} {A}) ≡ f
rightunit-comp f = refl

-- Exercise 2.3
const : {i j : Level} (A : UU i) (B : UU j) (y : B) → A → B
const A B y x = y

-- Exercise 2.4 (a)
Π-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
Π-swap f y x = f x y

-- Exercise 2.4 (b)
Π-swap-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
 (f : (x : A) (y : B) → C x y) →
 (Π-swap (Π-swap f)) ≡ f
Π-swap-swap f = refl