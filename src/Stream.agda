{-# OPTIONS --guardedness #-}
module Stream where

open import Prelude hiding (flip)
open import Flipper

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : Stream A
open Stream

variable
  A : Set
  
private
  record _≈_ (xs ys : Stream A) : Set where
    coinductive
    field
      ≈head : xs .hd ≡ ys .hd
      ≈tail : xs .tl ≈ ys .tl
  open _≈_
  
  ≈-refl : (xs : Stream A) → xs ≈ xs
  ≈head (≈-refl xs) = refl
  ≈tail (≈-refl xs) = ≈-refl (tl xs)
  
  prop : (xs : Stream A) → (hd xs ∷ tl xs) ≈ xs
  ≈head (prop xs) = refl
  ≈tail (prop xs) = ≈-refl (tl xs)
  
  postulate
    bisim : ∀ {xs ys : Stream A} → xs ≈ ys → xs ≡ ys
  
  ∷-inj : forall {y : A} {xs ys : Stream A} → hd xs ≡ y → tl xs ≡ ys → y ∷ ys ≡ xs
  ∷-inj refl refl = bisim (prop _)

cons : A × Stream A <-> Stream A
cons = MkF a u lemma₂ lemma₁ where
  a : A × Stream A → Stream A
  a (x , xs) = x ∷ xs

  u : Stream A → A × Stream A
  u xs = (hd xs , tl xs)

  lemma₁ : (xs : Stream A) → a (u xs) ≡ xs
  lemma₁ xs = bisim (prop xs) 

  lemma₂ : (x,xs : A × Stream A) → u (a x,xs) ≡ x,xs
  lemma₂ (x , xs) = refl

uncons : Stream A <-> A × Stream A
uncons = flip cons

repeat : ∀ {A} -> A -> Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

instance
  ShowStream : ∀ {A} -> Show (Stream A)
  ShowStream = simpleShowInstance (const "[...]")
