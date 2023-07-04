module ANS where

open import Prelude hiding (Fin; _<>_; flip; id; lookup)
open import Numeric.Nat.Properties using (mul-nonzero)
open import Tactic.Nat using (auto)

open import Sum
open import OrdLemmas
open import Range
open import NatPlus
open import Flipper
open import Flipper.Prelude


Dist : {A : Set} → Nat → (A → Nat) → Set
Dist {A} N mass = Fin N <-> Σ A (Fin ∘ mass)


private
  rangeDecode : ∀ {A} N mass → Dist N mass → ∀ a b →
    Range (N * a) (N * b) <-> Σ A λ x → Range (mass x * a) (mass x * b)
  rangeDecode N mass lookup _ _ = F λ where
    h → h       ⟨ unScale N      ⟩ λ { (h , i) →
        i       ⟨ lookup         ⟩ λ { (x , i) →
        (h , i) ⟨ scale (mass x) ⟩ λ { h       → (x , h) } } }

module Decode {A : Set}(N base a : Nat)(mass' : A -> Nat+)
  (lookup : Dist N (Nat+.n ∘ mass')){{_ : IsTrue (2 ≤? base)}}
  {{_ : NonZero a}}{{_ : NonZero N}} where

  open import Message base public

  private
    mass : A -> Nat
    mass = Nat+.n ∘ mass'

    rangeDecode' = rangeDecode N mass lookup

    decode' : ∀ k -> Message (N * k) <-> Σ A λ x -> Message (mass x * k)
    decode' k = F λ where
      (h , t /  ) → h ⟨ =R= refl auto             ⟩ λ { h       →
                    h ⟨ rangeDecode' k (base * k) ⟩ λ { (x , h) →
                    h ⟨ =R= refl auto             ⟩ λ { h       → x , (h , t /  ) } } }
      (      / h) → h ⟨ =R= auto refl             ⟩ λ { h       →
                    h ⟨ rangeDecode' 0 k          ⟩ λ { (x , h) →
                    h ⟨ =R= auto refl             ⟩ λ { h       → x , (      / h) } } }

  decode : ∀ k -> {{NonZero k}} -> Message a <-> Message a × A
  decode k = (refocus {{a'NZ = mul-nonzero N k}}) <> decode' k <> (
    F λ { (x , m) → m ⟨ refocus {{aNZ = massx*nNZ x}} ⟩ λ { m → (m , x) }})
    where
    massx*nNZ : ∀ x -> NonZero (mass x * k)
    massx*nNZ x with mass' x
    ... | [ massx ]+ = mul-nonzero massx k
