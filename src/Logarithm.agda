open import Prelude
open import Prelude.Ord.Properties
open import Control.WellFounded
open import Numeric.Nat.Properties
open import Tactic.Nat

open import OrdLemmas using (<-minus-mono; _<-dec'_; lt; ge)


module Logarithm (base : Nat){{_ : IsTrue (2 ≤? base)}} where

private
  baseNZAux : ∀ base → {{IsTrue (2 ≤? base)}} → NonZero base
  baseNZAux (suc base) = unit

  instance
    baseNZ : NonZero base
    baseNZ = baseNZAux base
  
  NZ⇒>0 : ∀ a {{_ : NonZero a}} → a > 0
  NZ⇒>0 (suc a) = auto
  
  wf-helper : ∀ {a b} base {{_ : IsTrue (2 ≤? base)}}{{_ : NonZero a}}
    → a ≤ b → base * a ≤ b → b - base * a < b - a
  wf-helper {a} {b} (suc (suc base)) a≤b base*a≤b =
    <-minus-mono base*a≤b (
      ordProof
        b
      ≡[ by (sub-less a≤b) ]
        a + (b - a)
      <[ by (NZ⇒>0 a)  ]
        a + (a + base * a) + (b - a)
      ∎Ord) 
  
 -- Analogous to log_{base} (b / a)
data Log (a b : Nat) : Set where
  lg : ∀ n → base ^ n * a ≤ b → b < base ^ (1 + n) * a → Log a b
  
private
  logAux : ∀ a b → {{NonZero a}} → Acc _<_ (b - a) → a ≤ b → Log a b
  logAux a b wf       a≤b with b <-dec' base * a
  logAux a b wf       a≤b | lt b<base*a = lg 0 (by a≤b) (by b<base*a)
  logAux a b (acc wf) a≤b | ge base*a≤b with logAux
    (base * a) b {{mul-nonzero base a}}
    (wf (b - base * a) (wf-helper base a≤b base*a≤b)) base*a≤b
  ... | lg n lb ub = lg (1 + n) (by lb) (by ub)

log : ∀ a b → {{NonZero a}} → a ≤ b → Log a b
log a b a≤b = logAux a b (wfNat (b - a)) a≤b
