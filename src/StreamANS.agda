{-# OPTIONS --guardedness #-}
module StreamANS where

open import Range
open import Util
open import Stream
open import OrdLemmas

open import Flipper
open import Flipper.Prelude
open import Prelude hiding (Fin; flip; _<>_; id)
open import Tactic.Nat

module Messages (base : Nat){{_ : IsTrue (2 ≤? base)}} where
  open import Logarithm base

  Message : Nat -> Set
  Message a = Range a (base * a) × Stream (Fin base)

  private
    variable
      a b : Nat

    refocus-step : Message a <-> Message (base * a)
    refocus-step = F \
      { (h , ts) -> ts      ⟨ uncons     ⟩ \ { (t , ts) -> 
                    (h , t) ⟨ scale base ⟩ \ { h        -> h , ts } }
      }

    =F=M : a ≡ b -> Message a <-> Message b
    =F=M refl = id

    refocus-part1 : ∀ n -> Message a <-> Message (base ^ n * a)
    refocus-part1 zero    = =F=M auto
    refocus-part1 (suc n) = refocus-part1 n <> refocus-step <> =F=M auto

    refocus-part2 : ∀ {a b} -> a ≤ b -> b ≤ base * a -> Message a <-> Message b
    refocus-part2 {a} {b} lb ub = (F \
      { (h , ts) → h ⟨ split b lb ub ⟩ \ { h -> h , ts } })
        <> (F \
      { ((h /  ) , ts) → ts      ⟨ uncons     ⟩ \ { (t , ts) -> 
                         (h , t) ⟨ scale base ⟩ \ { h        -> ((  / h) , ts) } }
      ; ((  / h) , ts) →                                        ((h /  ) , ts) })
        <> F \
      { (h , ts) → h ⟨ unSplit (base * a) ub (≤-mono a b base lb) ⟩ \ { h -> h , ts } }

    refocus-up : ∀ {a b} -> {{NonZero a}} -> a < b ->  
      Message a <-> Message b
    refocus-up {a} {b} a<b with log a b (by a<b)
    ... | lg n lb ub = refocus-part1 n <> refocus-part2 lb (by ub)

    tailZero : Fin base
    tailZero = helper
      where
      helper : ∀ {base} -> {{IsTrue (2 ≤? base)}} -> Fin base
      helper {suc base} = zero [[ diff! 0 , auto ]]

  refocus : ∀ {a b} -> {{NonZero a}} -> {{NonZero b}} ->
    Message a <-> Message b
  refocus {a} {b} with compare a b
  ... | less    lt   = refocus-up lt
  ... | equal   refl = id
  ... | greater gt   = flip (refocus-up gt)

  emptyMsg : ∀ {a} -> {{NonZero a}} -> Message a
  emptyMsg {a} = (a [[ (diff! zero) , less-mul-l' a base ]]) , repeat tailZero
open Messages (2 ^ 8)

m : Message (2 ^ 32)
m = emptyMsg

m2 : Message (2 ^ 64)
m2 = apply refocus m
