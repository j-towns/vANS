module NatPlus where

open import Prelude


record Nat+ : Set where
  constructor [_]+
  field
    n : Nat
    {{nNZ}} : NonZero n
