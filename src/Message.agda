open import Prelude hiding (Fin; id; _<>_; flip)
open import Tactic.Nat
open import Flipper
open import Flipper.Prelude
open import Range
open import Sum
open import OrdLemmas

module Message (base : Nat){{_ : IsTrue (2 ≤? base)}} where
open import Logarithm base

private
  Message' : Nat → Set
  Message' a = Range a (base * a) × List (Fin base)

Message : Nat → Set
Message a = Message' a ⊎ Fin a

private
  instance
    baseNZ : NonZero base
    baseNZ = helper base where
      helper : ∀ base → {{IsTrue (2 ≤? base)}} → NonZero base
      helper (suc base) = unit

  1≤base : 1 ≤ base
  1≤base = helper base
    where
    helper : ∀ b → {{IsTrue (2 ≤? b)}} → 1 ≤ b
    helper zero    {{ () }}
    helper (suc b) {{ 2≤baseTrue }} = auto

  a≤base*a : ∀ {a} → a ≤ base * a
  a≤base*a {a} = leq-mul-l a base

  refocus-step : ∀ {a} → Message a <-> Message (base * a)
  refocus-step {a} = F (λ where
    (m , []     /  ) → (           /   / m)
    (h , t ∷ ts /  ) → (h , t , ts /      )
    (           / m) → (           / m /  ))
    <> ((F λ where
    (h , t , ts) → (h , t) ⟨ scale base    ⟩ λ { h →
                   h       ⟨ =R= refl auto ⟩ λ { h → (h , ts) } })
    <+> unSplitFin a a≤base*a)

  =M= : ∀ {a b} → a ≡ b → Message a <-> Message b
  =M= refl = id

  refocus-part1 : ∀ {a} n → Message a <-> Message (base ^ n * a)
  refocus-part1 zero    = =M= auto
  refocus-part1 (suc n) =
    refocus-part1 n <> refocus-step <> =M= auto

  refocus-part2 : ∀ {a a'} → a ≤ a' → a' ≤ base * a
    → Message a <-> Message a'
  refocus-part2 {a} {a'} lb ub = F (λ where
    (h , ts /  ) → h ⟨ split a' lb ub ⟩ λ { h → (h , ts /  ) }
    (       / h) →                              (       / h) )
    <>
    (F λ where
    ((h /  ) , []     /  ) → (                 /   / h)
    ((h /  ) , t ∷ ts /  ) → ((  / h , t) , ts /      )
    ((  / h) , ts     /  ) → ((h /      ) , ts /      )
    (                 / h) → (                 / h /  ))
    < (_ × List (Fin base) ⊎ _) >
    ((F λ where
    ((  / h , t) , ts) → (h , t) ⟨ scale base ⟩ λ { h → (  / h) , ts }
    ((h /      ) , ts) →                                (h /  ) , ts )
    <> (F λ where
    (h , ts) → h ⟨ unSplit (base * a) ub lb' ⟩ λ { h → (h , ts) })
    <+> unSplitFin a lb)
    where
    lb' : base * a ≤ base * a'
    lb' = ≤-mono base lb

  refocus-up : ∀ {a a'} → {{NonZero a}} → a < a' →
    Message a <-> Message a'
  refocus-up {a} {a'} a<a' with log a a' (by a<a')
  ... | lg n lb ub = refocus-part1 n <> refocus-part2 lb (by ub)

refocus : ∀ {a a'} → {{aNZ : NonZero a}} → {{a'NZ : NonZero a'}} →
  Message a <-> Message a'
refocus {a} {a'} with compare a a'
... | less    a<a' = refocus-up a<a'
... | equal   refl = id
... | greater a>a' = flip (refocus-up a>a')

normalize : {a : Nat} → {{NonZero a}} → Message a <-> Message 1
normalize = refocus

zeroMessage : ∀ {a : Nat} → {{NonZero a}} → Message a
zeroMessage {suc a} = right (zero [[ (diff! zero) , (diff a auto) ]])

isZeroMessage : ∀ {a : Nat} → {{NonZero a}} → Message a → Bool
isZeroMessage {suc a} (m /                    ) = false
isZeroMessage {suc a} (  / (zero  [[ _ , _ ]])) = true
isZeroMessage {suc a} (  / (suc n [[ _ , _ ]])) = false

flatten : Message 1 ->> List (Fin base)
flatten = List (Fin base) , (part1 <> part2)
  where
  part1 : Message 1 ⊎ List (Fin base) <-> ⊤ ⊎ ((Fin 1 ⊎ Range 1 base) × List (Fin base))
  part1 = F λ where
    ((h , ts /  ) /   ) → h    ⟨ =R= refl auto ⟩ λ { h →   / (  / h) , ts }
    ((       / h) /   ) → h    ⟨ fin1Unit      ⟩ λ { h → h /              }
    (             / ts) → unit ⟨ flip fin1Unit ⟩ λ { h →   / (h /  ) , ts }

  part2 : ⊤ ⊎ ((Fin 1 ⊎ Range 1 base) × List (Fin base)) <-> List (Fin base)
  part2 = F λ where
    (unit /       ) → []
    (     / h , ts) → h ⟨ unSplit 1 (diff! 1) 1≤base ⟩ λ { h → h ∷ ts }
