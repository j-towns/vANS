module Sum where

open import Flipper
open import Prelude


_⊎_ : {a b : Level} → Set a → Set b → Set (a ⊔ b)
A ⊎ B = Either A B
infixr 1 _⊎_

pattern _/ x = left x
pattern /_ x = right x
infixr 0 _/
infixr -1 /_

_<+>_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> A ⊎ B <-> C ⊎ D
f <+> g = F λ where
  (a /  ) → a ⟨ f ⟩ λ { c → (c /  ) }
  (  / b) → b ⟨ g ⟩ λ { d → (  / d) }
  
infix 1 _<+>_

_->>_ : Set -> Set -> Set₁
A ->> B = ∃ C , A ⊎ C <-> B

applyP : ∀ {A B} -> (A ->> B) -> A -> B
applyP f a = apply (snd f) (a /  )

unapplyP : ∀ {A B} -> (A ->> B) -> B -> Maybe A
unapplyP f b with unapply (snd f) b
... | a /   = just a
... |   / _ = nothing
