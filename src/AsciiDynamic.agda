open import Prelude hiding (Fin; _<>_)
open import Flipper.Prelude

open import Sum
open import Ascii
open import Trees
open import NatPlus
open import ANS using (Dist)
open import Range

 -- Extra symbol for EOF
Ascii' : Set
Ascii' = ⊤ ⊎ Ascii

asciiFTree : FTree 0 asciiBTree
asciiFTree = zer



