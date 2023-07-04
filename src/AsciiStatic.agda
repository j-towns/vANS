open import Prelude hiding (Fin; _<>_)
open import Flipper.Prelude

open import Sum
open import Ascii
open import Trees
open import NatPlus
open import ANS using (Dist)
open import Range

private
   -- Extra symbol for EOF
  Ascii' : Set
  Ascii' = ⊤ ⊎ Ascii

   -- Frequencies in the complete works of Shakespeare
  ascii-mass' : Ascii' -> Nat
  ascii-mass' = λ where
    (left unit)                                             → 1
    (right (<0> (<0> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → 124456
    (right (<0> (<0> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → 1
    (right (<0> (<0> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<1> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → 1293934
    (right (<0> (<1> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → 8844
    (right (<0> (<1> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → 470
    (right (<0> (<1> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<1> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → 1
    (right (<0> (<1> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<1> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → 21
    (right (<0> (<1> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → 31069
    (right (<0> (<1> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → 628
    (right (<0> (<1> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → 629
    (right (<0> (<1> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → 63
    (right (<0> (<1> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → 1
    (right (<0> (<1> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → 83174
    (right (<0> (<1> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → 8074
    (right (<0> (<1> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → 78025
    (right (<0> (<1> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → 5
    (right (<0> (<1> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → 299
    (right (<0> (<1> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → 928
    (right (<0> (<1> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → 366
    (right (<0> (<1> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → 330
    (right (<0> (<1> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → 93
    (right (<0> (<1> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → 82
    (right (<0> (<1> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → 63
    (right (<0> (<1> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → 41
    (right (<0> (<1> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → 40
    (right (<0> (<1> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → 948
    (right (<0> (<1> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → 1827
    (right (<0> (<1> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → 17199
    (right (<0> (<1> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → 468
    (right (<0> (<1> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → 1
    (right (<0> (<1> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → 441
    (right (<0> (<1> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → 10476
    (right (<1> (<0> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → 8
    (right (<1> (<0> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → 44486
    (right (<1> (<0> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → 15413
    (right (<1> (<0> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → 21497
    (right (<1> (<0> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → 15683
    (right (<1> (<0> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → 42583
    (right (<1> (<0> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → 11713
    (right (<1> (<0> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → 11164
    (right (<1> (<0> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → 18462
    (right (<1> (<0> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → 55806
    (right (<1> (<0> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → 2067
    (right (<1> (<0> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → 6196
    (right (<1> (<0> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → 23858
    (right (<1> (<0> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → 15872
    (right (<1> (<0> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → 27338
    (right (<1> (<0> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → 33209
    (right (<1> (<0> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → 11939
    (right (<1> (<0> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → 1178
    (right (<1> (<0> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → 28970
    (right (<1> (<0> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → 34011
    (right (<1> (<0> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → 39800
    (right (<1> (<0> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → 14129
    (right (<1> (<0> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → 3580
    (right (<1> (<0> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → 16496
    (right (<1> (<0> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → 606
    (right (<1> (<0> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → 9099
    (right (<1> (<0> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → 532
    (right (<1> (<0> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → 2085
    (right (<1> (<0> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → 1
    (right (<1> (<0> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → 2077
    (right (<1> (<0> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → 1
    (right (<1> (<0> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → 71
    (right (<1> (<1> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → 1
    (right (<1> (<1> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → 244664
    (right (<1> (<1> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → 46543
    (right (<1> (<1> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → 66688
    (right (<1> (<1> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → 133779
    (right (<1> (<1> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → 404621
    (right (<1> (<1> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → 68803
    (right (<1> (<1> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → 57035
    (right (<1> (<1> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → 218406
    (right (<1> (<1> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → 198184
    (right (<1> (<1> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → 2712
    (right (<1> (<1> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → 29212
    (right (<1> (<1> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → 146161
    (right (<1> (<1> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → 95580
    (right (<1> (<1> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → 215924
    (right (<1> (<1> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → 281391
    (right (<1> (<1> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → 46525
    (right (<1> (<1> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → 2404
    (right (<1> (<1> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → 208894
    (right (<1> (<1> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → 214978
    (right (<1> (<1> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → 289975
    (right (<1> (<1> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → 114818
    (right (<1> (<1> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → 33989
    (right (<1> (<1> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → 72894
    (right (<1> (<1> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → 4688
    (right (<1> (<1> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → 85271
    (right (<1> (<1> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → 1099
    (right (<1> (<1> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → 1
    (right (<1> (<1> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → 33
    (right (<1> (<1> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → 2
    (right (<1> (<1> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → 1
    (right (<1> (<1> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → 1

   -- Sum of the masses
  N : Nat
  N = 5458236

  asciiFTree : FTree N asciiBTree
  asciiFTree = snd (fromMass asciiBTree (ascii-mass' ∘ right))

  asciiMassNZ : ∀ (a : Ascii')
    → NonZero (either (const 1) (weight asciiFTree) a)
  asciiMassNZ = λ where
    (left unit)                                             → unit
    (right (<0> (<0> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<0> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<0> (<1> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<0> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<0> (<1> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<0> (<1> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<0> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<0> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<0> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<0> (<1> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<1> (<0> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<1> (<0> (<1> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<1> (<1> (<0> <end>)))))))) → unit
    (right (<1> (<1> (<1> (<1> (<1> (<1> (<1> <end>)))))))) → unit

  asciiMass : Ascii' → Nat+
  asciiMass a =
    [_]+ (either (const 1) (weight asciiFTree) a) {{asciiMassNZ a}}

  asciiDist : Dist (suc N) (Nat+.n ∘ asciiMass)
  asciiDist = split' (2-comp 1 N refl) <> F λ where
    (x /  ) → (left unit) , x  -- <- this is a bit of a hack :)
    (  / x) → x ⟨ ft-lookup asciiFTree ⟩ λ { (c , cMass) → (right c) , cMass }

  ransL : Nat
  ransL = 2 ^ 56

  ransLdivN : Nat
  ransLdivN = ransL div N

  base : Nat
  base = 2 ^ 8

  open ANS.Decode (suc N) base ransL asciiMass asciiDist

  Message' : Set
  Message' = Message ransL

  {-# TERMINATING #-}
  asciiDecode' : Message' <-> Message' × List Ascii
  asciiDecode' = decode ransLdivN <> F λ where
    (m , (unit /  )) →                                   m , []
    (m , (     / x)) → m ⟨ asciiDecode' ⟩ λ { (m , xs) → m , x ∷ xs }

  asciiDecode : Message 1 <-> Message 1 × List Ascii
  asciiDecode = refocus < Message' > asciiDecode' <> F λ where
    (m , xs) → m ⟨ refocus ⟩ λ { m → m , xs }

asciiEnc : List Ascii → List Byte
asciiEnc xs = applyP flatten (unapply asciiDecode (zeroMessage , xs))

asciiDec : List Byte → Maybe (List Ascii)
asciiDec bs = do
  m ← unapplyP flatten bs
  let zeroM , xs = apply asciiDecode m
  if (isZeroMessage zeroM) then (pure xs) else nothing
