open import Prelude
open import Tactic.Nat using (by; auto; refute)
open import Prelude.Ord.Properties
open import Numeric.Nat.Properties using (sub-less)


≤-mono : {a b : Nat}(c : Nat) → a ≤ b → c * a ≤ c * b
≤-mono         zero    a≤b = diff! zero
≤-mono {a} {b} (suc c) a≤b = ordProof
    a + c * a ≤[ by a≤b ] b + c * a ≤[ by (≤-mono c a≤b) ] b + c * b
  ∎Ord

<-mono-contra : {a b : Nat}(c : Nat) → c * a > c * b → a > b
<-mono-contra c cb<ca = ≰⇒> \ a≤b → <⇒≱ cb<ca (≤-mono c a≤b)

<-mono : {a b c d : Nat} → d < b → c < a → b * c + d < b * a
<-mono {a} {b} {c} {d} d<b c<a =
  ordProof 
    b * c + d
  <[ by d<b ]
    b * c + b
  ≡[ auto ]
    b * suc c
  ≤[ ≤-mono b (suc-monotone c<a)  ]
    b * a
  ∎Ord 

≤-mono-contra : {a b c d : Nat} → d < b → b * c + d ≥ b * a → c ≥ a
≤-mono-contra d<b ab≤cb+d = ≮⇒≥ \ c<a → <⇒≱ (<-mono d<b c<a) ab≤cb+d

 -- Adapted from agda-prelude
less-mul-l : (a b : Nat) → {{NonZero a}} → {{2 ≤ b}} → a < a * b
less-mul-l (suc a) 0 ⦃ _ ⦄ ⦃ 0>1 ⦄ = refute 0>1
less-mul-l (suc a) 1 ⦃ _ ⦄ ⦃ 1>1 ⦄ = refute 1>1
less-mul-l (suc a) (suc (suc b)) ⦃ _ ⦄ ⦃ diff k eq ⦄ = auto

less-mul-l' : ∀ a b → {{NonZero a}} → {{IsTrue (2 ≤? b)}} → a < b * a
less-mul-l' (suc a) (suc (suc b)) = auto

leq-mul-l : (a b : Nat) → {{NonZero b}} → a ≤ b * a
leq-mul-l a (suc b) = auto

 -- Generalizations of inv-suc-monotone
<-minus-mono : {a b c : Nat} → a ≤ b → b < a + c → b - a < c
<-minus-mono {zero}  {b}     {c} a≤b            b<c   = b<c
<-minus-mono {suc a} {zero}  {c} (diff zero ()) 0≤a+c
<-minus-mono {suc a} {suc b} {c} a≤b            b<a+c =
  <-minus-mono (inv-suc-monotone a≤b) (inv-suc-monotone b<a+c)

≤-minus-mono : {a b c : Nat} → b + a ≤ c → a ≤ c - b
≤-minus-mono {a} {zero}  {c}     b+a≤c          = b+a≤c
≤-minus-mono {a} {suc b} {zero}  (diff zero ())
≤-minus-mono {a} {suc b} {suc c} b+a≤c          =
  ≤-minus-mono (inv-suc-monotone b+a≤c)

data LT {A : Set}{{_ : Ord A}}(a b : A) : Set where
  lt : a < b → LT a b
  ge : a ≥ b → LT a b

_<-dec'_ : ∀ {A : Set}{{_ : Ord/Laws A}}(a b : A) → LT a b
a <-dec' b with a <-dec b
... | yes a<b = lt a<b
... | no  a≮b = ge (≮⇒≥ a≮b)

infix 4 _<-dec'_
  
