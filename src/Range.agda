module Range where

open import Prelude hiding (Fin; flip; _<>_; id)
open import Tactic.Nat using (by; auto; refute)
open import Flipper
open import Flipper.Prelude
open import Prelude.Ord.Properties
open import Numeric.Nat.Properties
open import Numeric.Nat.DivMod

open import OrdLemmas
open import Sum


 -- Equivalent to [a , b), or {a, a + 1, ..., b - 1}
record Range (a b : Nat) : Set where
  constructor _[[_,_]]
  field
    n   : Nat
    a≤n : a ≤ n
    n<b : n < b

Fin : Nat → Set
Fin = Range 0

Byte : Set
Byte = Fin 256

rangeToNat : ∀ {a b} → Range a b → Nat
rangeToNat = Range.n

InRange : Nat → Nat → Nat → Set
InRange a b n = IsTrue (a <? suc n && n <? b)

natToRange : ∀ {a b} n → {{InRange a b n}} → Range a b
natToRange {a} {b} n with compare a (suc n) | compare n b
... | less a≤n | less n<b = n [[ a≤n , n<b ]]

instance
  ShowRange : ∀ {a b} → Show (Range a b)
  ShowRange = simpleShowInstance (show ∘ rangeToNat)

≡-Range : ∀ {a b}{x y : Range a b}
  → rangeToNat x ≡ rangeToNat y → x ≡ y
≡-Range {_} {_} {x [[ _ , _ ]]} {.x [[ _ , _ ]]} refl =
  cong₂ (x [[_,_]]) smashed smashed

move : ∀ {a b} c → Range a b <-> Range (c + a) (c + b)
split : ∀ {a c} b → a ≤ b → b ≤ c
  → Range a c <-> Range a b ⊎ Range b c
scale : ∀ {a b} c → Range a b × Fin c <-> Range (c * a) (c * b)

move {a} {b} c = MkF ap unap unapap apunap
  where
  ap : Range a b → Range (c + a) (c + b)
  ap (n [[ a≤n , n<b ]]) = (c + n) [[ by a≤n , by n<b ]]

  unap :  Range (c + a) (c + b) → Range a b
  unap (c+n [[ c+a≤c+n , c+n<c+b ]]) =
    (c+n - c) [[ ≤-minus-mono c+a≤c+n ,
                 <-minus-mono (by c+a≤c+n) c+n<c+b ]]

  unapap : ∀ n → unap (ap n) ≡ n
  unapap n = ≡-Range auto

  apunap : ∀ c+n → ap (unap c+n) ≡ c+n
  apunap (c+n [[ c+a≤c+n , _ ]]) =
    ≡-Range (by (sub-less {a = c} {b = c+n} (by c+a≤c+n)))

split {a} {c} b a≤b b≤c = MkF ap unap ua au
  where
  ap : Range a c → Range a b ⊎ Range b c
  ap (n [[ a≤n , n<c ]]) with n <-dec b
  ... | yes n<b = left  (n [[ a≤n       , n<b ]])
  ... | no  n≮b = right (n [[ (≮⇒≥ n≮b) , n<c ]])

  unap : Range a b ⊎ Range b c → Range a c
  unap (left  (n [[ a≤n , n<b ]])) =
    n [[ a≤n , ordProof n <[ n<b ] b ≤[ b≤c ] c ∎Ord ]]
  unap (right (n [[ b≤n , n<c ]])) = n [[ leq-trans a≤b b≤n , n<c ]]

  ua : (n : Range a c) → unap (ap n) ≡ n
  ua (n [[ a≤n , n<c ]]) with n <-dec b
  ... | yes n<b = ≡-Range refl
  ... | no  n≮b = ≡-Range refl

  au : (n : Range a b ⊎ Range b c) → ap (unap n) ≡ n
  au (left (n [[ a≤n , n<b ]])) with n <-dec b
  ... | yes n<b = cong left (≡-Range refl)
  ... | no  n≮b with n≮b n<b
  ...   | ()
  au (right (n [[ b≤n , n<c ]])) with n <-dec b
  au (right (n [[ b≤n , n<c ]])) | yes n<b with leq-less-antisym b≤n n<b
  au (right (n [[ b≤n , n<c ]])) | yes n<b | ()
  au (right (n [[ b≤n , n<c ]])) | no  n≮b = cong right (≡-Range refl)

scale zero = MkF
  (\ { (_ , (_ [[ _ , diff _ () ]])) })
  (\ { (_ [[ _ , diff _ () ]]) })
  (\ { (_ , (_ [[ _ , diff _ () ]])) })
  (\ { (_ [[ _ , diff _ () ]]) })
scale {a} {b} (suc c) =
  MkF (ap (suc c)) (unap (suc c)) (ua (suc c)) (au (suc c))
  where
  ap : ∀ c → {{NonZero c}}
    → Range a b × Fin c → Range (c * a) (c * b)
  ap c ((q [[ a≤q , q<b ]]) , (r [[ _ , r<c ]])) =
    (c * q + r) [[ by (≤-mono c a≤q) , <-mono r<c q<b ]]

  unap : ∀ c → {{NonZero c}} → Range (c * a) (c * b)
    → Range a b × Fin c
  unap c (n [[ c*a≤n , n<c*b ]]) with n divmod c
  ... | qr q r r<c eq =
    (q [[ ≤-mono-contra r<c c*a≤c*q+r , <-mono-contra c c*q<c*b ]]) ,
    (r [[ auto , r<c ]])
    where
    c*a≤c*q+r : c * a ≤ c * q + r
    c*a≤c*q+r = ordProof c * a ≤[ c*a≤n ] n ≡[ by eq ] c * q + r ∎Ord

    c*q<c*b : c * q < c * b
    c*q<c*b = ordProof
      c * q ≤[ auto ] q * c + r ≡[ eq ] n <[ n<c*b ] c * b ∎Ord

  ua : ∀ c → {{_ : NonZero c}} → ∀ qr → unap c (ap c qr) ≡ qr
  ua c ((q [[ _ , _ ]]) , (r [[ _ , r<c ]])) with (c * q + r) divmod c
  ... | qr q' r' r'<c eq = let
    q≡q' , r≡r' = divmod-unique (qr q' r' r'<c eq) (qr q r r<c auto)
    in cong₂ _,_ (≡-Range q≡q') (≡-Range r≡r')

  au : ∀ c → {{_ : NonZero c}} → ∀ n → ap c (unap c n) ≡ n
  au c (n [[ _ , _ ]]) with n divmod c
  ... | qr _ _ _ eq = ≡-Range (by eq)

unMove  : ∀ {a b} c → Range (c + a) (c + b) <-> Range a b
unSplit : ∀ {a c} b → a ≤ b → b ≤ c
  → Range a b ⊎ Range b c <-> Range a c
unScale : ∀ {a b} c → Range (c * a) (c * b) <-> Range a b × Fin c

unMove c        = flip (move c)
unSplit b lb ub = flip (split b lb ub)
unScale c       = flip (scale c)

splitFin : ∀ {b} a → a ≤ b → Fin b <-> Fin a ⊎ Range a b
splitFin a a≤b = split a auto a≤b

unSplitFin : ∀ {b} a → a ≤ b → Fin a ⊎ Range a b <-> Fin b
unSplitFin a a≤b = flip (splitFin a a≤b)

=R= : ∀ {a b c d} → a ≡ c → b ≡ d → Range a b <-> Range c d
=R= refl refl = id

 -- comp is short for 'composition', see
 -- https://en.wikipedia.org/wiki/Composition_(combinatorics)
record 2-Comp (n : Nat) : Set where
  constructor 2-comp
  field
    l : Nat
    m : Nat
    eq : n ≡ l + m
pattern 2-comp! lw = 2-comp lw _ refl

split' : ∀ {a} ((2-comp l m _) : 2-Comp a) → Fin a <-> Fin l ⊎ Fin m
split' (2-comp l m eq) = split l auto (diff m (by eq))
  <> (id <+> =R= auto eq <> unMove {0} {m} l)

unSplit' : ∀ {a} ((2-comp l m _) : 2-Comp a) → Fin l ⊎ Fin m <-> Fin a
unSplit' c = flip (split' c)

instance
  SmashRange : ∀ {a} → Smashed (Range a (suc a))
  smashed {{ SmashRange {a} }} {x} {y} =
      ≡-Range (helper x ⟨≡⟩ sym (helper y))
    where
    helper : (x : Range a (suc a)) → rangeToNat x ≡ a
    helper (x [[ a≤x , x≤a ]]) with compare x a
    helper (x [[ a≤x , _   ]]) | less lt₁ with less-not-geq lt₁ a≤x
    helper (x [[ a≤x , _   ]]) | less lt₁ | ()
    helper (x [[ _   , _   ]]) | equal eq = eq
    helper (x [[ _   , x≤a ]]) | greater gt with less-not-geq gt x≤a
    helper (x [[ _   , x≤a ]]) | greater gt | ()


fin1Unit : Fin 1 <-> ⊤
fin1Unit = MkF
  (λ _ → unit)
  (λ _ → zero [[ (diff! zero) , (diff! zero) ]])
  (λ _ → smashed)
  (λ _ → smashed)
