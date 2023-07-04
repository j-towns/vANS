open import Prelude hiding (flip; _<>_; Fin)
open import Tactic.Nat

open import Flipper
open import Flipper.Prelude

open import Range


data BTree : Set where
  node : BTree -> BTree -> BTree
  leaf : BTree

example-btree : BTree
example-btree =
  node
    leaf
    (node
      leaf
      (node
        leaf
        leaf)
      )

{-
For an alphabet a₀, a₁, ..., aₙ₋₁, store weights w(a₀), w(a₁), ...,
w(aₙ₋₁) : Nat, in such a way that looking up the weight of a symbol
and updating the weight of a symbol are both cheap, and looking up
partial sums

sₘ := ₖ₌₀∑ᵐ w(aₖ)

is also cheap.

ft-lookup : forall {t m} -> (ft : FTree m t)
  -> Fin m <-> Σ (ValidAddress t) (Fin ∘ weight ft)

  0   1   2   3   4   5   6   7

  |---------------------------|    \
       /         \                 |
  |-------|-------------------|    |
             /      \              +- This tree represents...
          |---|---------------|    |
                 /     \           |
              |---|-----------|    /

  |-------|---|---|-----------|    <- ...these weights.

  +---+---+---+---+---+---+---+
  0   1   2   3   4   5   6   7
-}

data FTree (m : Nat) : BTree -> Set where
  node : ((2-comp lw rw _) : 2-Comp m){lt rt : BTree}
         (l : FTree lw lt)(r : FTree rw rt)
         -> FTree m (node lt rt)
  leaf : FTree m leaf

 -- We can define an FTree with a free structure, but then
 -- ValidAddresses are indexed by FTrees, which won't make sense,
 -- since we will need the addresses to stay valid when we change the
 -- c values in the tree.
data FTree' (m : Nat) : Set where
  node : (c : 2-Comp m)
         (l : FTree' (2-Comp.l c))(r : FTree' (2-Comp.m c))
         -> FTree' m
  leaf : FTree' m

example-ftree : FTree 7 example-btree
example-ftree =
  node (2-comp! 2)
    leaf
    (node (2-comp! 1)
      leaf
      (node (2-comp! 1)
        leaf
        leaf))

data ValidAddress : (t : BTree) -> Set where
  <0> : {l r : BTree} -> ValidAddress l -> ValidAddress (node l r)
  <1> : {l r : BTree} -> ValidAddress r -> ValidAddress (node l r)
  <end> : ValidAddress leaf

weight : forall {m t} -> (ft : FTree m t) -> ValidAddress t -> Nat
weight     (node lw l r) (<0> a) = weight l a
weight     (node lw l r) (<1> a) = weight r a
weight {m} leaf          <end>   = m

_ : weight example-ftree (<1> (<0> <end>)) ≡ 1
_ = refl

inc : forall {t m} -> (ft : FTree m t) -> ValidAddress t -> FTree (suc m) t
inc (node (2-comp! lw) l r) (<0> a) = node (2-comp! (suc lw)) (inc l a) r
inc (node (2-comp! lw) l r) (<1> a) = node (2-comp lw _ auto) l         (inc r a)
inc leaf                    <end>   = leaf

 -- This does lookup (given a position in Fin m find the leaf
 -- corresponding to that position), but in a reversible way...
ft-lookup : forall {t m} -> (ft : FTree m t)
  -> Fin m <-> Σ (ValidAddress t) (Fin ∘ weight ft)
ft-lookup (node c l r) = split' c
  <>
    F \ { (left  x) → x ⟨ ft-lookup l ⟩ \ { (a , w) → (<0> a , w) }
        ; (right x) → x ⟨ ft-lookup r ⟩ \ { (a , w) → (<1> a , w) }
        }
ft-lookup leaf = F \ { x -> <end> , x }

zer : forall {t} -> FTree 0 t
zer {node l r} = node (2-comp! 0) zer zer
zer {leaf}     = leaf

complete : (depth : Nat) -> BTree
complete zero        = leaf
complete (suc depth) = node (complete depth) (complete depth)

fromMass : (t : BTree) → (ValidAddress t → Nat) → Σ Nat λ m → FTree m t
fromMass (node l r) massFn with fromMass l (massFn ∘ <0>) | fromMass r (massFn ∘ <1>)
... | ml , tl | mr , tr = (ml + mr) , (node (2-comp ml mr refl) tl tr)
fromMass leaf massFn = (massFn <end>) , leaf
