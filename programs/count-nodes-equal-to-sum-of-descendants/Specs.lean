import Aegis.EqualToDescendants.Code.Funs

/-!
# Specifications of `Aegis.EqualToDescendants.equal_to_descendants`

LeetCode problem `count-nodes-equal-to-sum-of-descendants`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.EqualToDescendants

namespace AegisSpec.EqualToDescendants

def size : Tree → Nat
  | .Null => 0
  | .Node _ l r => size l + size r + 1

def values : Tree → List Int
  | .Null => []
  | .Node v l r => v.val :: (values l ++ values r)

def descValues : Tree → List Int
  | .Null => []
  | .Node _ l r => values l ++ values r

def valBounded (t : Tree) : Prop := ∀ v ∈ values t, 0 ≤ v ∧ v ≤ 100000

def rootVal : Tree → Int
  | .Null => 0
  | .Node v _ _ => v.val

def subtreeSum : Tree → Int
  | .Null => 0
  | .Node v l r => v.val + subtreeSum l + subtreeSum r

def descSum : Tree → Int
  | .Null => 0
  | .Node _ l r => subtreeSum l + subtreeSum r

def isGood : Tree → Prop
  | .Null => False
  | .Node v l r => v.val = subtreeSum l + subtreeSum r

def goodCount : Tree → Nat
  | .Null => 0
  | .Node v l r =>
      goodCount l + goodCount r + (if v.val = subtreeSum l + subtreeSum r then 1 else 0)

def leafCount : Tree → Nat
  | .Null => 0
  | .Node _ .Null .Null => 1
  | .Node _ l r => leafCount l + leafCount r

def everyNode (p : Tree → Prop) : Tree → Prop
  | .Null => True
  | .Node v l r => p (.Node v l r) ∧ everyNode p l ∧ everyNode p r

def get? (t : Tree) (p : List Bool) : Option Tree :=
  match t, p with
  | .Null, _ => none
  | .Node _ _ _, [] => some t
  | .Node _ l _, true :: q => get? l q
  | .Node _ _ r, false :: q => get? r q

def positivePaths : Tree → List (List Bool)
  | .Null => []
  | .Node v l r =>
      (if 0 < v.val then ([[]] : List (List Bool)) else [])
        ++ (positivePaths l).map (fun p => true :: p)
        ++ (positivePaths r).map (fun p => false :: p)

def countOf (t : Tree) : Result I64 :=
  match t with
  | .Null => ok 0#i64
  | .Node _ _ _ => equal_to_descendants t

inductive SwapNode : Tree → Tree → Prop
  | root (v : I64) (l r : Tree) : SwapNode (.Node v l r) (.Node v r l)
  | left {v : I64} {l l' r : Tree} : SwapNode l l' → SwapNode (.Node v l r) (.Node v l' r)
  | right {v : I64} {l r r' : Tree} : SwapNode r r' → SwapNode (.Node v l r) (.Node v r' r)

inductive AddZeroLeaf : Tree → Tree → Prop
  | left (v : I64) (r : Tree) :
      AddZeroLeaf (.Node v .Null r) (.Node v (.Node 0#i64 .Null .Null) r)
  | right (v : I64) (l : Tree) :
      AddZeroLeaf (.Node v l .Null) (.Node v l (.Node 0#i64 .Null .Null))
  | under_left {v : I64} {l l' r : Tree} :
      AddZeroLeaf l l' → AddZeroLeaf (.Node v l r) (.Node v l' r)
  | under_right {v : I64} {l r r' : Tree} :
      AddZeroLeaf r r' → AddZeroLeaf (.Node v l r) (.Node v r' r)

inductive SetValAt : Tree → List Bool → I64 → Tree → Prop
  | root (v a : I64) (l r : Tree) : SetValAt (.Node v l r) [] a (.Node a l r)
  | left {v a : I64} {l l' r : Tree} {p : List Bool} :
      SetValAt l p a l' → SetValAt (.Node v l r) (true :: p) a (.Node v l' r)
  | right {v a : I64} {l r r' : Tree} {p : List Bool} :
      SetValAt r p a r' → SetValAt (.Node v l r) (false :: p) a (.Node v r' r)

/-- The function returns an i64 r such that r equals the number of nodes x in T for which val(x) = descSum(x), where descSum(x) is the sum of val(y) over all proper descendants y of x (i.e., all nodes in the subtree rooted at x other than x); if x has no proper descendants, descSum(x) = 0.
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, and every node value v satisfies 0 <= v <= 100000. -/
theorem spec_1 (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root) :
    ∃ r : I64,
      equal_to_descendants root = ok r ∧ r.val = (goodCount root : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root), ∃ r : I64,
      equal_to_descendants root = ok r ∧ r.val = (goodCount root : Int)) := by
  sorry

/-- Whenever the function returns r, 0 <= r <= n, where n is the number of nodes of T.
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, and every node value v satisfies 0 <= v <= 100000. -/
theorem spec_2 (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root) :
    ∀ r : I64, equal_to_descendants root = ok r → 0 ≤ r.val ∧ r.val ≤ (size root : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root), ∀ r : I64, equal_to_descendants root = ok r → 0 ≤ r.val ∧ r.val ≤ (size root : Int)) := by
  sorry

/-- The function does not fail on any such input: it returns a result r (no panic, no arithmetic overflow, no out-of-bounds access).
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, and every node value v satisfies 0 <= v <= 100000. -/
theorem spec_3 (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root) :
    ∃ r : I64, equal_to_descendants root = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root), ∃ r : I64, equal_to_descendants root = ok r) := by
  sorry

/-- Whenever the function returns r, r <= n - L, where L is the number of leaves of T.
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, every node value is in [0,100000], and every node of T has value at least 1. -/
theorem spec_4 (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hpos : ∀ v ∈ values root, 1 ≤ v) :
    ∀ r : I64,
      equal_to_descendants root = ok r →
        r.val ≤ (size root : Int) - (leafCount root : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hpos : ∀ v ∈ values root, 1 ≤ v), ∀ r : I64,
      equal_to_descendants root = ok r →
        r.val ≤ (size root : Int) - (leafCount root : Int)) := by
  sorry

/-- equal_to_descendants(T) = equal_to_descendants(T').
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, and every node value is in [0,100000]. The tree T' is obtained from T by choosing any node x and swapping its left and right subtrees (if one child is Null, the two child slots are still swapped). T' also satisfies the same size and value bounds. -/
theorem spec_5 (root root' : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hswap : SwapNode root root')
    (hne' : root' ≠ .Null)
    (hn'_lo : 1 ≤ size root')
    (hn'_hi : size root' ≤ 100000)
    (hb' : valBounded root') :
    equal_to_descendants root = equal_to_descendants root' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root root' : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hswap : SwapNode root root')
    (hne' : root' ≠ .Null)
    (hn'_lo : 1 ≤ size root')
    (hn'_hi : size root' ≤ 100000)
    (hb' : valBounded root'), equal_to_descendants root = equal_to_descendants root') := by
  sorry

/-- equal_to_descendants(T) = count(L) + count(R) + (1 if val(x0) = descSum(x0) in T else 0), where count(L) and count(R) are the results of equal_to_descendants on L and R respectively (and 0 when the subtree is Null).
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, and every node value is in [0,100000]. Let x0 be the root of T, and let L and R be the left and right subtrees of x0 (each possibly Null). Define count(Null) = 0. -/
theorem spec_6 (x0 : I64) (L R : Tree) (rL rR r : I64)
    (hne : (Tree.Node x0 L R) ≠ .Null)
    (hn_lo : 1 ≤ size (.Node x0 L R))
    (hn_hi : size (.Node x0 L R) ≤ 100000)
    (hb : valBounded (.Node x0 L R))
    (hL : countOf L = ok rL)
    (hR : countOf R = ok rR)
    (hT : equal_to_descendants (.Node x0 L R) = ok r) :
    r.val = rL.val + rR.val + (if x0.val = descSum (.Node x0 L R) then (1 : Int) else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (x0 : I64) (L R : Tree) (rL rR r : I64)
    (hne : (Tree.Node x0 L R) ≠ .Null)
    (hn_lo : 1 ≤ size (.Node x0 L R))
    (hn_hi : size (.Node x0 L R) ≤ 100000)
    (hb : valBounded (.Node x0 L R))
    (hL : countOf L = ok rL)
    (hR : countOf R = ok rR)
    (hT : equal_to_descendants (.Node x0 L R) = ok r), r.val = rL.val + rR.val + (if x0.val = descSum (.Node x0 L R) then (1 : Int) else 0)) := by
  sorry

/-- If a = 0 then the function returns r = n; if a > 0 then it returns r = n - 1.
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, every node value is in [0,100000], and every node other than the root has value 0. Let a = val(root). -/
theorem spec_7 (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hzeros : ∀ c ∈ descValues root, c = 0) :
    (rootVal root = 0 →
        ∀ r : I64, equal_to_descendants root = ok r → r.val = (size root : Int)) ∧
      (0 < rootVal root →
        ∀ r : I64,
          equal_to_descendants root = ok r → r.val = (size root : Int) - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hzeros : ∀ c ∈ descValues root, c = 0), (rootVal root = 0 →
        ∀ r : I64, equal_to_descendants root = ok r → r.val = (size root : Int)) ∧
      (0 < rootVal root →
        ∀ r : I64,
          equal_to_descendants root = ok r → r.val = (size root : Int) - 1)) := by
  sorry

/-- equal_to_descendants(T') = equal_to_descendants(T) + 1.
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, and every node value is in [0,100000]. The tree T' is obtained from T by choosing a node x and a Null child slot of x, and replacing that Null with a new leaf node of value 0. T' also satisfies the size and value bounds. -/
theorem spec_8 (root root' : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hadd : AddZeroLeaf root root')
    (hne' : root' ≠ .Null)
    (hn'_lo : 1 ≤ size root')
    (hn'_hi : size root' ≤ 100000)
    (hb' : valBounded root') :
    ∀ r r' : I64,
      equal_to_descendants root = ok r → equal_to_descendants root' = ok r' →
        r'.val = r.val + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root root' : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root)
    (hadd : AddZeroLeaf root root')
    (hne' : root' ≠ .Null)
    (hn'_lo : 1 ≤ size root')
    (hn'_hi : size root' ≤ 100000)
    (hb' : valBounded root'), ∀ r r' : I64,
      equal_to_descendants root = ok r → equal_to_descendants root' = ok r' →
        r'.val = r.val + 1) := by
  sorry

/-- The function returns r = n - (d + 1).
  Preconditions: Let T be the input tree (the value of root). T is non-null, has n nodes with 1 <= n <= 100000, and every node value is in [0,100000]. Exactly one node y of T has a positive value a > 0; every other node has value 0. Let d be the number of edges on the path from the root of T to y (so d = 0 if y is the root). -/
theorem spec_9 (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root) :
    ∀ (p : List Bool),
      positivePaths root = [p] →
        ∀ r : I64,
          equal_to_descendants root = ok r →
            r.val = (size root : Int) - ((p.length : Int) + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ .Null)
    (hn_lo : 1 ≤ size root)
    (hn_hi : size root ≤ 100000)
    (hb : valBounded root), ∀ (p : List Bool),
      positivePaths root = [p] →
        ∀ r : I64,
          equal_to_descendants root = ok r →
            r.val = (size root : Int) - ((p.length : Int) + 1)) := by
  sorry

end AegisSpec.EqualToDescendants
