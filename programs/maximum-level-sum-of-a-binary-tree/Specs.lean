import Aegis.MaxLevelSum.Code.Funs

/-!
# Specifications of `Aegis.MaxLevelSum.max_level_sum`

LeetCode problem `maximum-level-sum-of-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxLevelSum

  open Aegis.MaxLevelSum

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def height : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => max (height l) (height r) + 1

  def levelValues : Tree → Nat → List Int
    | Tree.Null, _ => []
    | Tree.Node v _ _, 0 => [v.val]
    | Tree.Node _ l r, d + 1 => levelValues l d ++ levelValues r d

  def levelSum : Tree → Nat → Int
    | _, 0 => 0
    | t, l + 1 => (levelValues t l).sum

  def OccursAtDepth : Tree → Nat → Int → Prop
    | Tree.Null, _, _ => False
    | Tree.Node v _ _, 0, x => v.val = x
    | Tree.Node _ l r, d + 1, x => OccursAtDepth l d x ∨ OccursAtDepth r d x

  def ValuesBounded : Tree → Int → Int → Prop
    | Tree.Null, _, _ => True
    | Tree.Node v l r, lo, hi =>
      lo ≤ v.val ∧ v.val ≤ hi ∧ ValuesBounded l lo hi ∧ ValuesBounded r lo hi

  def IsLeafOrNull : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ Tree.Null Tree.Null => True
    | Tree.Node _ _ _ => False

  def childValue : Tree → Int
    | Tree.Null => 0
    | Tree.Node v _ _ => v.val

  def childSum (left right : Tree) : Int := childValue left + childValue right

  inductive SwapCongr : Tree → Tree → Prop
    | refl (t : Tree) : SwapCongr t t
    | node {v : Std.I64} {a b a' b' : Tree} :
      SwapCongr a a' → SwapCongr b b' → SwapCongr (Tree.Node v a b) (Tree.Node v a' b')
    | swap {v : Std.I64} {a b a' b' : Tree} :
      SwapCongr a a' → SwapCongr b b' → SwapCongr (Tree.Node v a b) (Tree.Node v b' a')

  /-- Let h = height(root), where height is the largest level containing at least one node, with the root at level 1, and for 1 <= l <= h let S(l) be the sum of the values of all nodes at level l. The function returns a result r : i64 such that 1 <= r <= h, for every l with 1 <= l <= h we have S(l) <= S(r), and for every l with 1 <= l < r we have S(l) < S(r). Equivalently, r is the smallest level whose level sum is maximal among all levels of root.
    Preconditions: root is not Tree.Null; the number of nodes in root is between 1 and 10000 inclusive; every node value is in [-100000, 100000]. -/
  theorem spec_1 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000) :
      ∃ r : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root = ok r ∧
          1 ≤ r.val ∧
          r.val ≤ (height root : Int) ∧
          (∀ l : Nat, 1 ≤ l → l ≤ height root → levelSum root l ≤ levelSum root r.val.toNat) ∧
          (∀ l : Nat, 1 ≤ l → l < r.val.toNat → levelSum root l < levelSum root r.val.toNat) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000), ∃ r : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root = ok r ∧
            1 ≤ r.val ∧
            r.val ≤ (height root : Int) ∧
            (∀ l : Nat, 1 ≤ l → l ≤ height root → levelSum root l ≤ levelSum root r.val.toNat) ∧
            (∀ l : Nat, 1 ≤ l → l < r.val.toNat → levelSum root l < levelSum root r.val.toNat)) := by
    sorry

  /-- The function returns a result r : i64; in particular, it does not fail by panicking, accessing a missing tree node, or overflowing a 64-bit integer. Formally, there exists r : i64 such that max_level_sum root = ok r.
    Preconditions: root is not Tree.Null; the number of nodes in root is between 1 and 10000 inclusive; every node value is in [-100000, 100000]. -/
  theorem spec_2 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000) :
      ∃ r : Std.I64, Aegis.MaxLevelSum.max_level_sum root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000), ∃ r : Std.I64, Aegis.MaxLevelSum.max_level_sum root = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= nodeCount(root), where nodeCount(root) is the number of non-Null nodes in root.
    Preconditions: root is not Tree.Null; the number of nodes in root is between 1 and 10000 inclusive; every node value is in [-100000, 100000]. -/
  theorem spec_3 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000) :
      ∀ r : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root = ok r →
          1 ≤ r.val ∧ r.val ≤ (nodeCount root : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000), ∀ r : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root = ok r →
            1 ≤ r.val ∧ r.val ≤ (nodeCount root : Int)) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= height(root) and level r of root is nonempty; equivalently, there exists at least one node v in root whose depth from the root is r-1.
    Preconditions: root is not Tree.Null; the number of nodes in root is between 1 and 10000 inclusive; every node value is in [-100000, 100000]. -/
  theorem spec_4 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000) :
      ∀ r : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root = ok r →
          1 ≤ r.val ∧
            r.val ≤ (height root : Int) ∧
            levelValues root (r.val.toNat - 1) ≠ [] ∧
            ∃ x : Int, OccursAtDepth root (r.val.toNat - 1) x := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000), ∀ r : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root = ok r →
            1 ≤ r.val ∧
              r.val ≤ (height root : Int) ∧
              levelValues root (r.val.toNat - 1) ≠ [] ∧
              ∃ x : Int, OccursAtDepth root (r.val.toNat - 1) x) := by
    sorry

  /-- Whenever the function returns a result r, for every level l with 1 <= l <= height(root), the sum of the values of all nodes at level l is less than or equal to the sum of the values of all nodes at level r.
    Preconditions: root is not Tree.Null; the number of nodes in root is between 1 and 10000 inclusive; every node value is in [-100000, 100000]. -/
  theorem spec_5 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000) :
      ∀ r : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root = ok r →
          ∀ l : Nat, 1 ≤ l → l ≤ height root → levelSum root l ≤ levelSum root r.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000), ∀ r : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root = ok r →
            ∀ l : Nat, 1 ≤ l → l ≤ height root → levelSum root l ≤ levelSum root r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every level l with 1 <= l < r, the sum of the values of all nodes at level l is strictly less than the sum of the values of all nodes at level r.
    Preconditions: root is not Tree.Null; the number of nodes in root is between 1 and 10000 inclusive; every node value is in [-100000, 100000]. -/
  theorem spec_6 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000) :
      ∀ r : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root = ok r →
          ∀ l : Nat, 1 ≤ l → l < r.val.toNat → levelSum root l < levelSum root r.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000), ∀ r : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root = ok r →
            ∀ l : Nat, 1 ≤ l → l < r.val.toNat → levelSum root l < levelSum root r.val.toNat) := by
    sorry

  /-- The function returns 1.
    Preconditions: root = Tree.Node(v, Tree.Null, Tree.Null) for some i64 v with -100000 <= v <= 100000. -/
  theorem spec_7 (v : Std.I64) (hv : -100000 ≤ v.val ∧ v.val ≤ 100000) :
      ∃ r : Std.I64,
        Aegis.MaxLevelSum.max_level_sum (Tree.Node v Tree.Null Tree.Null) = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (v : Std.I64) (hv : -100000 ≤ v.val ∧ v.val ≤ 100000), ∃ r : Std.I64,
          Aegis.MaxLevelSum.max_level_sum (Tree.Node v Tree.Null Tree.Null) = ok r ∧ r.val = 1) := by
    sorry

  /-- Let s2 be the sum of the values of the non-Null children of the root (so s2 is the left child's value if only the left child exists, the right child's value if only the right child exists, and left value + right value if both exist). The function returns 1 if v >= s2, and returns 2 if v < s2.
    Preconditions: root = Tree.Node(v, left, right), where left and right are either Tree.Null or a leaf Tree.Node(_, Tree.Null, Tree.Null), and at least one of left and right is non-Null; all node values are in [-100000, 100000]. -/
  theorem spec_8 (v : Std.I64) (left right : Tree)
      (hleft : IsLeafOrNull left) (hright : IsLeafOrNull right)
      (hnnull : left ≠ Tree.Null ∨ right ≠ Tree.Null)
      (hbnd : ValuesBounded (Tree.Node v left right) (-100000) 100000) :
      (childSum left right ≤ v.val →
          ∃ r : Std.I64,
            Aegis.MaxLevelSum.max_level_sum (Tree.Node v left right) = ok r ∧ r.val = 1) ∧
        (v.val < childSum left right →
          ∃ r : Std.I64,
            Aegis.MaxLevelSum.max_level_sum (Tree.Node v left right) = ok r ∧ r.val = 2) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (v : Std.I64) (left right : Tree)
        (hleft : IsLeafOrNull left) (hright : IsLeafOrNull right)
        (hnnull : left ≠ Tree.Null ∨ right ≠ Tree.Null)
        (hbnd : ValuesBounded (Tree.Node v left right) (-100000) 100000), (childSum left right ≤ v.val →
            ∃ r : Std.I64,
              Aegis.MaxLevelSum.max_level_sum (Tree.Node v left right) = ok r ∧ r.val = 1) ∧
          (v.val < childSum left right →
            ∃ r : Std.I64,
              Aegis.MaxLevelSum.max_level_sum (Tree.Node v left right) = ok r ∧ r.val = 2)) := by
    sorry

  /-- The function returns height(root), i.e. the integer h.
    Preconditions: root is not Tree.Null; the number of nodes in root is between 1 and 10000 inclusive; every node value is in [-100000, 100000]; if h = height(root) and S(l) is the sum of values at level l for 1 <= l <= h, then S(1) < S(2) < ... < S(h). -/
  theorem spec_9 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000)
      (hincr : ∀ l : Nat, 1 ≤ l → l < height root → levelSum root l < levelSum root (l + 1)) :
      ∃ r : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root = ok r ∧ r.val = (height root : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000)
        (hincr : ∀ l : Nat, 1 ≤ l → l < height root → levelSum root l < levelSum root (l + 1)), ∃ r : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root = ok r ∧ r.val = (height root : Int)) := by
    sorry

  /-- Whenever max_level_sum root1 returns r1 and max_level_sum root2 returns r2, we have r1 = r2.
    Preconditions: root1 and root2 are non-Null trees, each with between 1 and 10000 nodes and all node values in [-100000, 100000]. Let h1 = height(root1), h2 = height(root2), and let S1, spec_2 be their level-sum functions. Suppose h1 = h2 = h and S1(l) = S2(l) for every 1 <= l <= h. -/
  theorem spec_10 (root1 root2 : Tree)
      (hne1 : root1 ≠ Tree.Null) (hne2 : root2 ≠ Tree.Null)
      (hcount1_ge : 1 ≤ nodeCount root1) (hcount1_le : nodeCount root1 ≤ 10000)
      (hcount2_ge : 1 ≤ nodeCount root2) (hcount2_le : nodeCount root2 ≤ 10000)
      (hbnd1 : ValuesBounded root1 (-100000) 100000)
      (hbnd2 : ValuesBounded root2 (-100000) 100000)
      (hheight : height root1 = height root2)
      (hsums : ∀ l : Nat, 1 ≤ l → l ≤ height root1 → levelSum root1 l = levelSum root2 l) :
      ∀ r1 r2 : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root1 = ok r1 →
          Aegis.MaxLevelSum.max_level_sum root2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hne1 : root1 ≠ Tree.Null) (hne2 : root2 ≠ Tree.Null)
        (hcount1_ge : 1 ≤ nodeCount root1) (hcount1_le : nodeCount root1 ≤ 10000)
        (hcount2_ge : 1 ≤ nodeCount root2) (hcount2_le : nodeCount root2 ≤ 10000)
        (hbnd1 : ValuesBounded root1 (-100000) 100000)
        (hbnd2 : ValuesBounded root2 (-100000) 100000)
        (hheight : height root1 = height root2)
        (hsums : ∀ l : Nat, 1 ≤ l → l ≤ height root1 → levelSum root1 l = levelSum root2 l), ∀ r1 r2 : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root1 = ok r1 →
            Aegis.MaxLevelSum.max_level_sum root2 = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever max_level_sum root returns r and max_level_sum root' returns r', we have r = r'.
    Preconditions: root and root' are non-Null trees, each with between 1 and 10000 nodes and all node values in [-100000, 100000], and root' is obtained from root by any sequence of replacing a subnode Tree.Node(v, a, b) with Tree.Node(v, b, a) (swapping left and right children at any nodes). -/
  theorem spec_11 (root root' : Tree)
      (hne : root ≠ Tree.Null) (hne' : root' ≠ Tree.Null)
      (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
      (hcount'_ge : 1 ≤ nodeCount root') (hcount'_le : nodeCount root' ≤ 10000)
      (hbnd : ValuesBounded root (-100000) 100000)
      (hbnd' : ValuesBounded root' (-100000) 100000)
      (hswap : SwapCongr root root') :
      ∀ r r' : Std.I64,
        Aegis.MaxLevelSum.max_level_sum root = ok r →
          Aegis.MaxLevelSum.max_level_sum root' = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root root' : Tree)
        (hne : root ≠ Tree.Null) (hne' : root' ≠ Tree.Null)
        (hcount_ge : 1 ≤ nodeCount root) (hcount_le : nodeCount root ≤ 10000)
        (hcount'_ge : 1 ≤ nodeCount root') (hcount'_le : nodeCount root' ≤ 10000)
        (hbnd : ValuesBounded root (-100000) 100000)
        (hbnd' : ValuesBounded root' (-100000) 100000)
        (hswap : SwapCongr root root'), ∀ r r' : Std.I64,
          Aegis.MaxLevelSum.max_level_sum root = ok r →
            Aegis.MaxLevelSum.max_level_sum root' = ok r' → r = r') := by
    sorry

  end AegisSpec.MaxLevelSum
