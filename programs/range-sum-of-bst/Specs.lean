import Aegis.RangeSumBst.Code.Funs

/-!
# Specifications of `Aegis.RangeSumBst.range_sum_bst`

LeetCode problem `range-sum-of-bst`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RangeSumBst

  open Aegis.RangeSumBst

  def values : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (values l ++ values r)

  def mem (x : ℤ) (t : Tree) : Prop := x ∈ values t

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def rangeSum (low high : ℤ) : Tree → ℤ
    | Tree.Null => 0
    | Tree.Node v l r =>
        (if low ≤ v.val ∧ v.val ≤ high then v.val else 0)
          + rangeSum low high l + rangeSum low high r

  def rangeCount (low high : ℤ) : Tree → Nat
    | Tree.Null => 0
    | Tree.Node v l r =>
        (if low ≤ v.val ∧ v.val ≤ high then 1 else 0)
          + rangeCount low high l + rangeCount low high r

  def BST : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        (∀ x, mem x l → x < v.val) ∧
        (∀ x, mem x r → v.val < x) ∧
        BST l ∧ BST r

  def Distinct (t : Tree) : Prop := (values t).Nodup

  def Bounded (lo hi : ℤ) (t : Tree) : Prop := ∀ x, mem x t → lo ≤ x ∧ x ≤ hi

  theorem i64_cMin :
      Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 = -9223372036854775808 := rfl

  theorem i64_cMax :
      Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64 = 9223372036854775807 := rfl

  def toI64 (x : ℤ)
      (h : Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 ≤ x ∧
           x ≤ Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64) : Aeneas.Std.I64 :=
    Aeneas.Std.I64.ofInt x h

  /-- The function returns a result r, and r is the sum of the values v of all nodes of root whose value v satisfies low <= v <= high. Each such node contributes its value exactly once, and no node outside the inclusive interval [low, high] contributes.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high <= 100000. -/
  theorem spec_1 (root : Tree) (low high : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        range_sum_bst root low high = ok r ∧
        r.val = rangeSum low.val high.val root := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (low high : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          range_sum_bst root low high = ok r ∧
          r.val = rangeSum low.val high.val root) := by
    sorry

  /-- The function returns a result r; it does not fail with overflow, panic, or out-of-bounds on any input satisfying the preconditions.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high <= 100000. -/
  theorem spec_2 (root : Tree) (low high : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64, range_sum_bst root low high = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (low high : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000), ∃ r : Aeneas.Std.I64, range_sum_bst root low high = ok r) := by
    sorry

  /-- Let k be the number of nodes of root whose value v satisfies low <= v <= high. The function returns a result r, and k * low <= r <= k * high.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high <= 100000. -/
  theorem spec_3 (root : Tree) (low high : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        range_sum_bst root low high = ok r ∧
        (rangeCount low.val high.val root : ℤ) * low.val ≤ r.val ∧
        r.val ≤ (rangeCount low.val high.val root : ℤ) * high.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (low high : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          range_sum_bst root low high = ok r ∧
          (rangeCount low.val high.val root : ℤ) * low.val ≤ r.val ∧
          r.val ≤ (rangeCount low.val high.val root : ℤ) * high.val) := by
    sorry

  /-- Let r1 be the result of range_sum_bst(root, low1, high1) and r2 be the result of range_sum_bst(root, low2, high2). The function returns both results, and r2 <= r1.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low1 <= low2 <= high2 <= high1 <= 100000. -/
  theorem spec_4 (root : Tree) (low1 high1 low2 high2 : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (h1 : 1 ≤ low1.val)
      (h12 : low1.val ≤ low2.val)
      (h23 : low2.val ≤ high2.val)
      (h34 : high2.val ≤ high1.val)
      (h45 : high1.val ≤ 100000) :
      ∃ r1 r2 : Aeneas.Std.I64,
        range_sum_bst root low1 high1 = ok r1 ∧
        range_sum_bst root low2 high2 = ok r2 ∧
        r2.val ≤ r1.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (low1 high1 low2 high2 : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (h1 : 1 ≤ low1.val)
        (h12 : low1.val ≤ low2.val)
        (h23 : low2.val ≤ high2.val)
        (h34 : high2.val ≤ high1.val)
        (h45 : high1.val ≤ 100000), ∃ r1 r2 : Aeneas.Std.I64,
          range_sum_bst root low1 high1 = ok r1 ∧
          range_sum_bst root low2 high2 = ok r2 ∧
          r2.val ≤ r1.val) := by
    sorry

  /-- Let r1 be the result of range_sum_bst(root, low, high) and r2 be the result of range_sum_bst(root, low, high + 1). The function returns both results, and r2 = r1 + (high + 1) if some node of root has value high + 1, and r2 = r1 otherwise.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high < 100000. -/
  theorem spec_5 (root : Tree) (low high : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val < 100000) :
      ∃ r1 r2 : Aeneas.Std.I64,
        range_sum_bst root low high = ok r1 ∧
        range_sum_bst root low
          (toI64 (high.val + 1) (by rw [i64_cMin, i64_cMax]; omega)) = ok r2 ∧
        ((∃ x, mem x root ∧ x = high.val + 1) →
            r2.val = r1.val + (high.val + 1)) ∧
        ((¬ ∃ x, mem x root ∧ x = high.val + 1) →
            r2.val = r1.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (low high : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val < 100000), ∃ r1 r2 : Aeneas.Std.I64,
          range_sum_bst root low high = ok r1 ∧
          range_sum_bst root low
            (toI64 (high.val + 1) (by rw [i64_cMin, i64_cMax]; omega)) = ok r2 ∧
          ((∃ x, mem x root ∧ x = high.val + 1) →
              r2.val = r1.val + (high.val + 1)) ∧
          ((¬ ∃ x, mem x root ∧ x = high.val + 1) →
              r2.val = r1.val)) := by
    sorry

  /-- Let r1 be the result of range_sum_bst(root, low, high) and r2 be the result of range_sum_bst(root, low - 1, high). The function returns both results, and r2 = r1 + (low - 1) if some node of root has value low - 1, and r2 = r1 otherwise.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 < low <= high <= 100000. -/
  theorem spec_6 (root : Tree) (low high : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000) :
      ∃ r1 r2 : Aeneas.Std.I64,
        range_sum_bst root low high = ok r1 ∧
        range_sum_bst root
          (toI64 (low.val - 1) (by rw [i64_cMin, i64_cMax]; omega)) high = ok r2 ∧
        ((∃ x, mem x root ∧ x = low.val - 1) →
            r2.val = r1.val + (low.val - 1)) ∧
        ((¬ ∃ x, mem x root ∧ x = low.val - 1) →
            r2.val = r1.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (low high : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 < low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000), ∃ r1 r2 : Aeneas.Std.I64,
          range_sum_bst root low high = ok r1 ∧
          range_sum_bst root
            (toI64 (low.val - 1) (by rw [i64_cMin, i64_cMax]; omega)) high = ok r2 ∧
          ((∃ x, mem x root ∧ x = low.val - 1) →
              r2.val = r1.val + (low.val - 1)) ∧
          ((¬ ∃ x, mem x root ∧ x = low.val - 1) →
              r2.val = r1.val)) := by
    sorry

  /-- For every integer mid with low <= mid < high, let r be the result of range_sum_bst(root, low, high), let r1 be the result of range_sum_bst(root, low, mid), and let r2 be the result of range_sum_bst(root, mid + 1, high). The function returns these results, and r = r1 + r2.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high <= 100000. -/
  theorem spec_7 (root : Tree) (low high mid : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000)
      (hmid1 : low.val ≤ mid.val) (hmid2 : mid.val < high.val) :
      ∃ r r1 r2 : Aeneas.Std.I64,
        range_sum_bst root low high = ok r ∧
        range_sum_bst root low mid = ok r1 ∧
        range_sum_bst root
          (toI64 (mid.val + 1) (by rw [i64_cMin, i64_cMax]; omega)) high = ok r2 ∧
        r.val = r1.val + r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (low high mid : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000)
        (hmid1 : low.val ≤ mid.val) (hmid2 : mid.val < high.val), ∃ r r1 r2 : Aeneas.Std.I64,
          range_sum_bst root low high = ok r ∧
          range_sum_bst root low mid = ok r1 ∧
          range_sum_bst root
            (toI64 (mid.val + 1) (by rw [i64_cMin, i64_cMax]; omega)) high = ok r2 ∧
          r.val = r1.val + r2.val) := by
    sorry

  /-- Let r1 be the result of range_sum_bst(root1, low, high) and r2 be the result of range_sum_bst(root2, low, high). The function returns both results, and r1 = r2.
    Preconditions: root1 and root2 are each nonempty binary search trees with at most 20000 nodes; every node value in either tree is an integer v with 1 <= v <= 100000; all node values within each tree are distinct; for every node in either tree, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high <= 100000; the set of values v of nodes of root1 with low <= v <= high equals the set of values v of nodes of root2 with low <= v <= high. -/
  theorem spec_8 (root1 root2 : Tree) (low high : Aeneas.Std.I64)
      (hne1 : root1 ≠ Tree.Null) (hne2 : root2 ≠ Tree.Null)
      (hcount1 : nodeCount root1 ≤ 20000) (hcount2 : nodeCount root2 ≤ 20000)
      (hbounds1 : Bounded 1 100000 root1) (hbounds2 : Bounded 1 100000 root2)
      (hdistinct1 : Distinct root1) (hdistinct2 : Distinct root2)
      (hbst1 : BST root1) (hbst2 : BST root2)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000)
      (hset : ∀ x : ℤ,
        (mem x root1 ∧ low.val ≤ x ∧ x ≤ high.val) ↔
        (mem x root2 ∧ low.val ≤ x ∧ x ≤ high.val)) :
      ∃ r1 r2 : Aeneas.Std.I64,
        range_sum_bst root1 low high = ok r1 ∧
        range_sum_bst root2 low high = ok r2 ∧
        r1.val = r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root1 root2 : Tree) (low high : Aeneas.Std.I64)
        (hne1 : root1 ≠ Tree.Null) (hne2 : root2 ≠ Tree.Null)
        (hcount1 : nodeCount root1 ≤ 20000) (hcount2 : nodeCount root2 ≤ 20000)
        (hbounds1 : Bounded 1 100000 root1) (hbounds2 : Bounded 1 100000 root2)
        (hdistinct1 : Distinct root1) (hdistinct2 : Distinct root2)
        (hbst1 : BST root1) (hbst2 : BST root2)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000)
        (hset : ∀ x : ℤ,
          (mem x root1 ∧ low.val ≤ x ∧ x ≤ high.val) ↔
          (mem x root2 ∧ low.val ≤ x ∧ x ≤ high.val)), ∃ r1 r2 : Aeneas.Std.I64,
          range_sum_bst root1 low high = ok r1 ∧
          range_sum_bst root2 low high = ok r2 ∧
          r1.val = r2.val) := by
    sorry

  /-- The function returns a result r, and r > 0 if and only if there exists at least one node of root whose value v satisfies low <= v <= high.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high <= 100000. -/
  theorem spec_9 (root : Tree) (low high : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        range_sum_bst root low high = ok r ∧
        (r.val > 0 ↔ ∃ x, mem x root ∧ low.val ≤ x ∧ x ≤ high.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (low high : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          range_sum_bst root low high = ok r ∧
          (r.val > 0 ↔ ∃ x, mem x root ∧ low.val ≤ x ∧ x ≤ high.val)) := by
    sorry

  /-- For every node of root whose value v satisfies low <= v <= high, the returned result r satisfies r >= v.
    Preconditions: The tree root is a nonempty binary search tree with at most 20000 nodes; every node value is an integer v with 1 <= v <= 100000; all node values in root are distinct; for every node, all values in its left subtree are less than its value and all values in its right subtree are greater than its value; 1 <= low <= high <= 100000. -/
  theorem spec_10 (root : Tree) (low high : Aeneas.Std.I64)
      (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 20000)
      (hbounds : Bounded 1 100000 root)
      (hdistinct : Distinct root)
      (hbst : BST root)
      (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        range_sum_bst root low high = ok r ∧
        (∀ x, mem x root → low.val ≤ x → x ≤ high.val → r.val ≥ x) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (low high : Aeneas.Std.I64)
        (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 20000)
        (hbounds : Bounded 1 100000 root)
        (hdistinct : Distinct root)
        (hbst : BST root)
        (hlow : 1 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh : high.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          range_sum_bst root low high = ok r ∧
          (∀ x, mem x root → low.val ≤ x → x ≤ high.val → r.val ≥ x)) := by
    sorry

  end AegisSpec.RangeSumBst
