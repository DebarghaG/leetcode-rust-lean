import Aegis.KthLargestPerfectSubtree.Code.Funs

/-!
# Specifications of `Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree`

LeetCode problem `k-th-largest-perfect-subtree-size-in-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.KthLargestPerfectSubtree

open Aegis.KthLargestPerfectSubtree

def nodeCount : Tree → Nat
  | .Null => 0
  | .Node _ l r => nodeCount l + nodeCount r + 1

def treeHeight : Tree → Nat
  | .Null => 0
  | .Node _ l r => max (treeHeight l) (treeHeight r) + 1

def isPerfect : Tree → Bool
  | .Null => true
  | .Node _ l r => isPerfect l && isPerfect r && decide (treeHeight l = treeHeight r)

def IsPerfect (t : Tree) : Prop := isPerfect t = true

def perfectSizes : Tree → List Nat
  | .Null => []
  | .Node v l r =>
      let t : Tree := .Node v l r
      perfectSizes l ++ perfectSizes r ++ (if isPerfect t then [nodeCount t] else [])

def HasPerfectSubtreeOfSize (t : Tree) (r : Int) : Prop :=
  ∃ s : Nat, s ∈ perfectSizes t ∧ (s : Int) = r

def perfectCount (t : Tree) : Nat := (perfectSizes t).length

def countSizeGt (t : Tree) (r : Int) : Nat :=
  (perfectSizes t).countP (fun s => decide (r < (s : Int)))

def countSizeGe (t : Tree) (r : Int) : Nat :=
  (perfectSizes t).countP (fun s => decide (r ≤ (s : Int)))

def descSorted (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (b ≤ a))

def sortedPerfectSizes (t : Tree) : List Nat := descSorted (perfectSizes t)

def kthLargestSize (t : Tree) (k : Nat) : Int :=
  if (sortedPerfectSizes t).length < k then -1
  else ((sortedPerfectSizes t).getD (k - 1) 0 : Int)

def ValuesIn (lo hi : Int) : Tree → Prop
  | .Null => True
  | .Node v l r => lo ≤ v.val ∧ v.val ≤ hi ∧ ValuesIn lo hi l ∧ ValuesIn lo hi r

inductive TreeShape where
  | null : TreeShape
  | node : TreeShape → TreeShape → TreeShape
  deriving DecidableEq, Repr

def shapeOf : Tree → TreeShape
  | .Null => .null
  | .Node _ l r => .node (shapeOf l) (shapeOf r)

def SameShape (t₁ t₂ : Tree) : Prop := shapeOf t₁ = shapeOf t₂

/-- Let S(root) be the multiset of sizes of all perfect binary subtrees of root, counted one entry per node occurrence: a perfect binary subtree is a node occurrence u together with all descendants of u such that the resulting tree is perfect (all leaves are at the same level and every non-leaf node has exactly two children), and its size is its number of nodes. Let A be the list of elements of S(root) sorted in non-increasing order, with duplicates preserved. The function returns a result r (it does not fail), and: if len(A) < k then r = -1; if len(A) >= k then r = A[k-1] (using 1-based k, so A[0] is the largest and A[k-1] is the kth largest).
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_1 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        r.val = kthLargestSize root k.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        r.val = kthLargestSize root k.val.toNat) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_2 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r) := by
  sorry

/-- Let N be the number of node occurrences in root. Whenever the function returns a result r, either r = -1 or 1 <= r <= N.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_3 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nodeCount root : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nodeCount root : Int))) := by
  sorry

/-- Let C be the number of node occurrences u in root such that the subtree rooted at u is a perfect binary tree (all leaves at the same level, every internal node has two children). The function returns a result r, and r = -1 if and only if k > C.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_4 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        (r.val = -1 ↔ k.val > (perfectCount root : Int)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        (r.val = -1 ↔ k.val > (perfectCount root : Int))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists a node occurrence u in root such that the subtree rooted at u is a perfect binary tree (all leaves at the same level, every internal node has two children) and has exactly r nodes.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_5 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → HasPerfectSubtreeOfSize root r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → HasPerfectSubtreeOfSize root r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, the number of perfect binary subtrees of root whose size is strictly greater than r is at most k-1, and the number of perfect binary subtrees of root whose size is at least r is at least k.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_6 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 →
          (countSizeGt root r.val : Int) ≤ k.val - 1 ∧
            k.val ≤ (countSizeGe root r.val : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 →
          (countSizeGt root r.val : Int) ≤ k.val - 1 ∧
            k.val ≤ (countSizeGe root r.val : Int)) := by
  sorry

/-- The function returns a result r, and r is the maximum element of the multiset S(root) of sizes of all perfect binary subtrees of root: there is a perfect binary subtree of size r, and every perfect binary subtree of root has size at most r.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k = 1. -/
theorem spec_7 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk : k.val = 1) :
    ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        HasPerfectSubtreeOfSize root r.val ∧
          ∀ s : Nat, s ∈ perfectSizes root → (s : Int) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk : k.val = 1), ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        HasPerfectSubtreeOfSize root r.val ∧
          ∀ s : Nat, s ∈ perfectSizes root → (s : Int) ≤ r.val) := by
  sorry

/-- Let N be the number of node occurrences in root. The function returns a result r and r = N.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k = 1; root itself is a perfect binary tree. -/
theorem spec_8 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root) (hperfect : IsPerfect root)
    (hk : k.val = 1) :
    ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        r.val = (nodeCount root : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root) (hperfect : IsPerfect root)
    (hk : k.val = 1), ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        r.val = (nodeCount root : Int)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an integer h >= 1 such that r = 2^h - 1. Equivalently, r is positive and r+1 is a power of two.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_9 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → ∃ h : Nat, 1 ≤ h ∧ r.val = (2 : Int) ^ h - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → ∃ h : Nat, 1 ≤ h ∧ r.val = (2 : Int) ^ h - 1) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; let C be the number of perfect binary subtrees of root; assume C <= 1024 and k = C. -/
theorem spec_10 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hC : perfectCount root ≤ 1024) (hk : k.val = (perfectCount root : Int)) :
    ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        r.val = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hC : perfectCount root ≤ 1024) (hk : k.val = (perfectCount root : Int)), ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r ∧
        r.val = 1) := by
  sorry

/-- Let r1 be the result of the function on (root, k1) and r2 the result on (root, k2). The function returns both results, and r1 >= r2.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k1 and k2 are i64 values with 1 <= k1 <= k2 <= 1024. -/
theorem spec_11 (root : Tree) (k1 k2 : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 1024) :
    ∃ r1 r2 : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k1 = ok r1 ∧
        Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k2 = ok r2 ∧
          r1.val ≥ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (k1 k2 : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 1024), ∃ r1 r2 : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k1 = ok r1 ∧
        Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k2 = ok r2 ∧
          r1.val ≥ r2.val) := by
  sorry

/-- Let r1 be the result on (root1, k) and r2 the result on (root2, k). The function returns both results, and r1 = r2.
  Preconditions: root1 and root2 are Trees with the same shape (one is obtained from the other by changing only the i64 values at Node constructors, leaving all Null/Node positions and left/right child links unchanged); each has N node occurrences with 1 <= N <= 2000; every Node value in each tree satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_12 (root1 root2 : Tree) (k : Std.I64)
    (hshape : SameShape root1 root2)
    (hN1_pos : 1 ≤ nodeCount root1) (hN1_le : nodeCount root1 ≤ 2000)
    (hN2_pos : 1 ≤ nodeCount root2) (hN2_le : nodeCount root2 ≤ 2000)
    (hvals1 : ValuesIn 1 2000 root1) (hvals2 : ValuesIn 1 2000 root2)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∃ r1 r2 : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root1 k = ok r1 ∧
        Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root2 k = ok r2 ∧
          r1 = r2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root1 root2 : Tree) (k : Std.I64)
    (hshape : SameShape root1 root2)
    (hN1_pos : 1 ≤ nodeCount root1) (hN1_le : nodeCount root1 ≤ 2000)
    (hN2_pos : 1 ≤ nodeCount root2) (hN2_le : nodeCount root2 ≤ 2000)
    (hvals1 : ValuesIn 1 2000 root1) (hvals2 : ValuesIn 1 2000 root2)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∃ r1 r2 : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root1 k = ok r1 ∧
        Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root2 k = ok r2 ∧
          r1 = r2) := by
  sorry

/-- Let N be the number of node occurrences in root. Whenever the function returns a result r with r != -1, r < N.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024; root itself is not a perfect binary tree. -/
theorem spec_13 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root) (hnotperfect : ¬ IsPerfect root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → r.val < (nodeCount root : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root) (hnotperfect : ¬ IsPerfect root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → r.val < (nodeCount root : Int)) := by
  sorry

/-- The function returns a result r, and r = 1 if k = 1, while r = -1 if k > 1.
  Preconditions: root is exactly Node(v, Null, Null) for some i64 v with 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_14 (v k : Std.I64)
    (hv_pos : 1 ≤ v.val) (hv_le : v.val ≤ 2000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree (.Node v .Null .Null) k = ok r ∧
        (k.val = 1 → r.val = 1) ∧ (1 < k.val → r.val = -1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (v k : Std.I64)
    (hv_pos : 1 ≤ v.val) (hv_le : v.val ≤ 2000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∃ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree (.Node v .Null .Null) k = ok r ∧
        (k.val = 1 → r.val = 1) ∧ (1 < k.val → r.val = -1)) := by
  sorry

/-- Let H be the height of root measured in nodes (a Null tree has height 0 and a Node has height 1 plus the maximum height of its children). Whenever the function returns a result r with r != -1, r <= 2^H - 1.
  Preconditions: root is a Tree with N node occurrences, 1 <= N <= 2000; every Node value v satisfies 1 <= v <= 2000; k is an i64 with 1 <= k <= 1024. -/
theorem spec_15 (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024) :
    ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → r.val ≤ (2 : Int) ^ treeHeight root - 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hN_pos : 1 ≤ nodeCount root) (hN_le : nodeCount root ≤ 2000)
    (hvals : ValuesIn 1 2000 root)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1024), ∀ r : Std.I64,
      Aegis.KthLargestPerfectSubtree.kth_largest_perfect_subtree root k = ok r →
        r.val ≠ -1 → r.val ≤ (2 : Int) ^ treeHeight root - 1) := by
  sorry

end AegisSpec.KthLargestPerfectSubtree
