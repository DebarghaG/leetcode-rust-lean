import Aegis.KthSmallest.Code.Funs

/-!
# Specifications of `Aegis.KthSmallest.kth_smallest`

LeetCode problem `kth-smallest-element-in-a-bst`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.KthSmallest

open Aegis.KthSmallest

def values : Tree → List ℤ
  | Tree.Null => []
  | Tree.Node v l r => values l ++ [v.val] ++ values r

def size : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => size l + 1 + size r

def sortedValues (t : Tree) : List ℤ :=
  List.insertionSort (· ≤ ·) (values t)

def IsBST : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    IsBST l ∧ IsBST r ∧ (∀ x ∈ values l, x < v.val) ∧ (∀ x ∈ values r, v.val < x)

def valuesBounded (t : Tree) : Prop := ∀ x ∈ values t, 0 ≤ x ∧ x ≤ 10000

def countLt (t : Tree) (x : ℤ) : Nat :=
  List.countP (fun y => decide (y < x)) (values t)

def countGt (t : Tree) (x : ℤ) : Nat :=
  List.countP (fun y => decide (x < y)) (values t)

/-- Whenever kth_smallest(root, k) returns a result r, r is the k-th smallest value among all node values of root. Formally, if sorted_values(root) is the list of all node values of root sorted in nondecreasing order, so len(sorted_values(root)) = size(root), then r = sorted_values(root)[k - 1], where the list index k - 1 is 0-based and the rank k is 1-based.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; and k is an integer with 1 <= k <= size(root), where size(root) is the number of nodes in root. -/
theorem spec_1 (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)) :
    ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r →
      (sortedValues root)[(k.val - 1).toNat]? = some r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)), ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r →
      (sortedValues root)[(k.val - 1).toNat]? = some r.val) := by
  sorry

/-- For every input satisfying the preconditions, kth_smallest(root, k) returns a result r; that is, it does not fail by overflow, panic, or out-of-bounds access.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; and k is an integer with 1 <= k <= size(root), where size(root) is the number of nodes in root. -/
theorem spec_2 (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)) :
    ∃ r, Aegis.KthSmallest.kth_smallest root k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)), ∃ r, Aegis.KthSmallest.kth_smallest root k = ok r) := by
  sorry

/-- Whenever kth_smallest(root, k) returns a result r, there exists a node in root whose value is exactly r; equivalently, r belongs to the set of node values of root.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; and k is an integer with 1 <= k <= size(root), where size(root) is the number of nodes in root. -/
theorem spec_3 (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)) :
    ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val ∈ values root := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)), ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val ∈ values root) := by
  sorry

/-- Whenever kth_smallest(root, k) returns a result r, exactly k - 1 nodes of root have values strictly less than r.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; and k is an integer with 1 <= k <= size(root), where size(root) is the number of nodes in root. -/
theorem spec_4 (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)) :
    ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r →
      countLt root r.val = (k.val - 1).toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)), ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r →
      countLt root r.val = (k.val - 1).toNat) := by
  sorry

/-- Whenever kth_smallest(root, k) returns a result r, exactly size(root) - k nodes of root have values strictly greater than r.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; and k is an integer with 1 <= k <= size(root), where size(root) is the number of nodes in root. -/
theorem spec_5 (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)) :
    ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r →
      countGt root r.val = size root - k.val.toNat := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)), ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r →
      countGt root r.val = size root - k.val.toNat) := by
  sorry

/-- If kth_smallest(root1, k) returns a result r1 and kth_smallest(root2, k) returns a result r2, then r1 = r2. Thus the answer depends only on the multiset of node values and on k, not on the shape of the BST.
  Preconditions: root1 and root2 are binary search trees in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value in either tree is an integer between 0 and 10000 inclusive; size(root1) = size(root2) <= 10000; root1 and root2 have the same multiset of node values; and k is an integer with 1 <= k <= size(root1). -/
theorem spec_6 (root1 root2 : Tree) (k : Std.I64)
    (hbst1 : IsBST root1)
    (hbst2 : IsBST root2)
    (hbounded1 : valuesBounded root1)
    (hbounded2 : valuesBounded root2)
    (hsize_eq : size root1 = size root2)
    (hsize_le : size root1 ≤ 10000)
    (hperm : (values root1).Perm (values root2))
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root1 : ℤ)) :
    ∀ r1 r2, Aegis.KthSmallest.kth_smallest root1 k = ok r1 →
      Aegis.KthSmallest.kth_smallest root2 k = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root1 root2 : Tree) (k : Std.I64)
    (hbst1 : IsBST root1)
    (hbst2 : IsBST root2)
    (hbounded1 : valuesBounded root1)
    (hbounded2 : valuesBounded root2)
    (hsize_eq : size root1 = size root2)
    (hsize_le : size root1 ≤ 10000)
    (hperm : (values root1).Perm (values root2))
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root1 : ℤ)), ∀ r1 r2, Aegis.KthSmallest.kth_smallest root1 k = ok r1 →
      Aegis.KthSmallest.kth_smallest root2 k = ok r2 → r1.val = r2.val) := by
  sorry

/-- If kth_smallest(root, k1) returns a result r1 and kth_smallest(root, k2) returns a result r2, then r1 < r2.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; and k1, k2 are integers with 1 <= k1 < k2 <= size(root). -/
theorem spec_7 (root : Tree) (k1 k2 : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk1_lo : 1 ≤ k1.val)
    (hk_lt : k1.val < k2.val)
    (hk2_hi : k2.val ≤ (size root : ℤ)) :
    ∀ r1 r2, Aegis.KthSmallest.kth_smallest root k1 = ok r1 →
      Aegis.KthSmallest.kth_smallest root k2 = ok r2 → r1.val < r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (k1 k2 : Std.I64)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk1_lo : 1 ≤ k1.val)
    (hk_lt : k1.val < k2.val)
    (hk2_hi : k2.val ≤ (size root : ℤ)), ∀ r1 r2, Aegis.KthSmallest.kth_smallest root k1 = ok r1 →
      Aegis.KthSmallest.kth_smallest root k2 = ok r2 → r1.val < r2.val) := by
  sorry

/-- Whenever kth_smallest(root, k) returns a result r, r = v.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; k is an integer with 1 <= k <= size(root); root is a node with value v, left subtree L, and right subtree R, so root = Node(v, L, R); and k = size(L) + 1. -/
theorem spec_8 (root : Tree) (k v : Std.I64) (L R : Tree)
    (hroot : root = Tree.Node v L R)
    (hk_eq : k.val = (size L : ℤ) + 1)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)) :
    ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val = v.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (k v : Std.I64) (L R : Tree)
    (hroot : root = Tree.Node v L R)
    (hk_eq : k.val = (size L : ℤ) + 1)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ (size root : ℤ)), ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val = v.val) := by
  sorry

/-- Whenever kth_smallest(root, k) returns a result r, r occurs as a node value in the left subtree L, and therefore r < v.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; k is an integer with 1 <= k <= size(root); root = Node(v, L, R); and 1 <= k <= size(L). -/
theorem spec_9 (root : Tree) (k v : Std.I64) (L R : Tree)
    (hroot : root = Tree.Node v L R)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_L_hi : k.val ≤ (size L : ℤ)) :
    ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val ∈ values L ∧ r.val < v.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (k v : Std.I64) (L R : Tree)
    (hroot : root = Tree.Node v L R)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_lo : 1 ≤ k.val)
    (hk_L_hi : k.val ≤ (size L : ℤ)), ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val ∈ values L ∧ r.val < v.val) := by
  sorry

/-- Whenever kth_smallest(root, k) returns a result r, r occurs as a node value in the right subtree R, and therefore r > v.
  Preconditions: root is a binary search tree in the strict sense: for every node with value v, every value in its left subtree is strictly less than v, and every value in its right subtree is strictly greater than v; every node value is an integer between 0 and 10000 inclusive; size(root) <= 10000; k is an integer with 1 <= k <= size(root); root = Node(v, L, R); and size(L) + 1 < k <= size(root). -/
theorem spec_10 (root : Tree) (k v : Std.I64) (L R : Tree)
    (hroot : root = Tree.Node v L R)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_L_lt : (size L : ℤ) + 1 < k.val)
    (hk_hi : k.val ≤ (size root : ℤ)) :
    ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val ∈ values R ∧ v.val < r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (k v : Std.I64) (L R : Tree)
    (hroot : root = Tree.Node v L R)
    (hbst : IsBST root)
    (hbounded : valuesBounded root)
    (hsize : size root ≤ 10000)
    (hk_L_lt : (size L : ℤ) + 1 < k.val)
    (hk_hi : k.val ≤ (size root : ℤ)), ∀ r, Aegis.KthSmallest.kth_smallest root k = ok r → r.val ∈ values R ∧ v.val < r.val) := by
  sorry

end AegisSpec.KthSmallest
