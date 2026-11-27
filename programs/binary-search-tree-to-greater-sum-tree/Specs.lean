import Aegis.BstToGst.Code.Funs

/-!
# Specifications of `Aegis.BstToGst.bst_to_gst`

LeetCode problem `binary-search-tree-to-greater-sum-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BstToGst

open Aegis.BstToGst

inductive Move where

  | left : Move

  | right : Move
  deriving DecidableEq, Repr

def getAt : Tree → List Move → Tree
  | t, [] => t
  | Tree.Null, _ :: _ => Tree.Null
  | Tree.Node _ l _, Move.left :: p => getAt l p
  | Tree.Node _ _ r, Move.right :: p => getAt r p

def keyAt (t : Tree) (p : List Move) : Option Int :=
  match getAt t p with
  | Tree.Null => none
  | Tree.Node v _ _ => some v.val

def nodeKeys : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => nodeKeys l ++ v.val :: nodeKeys r

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => nodeCount l + 1 + nodeCount r

def IsBST : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    (∀ w ∈ nodeKeys l, w < v.val) ∧
      (∀ w ∈ nodeKeys r, v.val < w) ∧
        IsBST l ∧ IsBST r

def Occurs (t : Tree) (v : Int) : Prop := v ∈ nodeKeys t

def IsMaxKey (t : Tree) (v : Int) : Prop := ∀ w ∈ nodeKeys t, w ≤ v

def totalSum (t : Tree) : Int := (nodeKeys t).sum

def sumGreater (t : Tree) (v : Int) : Int :=
  ((nodeKeys t).filter (fun w => decide (v < w))).sum

def sumBetween (t : Tree) (lo hi : Int) : Int :=
  ((nodeKeys t).filter (fun w => decide (lo ≤ w ∧ w < hi))).sum

/-- The function returns a result r (it does not fail). For every finite path p of left/right moves from the root (the empty path denotes the root), the node at p in r is Null if and only if the node at p in root is Null. Moreover, for every non-null node u of root, if v is the key of u and p is the path of u, then the node at p in r is non-null and has key v + G(v), where G(v) is the sum of all keys w occurring in root with w > v (and G(v) = 0 if no such key exists).
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_1 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      (∀ p : List Move, getAt r p = Tree.Null ↔ getAt root p = Tree.Null) ∧
        (∀ (p : List Move) (v : Int), keyAt root p = some v →
          keyAt r p = some (v + sumGreater root v)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      (∀ p : List Move, getAt r p = Tree.Null ↔ getAt root p = Tree.Null) ∧
        (∀ (p : List Move) (v : Int), keyAt root p = some v →
          keyAt r p = some (v + sumGreater root v))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (an Ok value, not a failure); in particular there is no panic, out-of-bounds access, or 64-bit overflow.
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_2 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r) := by
  sorry

/-- The function returns a result r such that for every finite path p of left/right moves from the root, the node at p in r is Null exactly when the node at p in root is Null (so r has the same pattern of present and absent children as root).
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_3 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ p : List Move, getAt r p = Tree.Null ↔ getAt root p = Tree.Null := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ p : List Move, getAt r p = Tree.Null ↔ getAt root p = Tree.Null) := by
  sorry

/-- The function returns a result r such that for every non-null node u of root, if v is the key of u and u' is the node of r at the same path, then the key of u' is v + sum{ w | w is a key of some node of root and w > v } (the sum is 0 if no key is greater than v).
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_4 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p : List Move) (v : Int), keyAt root p = some v →
        keyAt r p = some (v + sumGreater root v) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p : List Move) (v : Int), keyAt root p = some v →
        keyAt r p = some (v + sumGreater root v)) := by
  sorry

/-- Let S be the sum of all keys of non-null nodes of root. The function returns a result r such that every key y of a non-null node of r satisfies 0 <= y <= S.
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_5 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ y ∈ nodeKeys r, 0 ≤ y ∧ y ≤ totalSum root := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ y ∈ nodeKeys r, 0 ≤ y ∧ y ≤ totalSum root) := by
  sorry

/-- The function returns a result r such that for every non-null node u of root with key v, the key of the node at the same path in r is at least v.
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_6 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p : List Move) (v : Int), keyAt root p = some v →
        ∃ y : Int, keyAt r p = some y ∧ v ≤ y := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p : List Move) (v : Int), keyAt root p = some v →
        ∃ y : Int, keyAt r p = some y ∧ v ≤ y) := by
  sorry

/-- The function returns a result r such that for every non-null node u of root whose key v is not the maximum key among all keys in root, the key of the node at the same path in r is strictly greater than v.
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_7 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p : List Move) (v : Int), keyAt root p = some v → ¬ IsMaxKey root v →
        ∃ y : Int, keyAt r p = some y ∧ v < y := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p : List Move) (v : Int), keyAt root p = some v → ¬ IsMaxKey root v →
        ∃ y : Int, keyAt r p = some y ∧ v < y) := by
  sorry

/-- Let k_0, k_1, ..., k_{n-1} be the keys of the non-null nodes of root in in-order (left subtree, then node, then right subtree). Let y_0, y_1, ..., y_{n-1} be the keys of the non-null nodes of r in the same in-order. Then for every i with 0 <= i < n-1, y_i >= y_{i+1}.
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_8 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (i : Nat) (a b : Int), (nodeKeys r)[i]? = some a →
        (nodeKeys r)[i + 1]? = some b → a ≥ b := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (i : Nat) (a b : Int), (nodeKeys r)[i]? = some a →
        (nodeKeys r)[i + 1]? = some b → a ≥ b) := by
  sorry

/-- The function returns a result r such that for any two non-null nodes u and u' of root with keys a < b, if y and y' are the keys of the nodes at their same paths in r, then y - y' = sum{ w | w is a key of some node of root and a <= w < b }.
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_9 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p p' : List Move) (a b y y' : Int), keyAt root p = some a →
        keyAt root p' = some b → a < b → keyAt r p = some y → keyAt r p' = some y' →
          y - y' = sumBetween root a b := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∀ (p p' : List Move) (a b y y' : Int), keyAt root p = some a →
        keyAt root p' = some b → a < b → keyAt r p = some y → keyAt r p' = some y' →
          y - y' = sumBetween root a b) := by
  sorry

/-- The function returns results r1 and r2 for root1 and root2. For every key v in the common key set, and for any node u1 of root1 and u2 of root2 both having key v, the key at the same path as u1 in r1 equals the key at the same path as u2 in r2.
  Preconditions: root1 and root2 are binary search trees, each with between 1 and 100 non-null nodes; every key in root1 or root2 is an integer with 0 <= key <= 100; all keys in root1 are pairwise distinct and all keys in root2 are pairwise distinct; and the set of keys of root1 is equal to the set of keys of root2. -/
theorem spec_10 (root1 root2 : Tree) (hbst1 : IsBST root1) (hbst2 : IsBST root2)
    (hsize1_lo : 1 ≤ nodeCount root1) (hsize1_hi : nodeCount root1 ≤ 100)
    (hsize2_lo : 1 ≤ nodeCount root2) (hsize2_hi : nodeCount root2 ≤ 100)
    (hkey_range : ∀ k, (k ∈ nodeKeys root1 ∨ k ∈ nodeKeys root2) → 0 ≤ k ∧ k ≤ 100)
    (hkey_nd1 : (nodeKeys root1).Nodup) (hkey_nd2 : (nodeKeys root2).Nodup)
    (hkey_set : ∀ v : Int, Occurs root1 v ↔ Occurs root2 v) :
    ∃ r1 r2 : Tree, bst_to_gst root1 = ok r1 ∧ bst_to_gst root2 = ok r2 ∧
      ∀ (p1 p2 : List Move) (v y1 y2 : Int), keyAt root1 p1 = some v →
        keyAt root2 p2 = some v → keyAt r1 p1 = some y1 → keyAt r2 p2 = some y2 →
          y1 = y2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root1 root2 : Tree) (hbst1 : IsBST root1) (hbst2 : IsBST root2)
    (hsize1_lo : 1 ≤ nodeCount root1) (hsize1_hi : nodeCount root1 ≤ 100)
    (hsize2_lo : 1 ≤ nodeCount root2) (hsize2_hi : nodeCount root2 ≤ 100)
    (hkey_range : ∀ k, (k ∈ nodeKeys root1 ∨ k ∈ nodeKeys root2) → 0 ≤ k ∧ k ≤ 100)
    (hkey_nd1 : (nodeKeys root1).Nodup) (hkey_nd2 : (nodeKeys root2).Nodup)
    (hkey_set : ∀ v : Int, Occurs root1 v ↔ Occurs root2 v), ∃ r1 r2 : Tree, bst_to_gst root1 = ok r1 ∧ bst_to_gst root2 = ok r2 ∧
      ∀ (p1 p2 : List Move) (v y1 y2 : Int), keyAt root1 p1 = some v →
        keyAt root2 p2 = some v → keyAt r1 p1 = some y1 → keyAt r2 p2 = some y2 →
          y1 = y2) := by
  sorry

/-- Let S be the sum of all keys of non-null nodes of root. The function returns a result r such that there exists a non-null node of r whose key is S.
  Preconditions: root is a binary search tree: for every node, all keys in its left subtree are strictly less than its key and all keys in its right subtree are strictly greater than its key, and the same property holds recursively; the number of non-null nodes in root is between 1 and 100; every key in root is an integer with 0 <= key <= 100; all keys in root are pairwise distinct. -/
theorem spec_11 (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup) :
    ∃ r : Tree, bst_to_gst root = ok r ∧
      ∃ p : List Move, keyAt r p = some (totalSum root) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (hbst : IsBST root)
    (hsize_lo : 1 ≤ nodeCount root) (hsize_hi : nodeCount root ≤ 100)
    (hkey_range : ∀ k ∈ nodeKeys root, 0 ≤ k ∧ k ≤ 100)
    (hkey_nd : (nodeKeys root).Nodup), ∃ r : Tree, bst_to_gst root = ok r ∧
      ∃ p : List Move, keyAt r p = some (totalSum root)) := by
  sorry

end AegisSpec.BstToGst
