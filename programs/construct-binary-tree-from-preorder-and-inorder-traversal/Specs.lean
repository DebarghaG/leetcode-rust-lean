import Aegis.BuildTree.Code.Funs

/-!
# Specifications of `Aegis.BuildTree.build_tree`

LeetCode problem `construct-binary-tree-from-preorder-and-inorder-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.BuildTree

namespace AegisSpec.BuildTree

def pre : Tree → List I64
  | .Null => []
  | .Node v l r => v :: (pre l ++ pre r)

def ino : Tree → List I64
  | .Null => []
  | .Node v l r => ino l ++ v :: ino r

def sz : Tree → Nat
  | .Null => 0
  | .Node _ l r => sz l + sz r + 1

def nodeCount (x : Int) (t : Tree) : Nat := (pre t).countP fun v => v.val == x

def sliceCount (x : Int) (s : Slice I64) : Nat := s.val.countP fun v => v.val == x

/-- Whenever build_tree(preorder, inorder) returns a result r, pre(r) = preorder and ino(r) = inorder.
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_1 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r) :
    pre r = preorder.val ∧ ino r = inorder.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r), pre r = preorder.val ∧ ino r = inorder.val) := by
  sorry

/-- build_tree(preorder, inorder) returns a result r (the computation does not fail: no panic, no integer overflow, no out-of-bounds access).
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_2 (preorder inorder : Slice I64)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val) :
    ∃ r : Tree, build_tree preorder inorder = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (preorder inorder : Slice I64)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val), ∃ r : Tree, build_tree preorder inorder = ok r) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, sz(r) = len(preorder).
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_3 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r) :
    sz r = preorder.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r), sz r = preorder.val.length) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, for every integer x, the number of nodes of r whose value is x equals the number of indices i with 0 <= i < len(inorder) and inorder[i] = x.
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_4 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r) :
    ∀ x : Int, nodeCount x r = sliceCount x inorder := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r), ∀ x : Int, nodeCount x r = sliceCount x inorder) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, for any two distinct nodes u and v of r, the value of u differs from the value of v (so no value occurs more than once in r).
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_5 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r) :
    (pre r).Nodup := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r), (pre r).Nodup) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, let v = preorder[0] and let k be the unique index with 0 <= k < len(inorder) and inorder[k] = v. Then r = Node(v, L, R) for some trees L and R, and ino(L) = inorder[0..k] (the list consisting of inorder[0], inorder[1], ..., inorder[k-1], of length k).
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_6 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k) :
    ∃ L R : Tree, r = .Node v L R ∧ ino L = inorder.val.take k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k), ∃ L R : Tree, r = .Node v L R ∧ ino L = inorder.val.take k) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, let v = preorder[0] and let k be the unique index with inorder[k] = v. Then r = Node(v, L, R) for some trees L and R, and ino(R) = inorder[k+1..len(inorder)] (the list consisting of inorder[k+1], ..., inorder[len(inorder)-1], of length len(inorder)-1-k).
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_7 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k) :
    ∃ L R : Tree, r = .Node v L R ∧ ino R = inorder.val.drop (k + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k), ∃ L R : Tree, r = .Node v L R ∧ ino R = inorder.val.drop (k + 1)) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, let v = preorder[0] and let k be the unique index with inorder[k] = v. Then r = Node(v, L, R) for some trees L and R, and pre(L) = preorder[1..k+1] (the list consisting of preorder[1], ..., preorder[k], of length k).
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_8 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k) :
    ∃ L R : Tree, r = .Node v L R ∧ pre L = (preorder.val.drop 1).take k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k), ∃ L R : Tree, r = .Node v L R ∧ pre L = (preorder.val.drop 1).take k) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, let v = preorder[0] and let k be the unique index with inorder[k] = v. Then r = Node(v, L, R) for some trees L and R, and pre(R) = preorder[k+1..len(preorder)] (the list consisting of preorder[k+1], ..., preorder[len(preorder)-1], of length len(preorder)-1-k).
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_9 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k) :
    ∃ L R : Tree, r = .Node v L R ∧ pre R = (preorder.val.drop 1).drop k := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k), ∃ L R : Tree, r = .Node v L R ∧ pre R = (preorder.val.drop 1).drop k) := by
  sorry

/-- Whenever build_tree(preorder, inorder) returns a result r, let v = preorder[0] and let k be the unique index with inorder[k] = v. Then r = Node(v, L, R) for some trees L and R, sz(L) = k, and sz(R) = len(preorder) - 1 - k.
  Preconditions: len(inorder) = len(preorder); 1 <= len(preorder) <= 3000; for every i with 0 <= i < len(preorder), -3000 <= preorder[i] <= 3000; for every i with 0 <= i < len(inorder), -3000 <= inorder[i] <= 3000; the entries of preorder are pairwise distinct; the entries of inorder are pairwise distinct; every value occurring in inorder also occurs in preorder; and there exists a Tree T with pre(T) = preorder and ino(T) = inorder. Notation: for a Tree t, pre(t) is the list of node values of t in preorder (root, then left subtree, then right subtree); ino(t) is the list of node values in inorder (left subtree, then root, then right subtree); sz(t) is the number of Node constructors in t; rev(xs) is the reverse of list xs. -/
theorem spec_10 (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k) :
    ∃ L R : Tree, r = .Node v L R ∧ sz L = k ∧ sz R = preorder.val.length - 1 - k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (preorder inorder : Slice I64) (r : Tree)
    (hlen : inorder.val.length = preorder.val.length)
    (hlen_lo : 1 ≤ preorder.val.length)
    (hlen_hi : preorder.val.length ≤ 3000)
    (hpre_bounds : ∀ v ∈ preorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hino_bounds : ∀ v ∈ inorder.val, -3000 ≤ v.val ∧ v.val ≤ 3000)
    (hpre_nd : preorder.val.Nodup)
    (hino_nd : inorder.val.Nodup)
    (hsubset : ∀ v ∈ inorder.val, v ∈ preorder.val)
    (hshape : ∃ T : Tree, pre T = preorder.val ∧ ino T = inorder.val)
    (hr : build_tree preorder inorder = ok r)
    (v : I64) (hv : preorder.val.head? = some v)
    (k : Nat) (hk : inorder.val[k]? = some v)
    (hk_unique : ∀ j : Nat, inorder.val[j]? = some v → j = k), ∃ L R : Tree, r = .Node v L R ∧ sz L = k ∧ sz R = preorder.val.length - 1 - k) := by
  sorry

end AegisSpec.BuildTree
