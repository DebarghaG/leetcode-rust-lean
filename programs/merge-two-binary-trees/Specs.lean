import Aegis.MergeTrees.Code.Funs

/-!
# Specifications of `Aegis.MergeTrees.merge_trees`

LeetCode problem `merge-two-binary-trees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MergeTrees

open Aegis.MergeTrees (Tree merge_trees)

inductive Step where

  | L : Step

  | R : Step
  deriving DecidableEq, Repr

def size : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + size l + size r

def depth : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + max (depth l) (depth r)

def hasNodeB : Tree → List Step → Bool
  | .Null, _ => false
  | .Node _ _ _, [] => true
  | .Node _ l _, .L :: p => hasNodeB l p
  | .Node _ _ r, .R :: p => hasNodeB r p

abbrev hasNode (T : Tree) (p : List Step) : Prop := hasNodeB T p = true

def valueAt : Tree → List Step → Option ℤ
  | .Null, _ => none
  | .Node v _ _, [] => some v.val
  | .Node _ l _, .L :: p => valueAt l p
  | .Node _ _ r, .R :: p => valueAt r p

def valsWithin (lo hi : ℤ) : Tree → Prop
  | .Null => True
  | .Node v l r => lo ≤ v.val ∧ v.val ≤ hi ∧ valsWithin lo hi l ∧ valsWithin lo hi r

def overlap : Tree → Tree → Nat
  | .Null, _ => 0
  | _, .Null => 0
  | .Node _ l r, .Node _ l' r' => 1 + overlap l l' + overlap r r'

inductive Merge : Tree → Tree → Tree → Prop where

  | null_right (A : Tree) : Merge A A .Null

  | null_left (B : Tree) : Merge B .Null B

  | node {v1 v2 i : I64} (hi : i.val = v1.val + v2.val)
      {Al Ar Bl Br Cl Cr : Tree}
      (hl : Merge Cl Al Bl) (hr : Merge Cr Ar Br) :
      Merge (.Node i Cl Cr) (.Node v1 Al Ar) (.Node v2 Bl Br)

/-- merge_trees returns Result.ok r for some tree r, where r is the unique tree T such that Merge(T, root1, root2). The relation Merge is defined by: (a) for every tree A, Merge(T, A, Null) holds iff T = A; (b) for every tree B, Merge(T, Null, B) holds iff T = B; (c) for A = Node(v1, Al, Ar) and B = Node(v2, Bl, Br), Merge(T, A, B) holds iff T = Node(v1+v2, Cl, Cr) for some trees Cl, Cr with Merge(Cl, Al, Bl) and Merge(Cr, Ar, Br). Clauses (a) and (b) fix the result to the non-null input when the other input is Null; clause (c) sums the values of the two overlapping roots and recurses on the corresponding left and right subtrees.
  Preconditions: root1 and root2 are finite trees of type Tree. size(root1) ≤ 2000 and size(root2) ≤ 2000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r). Every node value occurring in root1 or in root2 lies in the closed interval [-10000, 10000]. -/
theorem spec_1 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2) :
    ∃ r, merge_trees root1 root2 = ok r ∧ Merge r root1 root2 ∧
      ∀ T, Merge T root1 root2 → T = r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2), ∃ r, merge_trees root1 root2 = ok r ∧ Merge r root1 root2 ∧
      ∀ T, Merge T root1 root2 → T = r) := by
  sorry

/-- merge_trees does not fail: for every root1 and root2 satisfying the preconditions, it terminates and returns Result.ok r for some Tree r. In particular there is no panic, no out-of-bounds access, no i64 overflow, and no divergence.
  Preconditions: Same as spec_1: both trees have size ≤ 2000, and all node values lie in [-10000, 10000]. -/
theorem spec_2 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2) :
    ∃ r, merge_trees root1 root2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2), ∃ r, merge_trees root1 root2 = ok r) := by
  sorry

/-- If root2 = Null, then merge_trees returns Result.ok r where r is structurally equal to root1 (same shape and same node values at every position).
  Preconditions: Same as spec_1. -/
theorem spec_3 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (hnull : root2 = .Null) :
    ∃ r, merge_trees root1 root2 = ok r ∧ r = root1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (hnull : root2 = .Null), ∃ r, merge_trees root1 root2 = ok r ∧ r = root1) := by
  sorry

/-- If root1 = Null, then merge_trees returns Result.ok r where r is structurally equal to root2 (same shape and same node values at every position).
  Preconditions: Same as spec_1. -/
theorem spec_4 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (hnull : root1 = .Null) :
    ∃ r, merge_trees root1 root2 = ok r ∧ r = root2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (hnull : root1 = .Null), ∃ r, merge_trees root1 root2 = ok r ∧ r = root2) := by
  sorry

/-- Whenever merge_trees(root1, root2) returns Result.ok r and merge_trees(root2, root1) returns Result.ok r', the trees r and r' are structurally equal (identical shape and identical values at every position).
  Preconditions: Same as spec_1. -/
theorem spec_5 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r r' : Tree)
    (h : merge_trees root1 root2 = ok r) (h' : merge_trees root2 root1 = ok r') :
    r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r r' : Tree)
    (h : merge_trees root1 root2 = ok r) (h' : merge_trees root2 root1 = ok r'), r = r') := by
  sorry

/-- Whenever merge_trees returns Result.ok r, for every path p (a finite sequence of steps, each L or R) the tree r has a node at p if and only if root1 has a node at p or root2 has a node at p. A tree has a node at the empty path iff it is not Null; T has a node at L::p iff T = Node(v,l,rr) and l has a node at p; T has a node at R::p iff T = Node(v,l,rr) and rr has a node at p.
  Preconditions: Same as spec_1. -/
theorem spec_6 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) (p : List Step) :
    hasNode r p ↔ hasNode root1 p ∨ hasNode root2 p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) (p : List Step), hasNode r p ↔ hasNode root1 p ∨ hasNode root2 p) := by
  sorry

/-- Whenever merge_trees returns Result.ok r, for every path p at which both root1 and root2 have a node, r has a node at p whose value is valueAt(root1,p) + valueAt(root2,p). Here valueAt(T,p) denotes the value of the node of T at path p: valueAt(Node(v,_,_), []) = v; valueAt(Node(_,l,_), L::p) = valueAt(l,p); valueAt(Node(_,_,rr), R::p) = valueAt(rr,p).
  Preconditions: Same as spec_1. -/
theorem spec_7 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) (p : List Step) (x y : ℤ)
    (hx : valueAt root1 p = some x) (hy : valueAt root2 p = some y) :
    valueAt r p = some (x + y) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) (p : List Step) (x y : ℤ)
    (hx : valueAt root1 p = some x) (hy : valueAt root2 p = some y), valueAt r p = some (x + y)) := by
  sorry

/-- Whenever merge_trees returns Result.ok r, for every path p at which exactly one of root1 and root2 has a node, r has a node at p, and its value equals that of the one input that has a node there: valueAt(r,p) = valueAt(root1,p) if root1 has a node at p and root2 does not, and valueAt(r,p) = valueAt(root2,p) if root2 has a node at p and root1 does not. (valueAt is the path-indexed node value defined in spec_7.)
  Preconditions: Same as spec_1. -/
theorem spec_8 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) :
    (∀ p, hasNode root1 p → ¬ hasNode root2 p → valueAt r p = valueAt root1 p) ∧
      (∀ p, hasNode root2 p → ¬ hasNode root1 p → valueAt r p = valueAt root2 p) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r), (∀ p, hasNode root1 p → ¬ hasNode root2 p → valueAt r p = valueAt root1 p) ∧
      (∀ p, hasNode root2 p → ¬ hasNode root1 p → valueAt r p = valueAt root2 p)) := by
  sorry

/-- Whenever merge_trees returns Result.ok r, every node value of r lies in the closed interval [-20000, 20000]; formally, for every path p at which r has a node, -20000 ≤ valueAt(r,p) ≤ 20000. (valueAt is defined in spec_7.)
  Preconditions: Same as spec_1. -/
theorem spec_9 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) (p : List Step) (x : ℤ)
    (hx : valueAt r p = some x) :
    -20000 ≤ x ∧ x ≤ 20000 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) (p : List Step) (x : ℤ)
    (hx : valueAt r p = some x), -20000 ≤ x ∧ x ≤ 20000) := by
  sorry

/-- Whenever merge_trees returns Result.ok r, size(r) ≤ size(root1) + size(root2), where size(Null)=0 and size(Node(v,l,rr))=1+size(l)+size(rr).
  Preconditions: Same as spec_1. -/
theorem spec_10 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) :
    size r ≤ size root1 + size root2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r), size r ≤ size root1 + size root2) := by
  sorry

/-- Whenever merge_trees returns Result.ok r, size(r) ≥ size(root1) and size(r) ≥ size(root2); equivalently size(r) ≥ max(size(root1), size(root2)). (size is defined in spec_10.)
  Preconditions: Same as spec_1. -/
theorem spec_11 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) :
    size root1 ≤ size r ∧ size root2 ≤ size r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r), size root1 ≤ size r ∧ size root2 ≤ size r) := by
  sorry

/-- Whenever merge_trees returns Result.ok r, depth(r) = max(depth(root1), depth(root2)), where depth(Null)=0 and depth(Node(v,l,rr))=1+max(depth(l),depth(rr)).
  Preconditions: Same as spec_1. -/
theorem spec_12 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) :
    depth r = max (depth root1) (depth root2) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r), depth r = max (depth root1) (depth root2)) := by
  sorry

/-- Whenever merge_trees returns Result.ok r, size(r) = size(root1) + size(root2) - overlap(root1, root2), where overlap(T1,T2) is the number of paths p at which both T1 and T2 have a node. Equivalently, the merged tree has exactly one node for each position occupied in at least one input.
  Preconditions: Same as spec_1: root1 and root2 are finite trees of type Tree with size(root1) ≤ 2000 and size(root2) ≤ 2000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r); every node value in root1 or root2 lies in [-10000,10000]. -/
theorem spec_13 (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r) :
    size r = size root1 + size root2 - overlap root1 root2 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root1 root2 : Tree)
    (h1 : size root1 ≤ 2000) (h2 : size root2 ≤ 2000)
    (hv1 : valsWithin (-10000) 10000 root1) (hv2 : valsWithin (-10000) 10000 root2)
    (r : Tree) (h : merge_trees root1 root2 = ok r), size r = size root1 + size root2 - overlap root1 root2) := by
  sorry

end AegisSpec.MergeTrees
