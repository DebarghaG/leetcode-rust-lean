import Aegis.LargestValues.Code.Funs

/-!
# Specifications of `Aegis.LargestValues.largest_values`

LeetCode problem `find-largest-value-in-each-tree-row`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LargestValues

open Aegis.LargestValues (largest_values)

def size : Aegis.LargestValues.Tree → ℕ
  | .Null => 0
  | .Node _ l r => 1 + size l + size r

def height : Aegis.LargestValues.Tree → ℕ
  | .Null => 0
  | .Node _ l r => 1 + max (height l) (height r)

def valuesAtDepth : Aegis.LargestValues.Tree → ℕ → List ℤ
  | .Null, _ => []
  | .Node v _ _, 0 => [v.val]
  | .Node _ l r, k + 1 => valuesAtDepth l k ++ valuesAtDepth r k

def AtDepth : Aegis.LargestValues.Tree → ℕ → ℤ → Prop
  | .Null, _, _ => False
  | .Node v _ _, 0, x => x = v.val
  | .Node _ l r, k + 1, x => AtDepth l k x ∨ AtDepth r k x

def nodeValues : Aegis.LargestValues.Tree → List ℤ
  | .Null => []
  | .Node v l r => v.val :: (nodeValues l ++ nodeValues r)

def listMax : List ℤ → Option ℤ
  | [] => none
  | x :: xs => some (xs.foldl (fun a y => max a y) x)

def i64OfInt (x : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

def mirror : Aegis.LargestValues.Tree → Aegis.LargestValues.Tree
  | .Null => .Null
  | .Node v l r => .Node v (mirror r) (mirror l)

def addConst (c : ℤ) : Aegis.LargestValues.Tree → Aegis.LargestValues.Tree
  | .Null => .Null
  | .Node v l r =>
      .Node (IScalar.wrapping_add v (i64OfInt c)) (addConst c l) (addConst c r)

def SameShapeLe : Aegis.LargestValues.Tree → Aegis.LargestValues.Tree → Prop
  | .Null, .Null => True
  | .Node vA lA rA, .Node vB lB rB => vA.val ≤ vB.val ∧ SameShapeLe lA lB ∧ SameShapeLe rA rB
  | _, _ => False

def vecAt (a : alloc.vec.Vec Std.I64) (d : ℕ) : ℤ :=
  match a.val[d]? with
  | some x => x.val
  | none => 0

/-- The function returns a result res and does not fail. Let height(root) be 0 if root = Null, and 1 + max(height(l), height(right)) if root = Node(v, l, right). Let depth be defined by: the root has depth 0, and a child of a node at depth k has depth k+1. Then len(res) = height(root), and for every d with 0 <= d < len(res), res[d] is the largest value among all nodes of root at depth d: (i) every node x at depth d satisfies x.val <= res[d], and (ii) there exists a node y at depth d with y.val = res[d].
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. -/
theorem spec_1 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1) :
    ∃ res : alloc.vec.Vec Std.I64,
      largest_values root = ok res ∧
        res.val.length = height root ∧
        ∀ d, d < res.val.length →
          (∀ x, AtDepth root d x → x ≤ vecAt res d) ∧
            (∃ x, AtDepth root d x ∧ x = vecAt res d) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1), ∃ res : alloc.vec.Vec Std.I64,
      largest_values root = ok res ∧
        res.val.length = height root ∧
        ∀ d, d < res.val.length →
          (∀ x, AtDepth root d x → x ≤ vecAt res d) ∧
            (∃ x, AtDepth root d x ∧ x = vecAt res d)) := by
  sorry

/-- For every such root, the call largest_values(root) returns some result r; it does not fail.
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. -/
theorem spec_2 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1) :
    ∃ r : alloc.vec.Vec Std.I64, largest_values root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1), ∃ r : alloc.vec.Vec Std.I64, largest_values root = ok r) := by
  sorry

/-- Whenever the function returns a result res, len(res) = height(root), where height(Null) = 0 and height(Node(v, left, right)) = 1 + max(height(left), height(right)). Equivalently, len(res) is the number of distinct depths at which nodes of root occur, with 0 rows for the empty tree.
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. -/
theorem spec_3 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (res : alloc.vec.Vec Std.I64) (hres : largest_values root = ok res) :
    res.val.length = height root := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (res : alloc.vec.Vec Std.I64) (hres : largest_values root = ok res), res.val.length = height root) := by
  sorry

/-- Whenever the function returns a result r, for every d with 0 <= d < len(r) and every node x at depth d in root, we have x.val <= r[d]. Depth is 0-based from the root: the root has depth 0 and a child of a depth-k node has depth k+1.
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. -/
theorem spec_4 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (r : alloc.vec.Vec Std.I64) (hr : largest_values root = ok r) :
    ∀ d, d < r.val.length → ∀ x, AtDepth root d x → x ≤ vecAt r d := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (r : alloc.vec.Vec Std.I64) (hr : largest_values root = ok r), ∀ d, d < r.val.length → ∀ x, AtDepth root d x → x ≤ vecAt r d) := by
  sorry

/-- Whenever the function returns a result r, for every d with 0 <= d < len(r), there exists a node x at depth d in root such that x.val = r[d].
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. -/
theorem spec_5 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (r : alloc.vec.Vec Std.I64) (hr : largest_values root = ok r) :
    ∀ d, d < r.val.length → ∃ x, AtDepth root d x ∧ x = vecAt r d := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (r : alloc.vec.Vec Std.I64) (hr : largest_values root = ok r), ∀ d, d < r.val.length → ∃ x, AtDepth root d x ∧ x = vecAt r d) := by
  sorry

/-- Whenever the function returns a result r and root = Node(v, l, rtree), we have r[0] = v, and for every d with 1 <= d < len(r), r[d] equals the maximum of the values occurring at depth d-1 within the child subtree l together with the values occurring at depth d-1 within the child subtree rtree. Here depth within a child subtree is measured with that child's root at depth 0. A child that has no nodes at that depth contributes no values. In particular, if neither l nor rtree has a node at depth d-1, then d >= len(r).
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. -/
theorem spec_6 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (v : Std.I64) (l rtree : Aegis.LargestValues.Tree) (hroot : root = .Node v l rtree)
    (r : alloc.vec.Vec Std.I64) (hr : largest_values root = ok r) :
    vecAt r 0 = v.val ∧
      (∀ d, 1 ≤ d → d < r.val.length →
        listMax (valuesAtDepth l (d - 1) ++ valuesAtDepth rtree (d - 1)) = some (vecAt r d)) ∧
      (∀ d, 1 ≤ d → valuesAtDepth l (d - 1) = [] → valuesAtDepth rtree (d - 1) = [] →
        r.val.length ≤ d) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (v : Std.I64) (l rtree : Aegis.LargestValues.Tree) (hroot : root = .Node v l rtree)
    (r : alloc.vec.Vec Std.I64) (hr : largest_values root = ok r), vecAt r 0 = v.val ∧
      (∀ d, 1 ≤ d → d < r.val.length →
        listMax (valuesAtDepth l (d - 1) ++ valuesAtDepth rtree (d - 1)) = some (vecAt r d)) ∧
      (∀ d, 1 ≤ d → valuesAtDepth l (d - 1) = [] → valuesAtDepth rtree (d - 1) = [] →
        r.val.length ≤ d)) := by
  sorry

/-- Let mirror(root) be defined by mirror(Null) = Null and mirror(Node(v, left, right)) = Node(v, mirror(right), mirror(left)). Whenever the function returns a result res for root and a result res' for mirror(root), we have len(res) = len(res') and res[d] = res'[d] for every d with 0 <= d < len(res).
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. -/
theorem spec_7 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (res res' : alloc.vec.Vec Std.I64)
    (hres : largest_values root = ok res) (hres' : largest_values (mirror root) = ok res') :
    res.val.length = res'.val.length ∧
      ∀ d, d < res.val.length → vecAt res d = vecAt res' d := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (res res' : alloc.vec.Vec Std.I64)
    (hres : largest_values root = ok res) (hres' : largest_values (mirror root) = ok res'), res.val.length = res'.val.length ∧
      ∀ d, d < res.val.length → vecAt res d = vecAt res' d) := by
  sorry

/-- Let root+c be the tree with the same shape as root in which each node value v is replaced by v+c. Whenever the function returns a result r for root and a result r_c for root+c, we have len(r) = len(r_c) and r_c[d] = r[d] + c for every d with 0 <= d < len(r).
  Preconditions: root is a binary tree with at most 10000 nodes; every node value v satisfies -2^31 <= v <= 2^31 - 1. Let c be an integer such that for every node value v in root, the value v+c also satisfies -2^31 <= v+c <= 2^31 - 1. -/
theorem spec_8 (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (c : ℤ)
    (hc : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x + c ∧ x + c ≤ (2 : ℤ) ^ 31 - 1)
    (r rc : alloc.vec.Vec Std.I64)
    (hr : largest_values root = ok r) (hrc : largest_values (addConst c root) = ok rc) :
    r.val.length = rc.val.length ∧
      ∀ d, d < r.val.length → vecAt rc d = vecAt r d + c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Aegis.LargestValues.Tree) (hnodes : size root ≤ 10000)
    (hvals : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (c : ℤ)
    (hc : ∀ x ∈ nodeValues root, -(2 : ℤ) ^ 31 ≤ x + c ∧ x + c ≤ (2 : ℤ) ^ 31 - 1)
    (r rc : alloc.vec.Vec Std.I64)
    (hr : largest_values root = ok r) (hrc : largest_values (addConst c root) = ok rc), r.val.length = rc.val.length ∧
      ∀ d, d < r.val.length → vecAt rc d = vecAt r d + c) := by
  sorry

/-- Whenever the function returns a result resA for rootA and a result resB for rootB, we have len(resA) = len(resB) and resA[d] <= resB[d] for every d with 0 <= d < len(resA).
  Preconditions: rootA and rootB are binary trees with at most 10000 nodes; every node value in either tree satisfies -2^31 <= v <= 2^31 - 1. The trees have the same shape and rootA is pointwise no larger than rootB: formally, the relation R holds, where R(Null, Null) holds, and R(Node(vA, lA, rightA), Node(vB, lB, rightB)) holds exactly when vA <= vB, R(lA, lB), and R(rightA, rightB). The precondition is R(rootA, rootB). -/
theorem spec_9 (rootA rootB : Aegis.LargestValues.Tree) (hnodesA : size rootA ≤ 10000)
    (hnodesB : size rootB ≤ 10000)
    (hvalsA : ∀ x ∈ nodeValues rootA, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (hvalsB : ∀ x ∈ nodeValues rootB, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (hR : SameShapeLe rootA rootB)
    (resA resB : alloc.vec.Vec Std.I64)
    (hresA : largest_values rootA = ok resA) (hresB : largest_values rootB = ok resB) :
    resA.val.length = resB.val.length ∧
      ∀ d, d < resA.val.length → vecAt resA d ≤ vecAt resB d := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rootA rootB : Aegis.LargestValues.Tree) (hnodesA : size rootA ≤ 10000)
    (hnodesB : size rootB ≤ 10000)
    (hvalsA : ∀ x ∈ nodeValues rootA, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (hvalsB : ∀ x ∈ nodeValues rootB, -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1)
    (hR : SameShapeLe rootA rootB)
    (resA resB : alloc.vec.Vec Std.I64)
    (hresA : largest_values rootA = ok resA) (hresB : largest_values rootB = ok resB), resA.val.length = resB.val.length ∧
      ∀ d, d < resA.val.length → vecAt resA d ≤ vecAt resB d) := by
  sorry

end AegisSpec.LargestValues
