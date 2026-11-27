import Aegis.MinDepth.Code.Funs

/-!
# Specifications of `Aegis.MinDepth.min_depth`

LeetCode problem `minimum-depth-of-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinDepth

open Aegis.MinDepth

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

def nodeValues : Tree → List ℤ
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (nodeValues l ++ nodeValues r)

def valuesBounded (t : Tree) : Prop := ∀ v ∈ nodeValues t, -1000 ≤ v ∧ v ≤ 1000

def D : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ Tree.Null Tree.Null => 1
  | Tree.Node _ Tree.Null r => 1 + D r
  | Tree.Node _ l Tree.Null => 1 + D l
  | Tree.Node _ l r => 1 + min (D l) (D r)

def leafDepths : Tree → List Nat
  | Tree.Null => []
  | Tree.Node _ Tree.Null Tree.Null => [1]
  | Tree.Node _ l r => (leafDepths l).map (· + 1) ++ (leafDepths r).map (· + 1)

def IsLeaf (t : Tree) : Prop := ∃ v, t = Tree.Node v Tree.Null Tree.Null

inductive Shape where
  | null : Shape
  | node : Shape → Shape → Shape

def shapeOf : Tree → Shape
  | Tree.Null => Shape.null
  | Tree.Node _ l r => Shape.node (shapeOf l) (shapeOf r)

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

def rightChain : List Std.I64 → Tree
  | [] => Tree.Null
  | v :: vs => Tree.Node v Tree.Null (rightChain vs)

/-- Let D(t) be defined by D(Null)=0 and, for non-null t, D(t)=min{k | t contains a leaf whose path from the root of t contains exactly k nodes}, where a leaf is a Node(v, Null, Null). The function returns a result r and r = D(root).
  Preconditions: root is a finite Tree with at most 100000 Node constructors, and every node value v satisfies -1000 <= v <= 1000. -/
theorem spec_1 (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root) :
    ∃ r, min_depth root = ok r ∧ r.val = (D root : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root), ∃ r, min_depth root = ok r ∧ r.val = (D root : ℤ)) := by
  sorry

/-- Let n be the number of Node constructors in root. Whenever min_depth(root) returns a result r, 0 <= r <= n; moreover, if root is non-null then 1 <= r <= n.
  Preconditions: root is a finite Tree with at most 100000 Node constructors, and every node value v satisfies -1000 <= v <= 1000. -/
theorem spec_2 (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root) :
    (∀ r, min_depth root = ok r → 0 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ)) ∧
      (root ≠ Tree.Null →
        ∀ r, min_depth root = ok r → 1 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ)) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root), (∀ r, min_depth root = ok r → 0 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ)) ∧
      (root ≠ Tree.Null →
        ∀ r, min_depth root = ok r → 1 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ))) := by
  sorry

/-- If root is non-null and min_depth(root) returns a result r, then root contains a leaf (a node Node(v, Null, Null)) whose path from the root of root contains exactly r nodes.
  Preconditions: root is a finite Tree with at most 100000 Node constructors, and every node value v satisfies -1000 <= v <= 1000. -/
theorem spec_3 (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root) :
    root ≠ Tree.Null →
      ∀ r, min_depth root = ok r → ∃ d ∈ leafDepths root, (d : ℤ) = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root), root ≠ Tree.Null →
      ∀ r, min_depth root = ok r → ∃ d ∈ leafDepths root, (d : ℤ) = r.val) := by
  sorry

/-- If root is non-null and min_depth(root) returns a result r, then for every leaf occurrence l in root, the path from the root of root to l contains at least r nodes.
  Preconditions: root is a finite Tree with at most 100000 Node constructors, and every node value v satisfies -1000 <= v <= 1000. -/
theorem spec_4 (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root) :
    root ≠ Tree.Null →
      ∀ r, min_depth root = ok r → ∀ d ∈ leafDepths root, r.val ≤ (d : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root), root ≠ Tree.Null →
      ∀ r, min_depth root = ok r → ∀ d ∈ leafDepths root, r.val ≤ (d : ℤ)) := by
  sorry

/-- The function returns the result 0.
  Preconditions: root = Null. -/
theorem spec_5 (root : Tree) (hroot : root = Tree.Null) :
    ∃ r, min_depth root = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hroot : root = Tree.Null), ∃ r, min_depth root = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns the result 1.
  Preconditions: root = Node(v, Null, Null) for some i64 v with -1000 <= v <= 1000. -/
theorem spec_6 (v : Std.I64) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000) (root : Tree)
    (hroot : root = Tree.Node v Tree.Null Tree.Null) :
    ∃ r, min_depth root = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (v : Std.I64) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000) (root : Tree)
    (hroot : root = Tree.Node v Tree.Null Tree.Null), ∃ r, min_depth root = ok r ∧ r.val = 1) := by
  sorry

/-- Whenever min_depth(root) returns a result r, r = 1 if and only if root = Node(v, Null, Null) for some i64 value v.
  Preconditions: root is a finite Tree with at most 100000 Node constructors, every node value is in [-1000,1000], and root is non-null. -/
theorem spec_7 (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root)
    (hne : root ≠ Tree.Null) :
    ∀ r, min_depth root = ok r → (r.val = 1 ↔ ∃ v, root = Tree.Node v Tree.Null Tree.Null) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root)
    (hne : root ≠ Tree.Null), ∀ r, min_depth root = ok r → (r.val = 1 ↔ ∃ v, root = Tree.Node v Tree.Null Tree.Null)) := by
  sorry

/-- The function returns the result k.
  Preconditions: For some integer k with 1 <= k <= 100000, root is the right chain C_k, where C_0 = Null and C_{j+1} = Node(v_j, Null, C_j) for j = 0,...,k-1, and each v_j satisfies -1000 <= v_j <= 1000. -/
theorem spec_8 (root : Tree) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 100000) (vs : List Std.I64)
    (hlen : vs.length = k) (hvs : ∀ v ∈ vs, -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hroot : root = rightChain vs) :
    ∃ r, min_depth root = ok r ∧ r.val = (k : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 100000) (vs : List Std.I64)
    (hlen : vs.length = k) (hvs : ∀ v ∈ vs, -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hroot : root = rightChain vs), ∃ r, min_depth root = ok r ∧ r.val = (k : ℤ)) := by
  sorry

/-- Let D(t) be D(Null)=0 and, for non-null t, D(t) be the minimum number of nodes on a path from the root of t to a leaf of t. If l = Null and r is non-null, then whenever min_depth(root) returns a result q, q = 1 + D(r). Symmetrically, if r = Null and l is non-null, then q = 1 + D(l).
  Preconditions: root = Node(v, l, r) where -1000 <= v <= 1000, exactly one of l and r is Null, and the whole tree has at most 100000 nodes with all values in [-1000,1000]. -/
theorem spec_9 (v : Std.I64) (l r : Tree) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hexactly : (l = Tree.Null ∧ r ≠ Tree.Null) ∨ (r = Tree.Null ∧ l ≠ Tree.Null))
    (hcount : nodeCount (Tree.Node v l r) ≤ 100000)
    (hvals : valuesBounded (Tree.Node v l r)) :
    (l = Tree.Null → r ≠ Tree.Null →
        ∀ q, min_depth (Tree.Node v l r) = ok q → q.val = 1 + (D r : ℤ)) ∧
      (r = Tree.Null → l ≠ Tree.Null →
        ∀ q, min_depth (Tree.Node v l r) = ok q → q.val = 1 + (D l : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (v : Std.I64) (l r : Tree) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hexactly : (l = Tree.Null ∧ r ≠ Tree.Null) ∨ (r = Tree.Null ∧ l ≠ Tree.Null))
    (hcount : nodeCount (Tree.Node v l r) ≤ 100000)
    (hvals : valuesBounded (Tree.Node v l r)), (l = Tree.Null → r ≠ Tree.Null →
        ∀ q, min_depth (Tree.Node v l r) = ok q → q.val = 1 + (D r : ℤ)) ∧
      (r = Tree.Null → l ≠ Tree.Null →
        ∀ q, min_depth (Tree.Node v l r) = ok q → q.val = 1 + (D l : ℤ))) := by
  sorry

/-- Let D(t) be D(Null)=0 and, for non-null t, D(t) be the minimum number of nodes on a path from the root of t to a leaf of t. Whenever min_depth(root) returns a result q, q = 1 + min(D(l), D(r)).
  Preconditions: root = Node(v, l, r) with -1000 <= v <= 1000, both l and r non-null, at most 100000 nodes total, and all values in [-1000,1000]. -/
theorem spec_10 (v : Std.I64) (l r : Tree) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hl : l ≠ Tree.Null) (hr : r ≠ Tree.Null)
    (hcount : nodeCount (Tree.Node v l r) ≤ 100000)
    (hvals : valuesBounded (Tree.Node v l r)) :
    ∀ q, min_depth (Tree.Node v l r) = ok q → q.val = 1 + ((min (D l) (D r) : Nat) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (v : Std.I64) (l r : Tree) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hl : l ≠ Tree.Null) (hr : r ≠ Tree.Null)
    (hcount : nodeCount (Tree.Node v l r) ≤ 100000)
    (hvals : valuesBounded (Tree.Node v l r)), ∀ q, min_depth (Tree.Node v l r) = ok q → q.val = 1 + ((min (D l) (D r) : Nat) : ℤ)) := by
  sorry

/-- Let min_depth(root) return r and min_depth(root2) return r2. Then r = r2.
  Preconditions: root and root2 are finite trees with identical shape: there is a bijection between their node occurrences that preserves the root, left-child, right-child, and Null positions. Both satisfy the node-count and value constraints. -/
theorem spec_11 (root root2 : Tree) (hshape : shapeOf root = shapeOf root2)
    (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root)
    (hcount2 : nodeCount root2 ≤ 100000) (hvals2 : valuesBounded root2) :
    ∀ r r2, min_depth root = ok r → min_depth root2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root root2 : Tree) (hshape : shapeOf root = shapeOf root2)
    (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root)
    (hcount2 : nodeCount root2 ≤ 100000) (hvals2 : valuesBounded root2), ∀ r r2, min_depth root = ok r → min_depth root2 = ok r2 → r.val = r2.val) := by
  sorry

/-- Define mirror(Null)=Null and mirror(Node(v,l,r)) = Node(v, mirror(r), mirror(l)). Then min_depth(root) returns r and min_depth(mirror(root)) returns r2 with r = r2.
  Preconditions: root is a finite Tree satisfying the node-count and value constraints: at most 100000 Node constructors and all node values in [-1000,1000]. -/
theorem spec_12 (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root) :
    ∀ r r2, min_depth root = ok r → min_depth (mirror root) = ok r2 → r.val = r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root), ∀ r r2, min_depth root = ok r → min_depth (mirror root) = ok r2 → r.val = r2.val) := by
  sorry

/-- Whenever min_depth(Node(v,l,r)) returns a result q1 and min_depth(Node(v,r,l)) returns a result q2, q1 = q2.
  Preconditions: v is an i64 with -1000 <= v <= 1000, and l and r are finite subtrees such that Node(v,l,r) has at most 100000 nodes and all values in [-1000,1000]. -/
theorem spec_13 (v : Std.I64) (l r : Tree) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hcount : nodeCount (Tree.Node v l r) ≤ 100000)
    (hvals : valuesBounded (Tree.Node v l r)) :
    ∀ q1 q2, min_depth (Tree.Node v l r) = ok q1 → min_depth (Tree.Node v r l) = ok q2 →
      q1.val = q2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (v : Std.I64) (l r : Tree) (hv : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (hcount : nodeCount (Tree.Node v l r) ≤ 100000)
    (hvals : valuesBounded (Tree.Node v l r)), ∀ q1 q2, min_depth (Tree.Node v l r) = ok q1 → min_depth (Tree.Node v r l) = ok q2 →
      q1.val = q2.val) := by
  sorry

/-- Whenever min_depth(root) returns a result r, r = 0 if and only if root = Null.
  Preconditions: root is a finite Tree with at most 100000 Node constructors, and every node value v satisfies -1000 <= v <= 1000. -/
theorem spec_14 (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root) :
    ∀ r, min_depth root = ok r → (r.val = 0 ↔ root = Tree.Null) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000) (hvals : valuesBounded root), ∀ r, min_depth root = ok r → (r.val = 0 ↔ root = Tree.Null)) := by
  sorry

/-- The function returns a result for every such root; it does not fail, panic, or overflow.
  Preconditions: root is any finite Tree with at most 100000 Node constructors; node values are arbitrary i64 values. -/
theorem spec_15 (root : Tree) (hcount : nodeCount root ≤ 100000) :
    ∃ r, min_depth root = ok r := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (root : Tree) (hcount : nodeCount root ≤ 100000), ∃ r, min_depth root = ok r) := by
  sorry

end AegisSpec.MinDepth
