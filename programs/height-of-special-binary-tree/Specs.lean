import Aegis.HeightOfTree.Code.Funs

/-!
# Specifications of `Aegis.HeightOfTree.height_of_tree`

LeetCode problem `height-of-special-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HeightOfTree

open Aegis.HeightOfTree

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

def labels : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (labels l ++ labels r)

def LabelsInRange (t : Tree) (n : Nat) : Prop :=
  (labels t).Nodup ∧ ∀ x ∈ labels t, 1 ≤ x ∧ x ≤ (n : Int)

def H : Tree → Int
  | Tree.Null => -1
  | Tree.Node _ l r => 1 + max (H l) (H r)

inductive NodeAt : Tree → Nat → Prop where
  | root {v : I64} {l r : Tree} : NodeAt (Tree.Node v l r) 0
  | left {v : I64} {l r : Tree} {d : Nat} : NodeAt l d → NodeAt (Tree.Node v l r) (d + 1)
  | right {v : I64} {l r : Tree} {d : Nat} : NodeAt r d → NodeAt (Tree.Node v l r) (d + 1)

inductive LeafAt : Tree → Nat → Prop where
  | here (v : I64) : LeafAt (Tree.Node v Tree.Null Tree.Null) 0
  | left {v : I64} {l r : Tree} {d : Nat} : LeafAt l d → LeafAt (Tree.Node v l r) (d + 1)
  | right {v : I64} {l r : Tree} {d : Nat} : LeafAt r d → LeafAt (Tree.Node v l r) (d + 1)

inductive SameShape : Tree → Tree → Prop where
  | null : SameShape Tree.Null Tree.Null
  | node {v v' : I64} {l l' r r' : Tree} :
      SameShape l l' → SameShape r r' → SameShape (Tree.Node v l r) (Tree.Node v' l' r')

/-- Let H be the height function on Tree defined by H(Null) = -1 and H(Node(v,l,r)) = 1 + max(H(l), H(r)). Then height_of_tree(root) returns a result r and r = H(root). Equivalently, r is the number of edges on a longest path from the root to any node of root.
  Preconditions: root is a finite Tree, root is not Null, N(root)=n where N(t) is the number of Node constructors in t, 2 <= n <= 10000, and the node labels are pairwise distinct integers in 1..n. -/
theorem spec_1 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hN : nodeCount root = n)
    (hlo : 2 ≤ n) (hhi : n ≤ 10000)
    (hlabels : LabelsInRange root n) :
    ∃ r : I64, height_of_tree root = Result.ok r ∧ r.val = H root := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hN : nodeCount root = n)
    (hlo : 2 ≤ n) (hhi : n ≤ 10000)
    (hlabels : LabelsInRange root n), ∃ r : I64, height_of_tree root = Result.ok r ∧ r.val = H root) := by
  sorry

/-- For every input root satisfying the preconditions, the call height_of_tree(root) returns a result; it does not fail with a panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, where N(t) is the number of Node constructors, and the node labels are pairwise distinct integers in 1..N(root). -/
theorem spec_2 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root)) :
    ∃ r : I64, height_of_tree root = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root)), ∃ r : I64, height_of_tree root = Result.ok r) := by
  sorry

/-- Whenever height_of_tree(root) returns a result r, we have r >= 1.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, where N(t) is the number of Node constructors, and the node labels are pairwise distinct integers in 1..N(root). -/
theorem spec_3 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever height_of_tree(root) returns a result r, we have r <= N(root) - 1, where N(t) is the number of Node constructors in t.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, where N(t) is the number of Node constructors, and the node labels are pairwise distinct integers in 1..N(root). -/
theorem spec_4 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r) :
    r.val ≤ (nodeCount root : Int) - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r), r.val ≤ (nodeCount root : Int) - 1) := by
  sorry

/-- For a node occurrence u of root, let depth(root,u) be the number of edges on the unique path from the root of root to u, with the root itself having depth 0. Whenever height_of_tree(root) returns a result r, there exists a node occurrence u of root such that depth(root,u) = r.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, where N(t) is the number of Node constructors, and the node labels are pairwise distinct integers in 1..N(root). -/
theorem spec_5 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r) :
    ∃ d : Nat, NodeAt root d ∧ (d : Int) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r), ∃ d : Nat, NodeAt root d ∧ (d : Int) = r.val) := by
  sorry

/-- For a node occurrence u of root, let depth(root,u) be the number of edges on the unique path from the root of root to u, with the root itself having depth 0. Whenever height_of_tree(root) returns a result r, for every node occurrence u of root we have depth(root,u) <= r.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, where N(t) is the number of Node constructors, and the node labels are pairwise distinct integers in 1..N(root). -/
theorem spec_6 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r) :
    ∀ d : Nat, NodeAt root d → (d : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r), ∀ d : Nat, NodeAt root d → (d : Int) ≤ r.val) := by
  sorry

/-- A leaf of root is a node occurrence of the form Node(v, Null, Null), and depth(root,leaf) is its distance in edges from the root. Whenever height_of_tree(root) returns a result r, every leaf of root satisfies depth(root,leaf) <= r, and there exists a leaf of root with depth(root,leaf) = r.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, where N(t) is the number of Node constructors, and the node labels are pairwise distinct integers in 1..N(root). -/
theorem spec_7 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r) :
    (∀ d : Nat, LeafAt root d → (d : Int) ≤ r.val) ∧
      (∃ d : Nat, LeafAt root d ∧ (d : Int) = r.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (r : I64) (hres : height_of_tree root = Result.ok r), (∀ d : Nat, LeafAt root d → (d : Int) ≤ r.val) ∧
      (∃ d : Nat, LeafAt root d ∧ (d : Int) = r.val)) := by
  sorry

/-- If root and root2 have the same shape, meaning root2 is obtained from root by replacing the integer label at every node while recursively preserving all Null positions and left/right child relationships, then whenever height_of_tree(root) returns Ok r and height_of_tree(root2) returns Ok r2, we have r = r2.
  Preconditions: root and root2 are finite Trees each satisfying the problem constraints: each is non-Null, has between 2 and 10000 nodes, and has pairwise distinct labels in 1..its node count. -/
theorem spec_8 (root root2 : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hne2 : root2 ≠ Tree.Null)
    (hlo2 : 2 ≤ nodeCount root2) (hhi2 : nodeCount root2 ≤ 10000)
    (hlabels2 : LabelsInRange root2 (nodeCount root2))
    (hshape : SameShape root root2)
    (r r2 : I64)
    (hres : height_of_tree root = Result.ok r)
    (hres2 : height_of_tree root2 = Result.ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root root2 : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hne2 : root2 ≠ Tree.Null)
    (hlo2 : 2 ≤ nodeCount root2) (hhi2 : nodeCount root2 ≤ 10000)
    (hlabels2 : LabelsInRange root2 (nodeCount root2))
    (hshape : SameShape root root2)
    (r r2 : I64)
    (hres : height_of_tree root = Result.ok r)
    (hres2 : height_of_tree root2 = Result.ok r2), r.val = r2.val) := by
  sorry

/-- Whenever height_of_tree(root) returns Ok h and height_of_tree(Node(v,r,l)) returns Ok h2, we have h = h2.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, the node labels are pairwise distinct integers in 1..N(root), and root = Node(v,l,r) for some value v and subtrees l and r. -/
theorem spec_9 (root : Tree) (v : I64) (l r : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hroot : root = Tree.Node v l r)
    (h h2 : I64)
    (hres : height_of_tree root = Result.ok h)
    (hres2 : height_of_tree (Tree.Node v r l) = Result.ok h2) :
    h.val = h2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (v : I64) (l r : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hroot : root = Tree.Node v l r)
    (h h2 : I64)
    (hres : height_of_tree root = Result.ok h)
    (hres2 : height_of_tree (Tree.Node v r l) = Result.ok h2), h.val = h2.val) := by
  sorry

/-- Let H(Null) = -1 and H(Node(_,a,b)) = 1 + max(H(a), H(b)). Whenever height_of_tree(root) returns a result h, we have h = 1 + H(c), where c is the unique non-Null child of root.
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, the node labels are pairwise distinct integers in 1..N(root), and root = Node(v,l,r) where exactly one of l and r is not Null. -/
theorem spec_10 (root : Tree) (v : I64) (l r : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hroot : root = Tree.Node v l r)
    (hexactly : (l = Tree.Null ∧ r ≠ Tree.Null) ∨ (r = Tree.Null ∧ l ≠ Tree.Null))
    (h : I64) (hres : height_of_tree root = Result.ok h) :
    ∃ c : Tree, ((l = Tree.Null ∧ c = r) ∨ (r = Tree.Null ∧ c = l)) ∧ h.val = 1 + H c := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (v : I64) (l r : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hroot : root = Tree.Node v l r)
    (hexactly : (l = Tree.Null ∧ r ≠ Tree.Null) ∨ (r = Tree.Null ∧ l ≠ Tree.Null))
    (h : I64) (hres : height_of_tree root = Result.ok h), ∃ c : Tree, ((l = Tree.Null ∧ c = r) ∨ (r = Tree.Null ∧ c = l)) ∧ h.val = 1 + H c) := by
  sorry

/-- Let H(Null) = -1 and H(Node(_,a,b)) = 1 + max(H(a), H(b)). Whenever height_of_tree(root) returns a result h, we have h = 1 + max(H(l), H(r)).
  Preconditions: root is a finite non-Null Tree with 2 <= N(root) <= 10000, the node labels are pairwise distinct integers in 1..N(root), and root = Node(v,l,r) with l != Null and r != Null. -/
theorem spec_11 (root : Tree) (v : I64) (l r : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hroot : root = Tree.Node v l r)
    (hl : l ≠ Tree.Null) (hr : r ≠ Tree.Null)
    (h : I64) (hres : height_of_tree root = Result.ok h) :
    h.val = 1 + max (H l) (H r) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (v : I64) (l r : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 2 ≤ nodeCount root) (hhi : nodeCount root ≤ 10000)
    (hlabels : LabelsInRange root (nodeCount root))
    (hroot : root = Tree.Node v l r)
    (hl : l ≠ Tree.Null) (hr : r ≠ Tree.Null)
    (h : I64) (hres : height_of_tree root = Result.ok h), h.val = 1 + max (H l) (H r)) := by
  sorry

end AegisSpec.HeightOfTree
