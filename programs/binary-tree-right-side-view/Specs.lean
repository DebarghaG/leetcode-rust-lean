import Aegis.RightSideView.Code.Funs

/-!
# Specifications of `Aegis.RightSideView.right_side_view`

LeetCode problem `binary-tree-right-side-view`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RightSideView

  open Aegis.RightSideView

  def values : Tree → List Std.I64
    | Tree.Null => []
    | Tree.Node v l r => v :: (values l ++ values r)

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def AllValuesBounded (t : Tree) : Prop :=
    ∀ v : Std.I64, v ∈ values t → -100 ≤ v.val ∧ v.val ≤ 100

  def depths : Tree → Finset Nat
    | Tree.Null => ∅
    | Tree.Node _ l r => insert 0 ((depths l).image Nat.succ ∪ (depths r).image Nat.succ)

  def HasNodeAtDepth (t : Tree) (d : Nat) : Prop := d ∈ depths t

  def height : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (height l) (height r)

  def valueAtPath : Tree → List Bool → Option Std.I64
    | Tree.Null, _ => none
    | Tree.Node v _ _, [] => some v
    | Tree.Node _ l _, false :: p => valueAtPath l p
    | Tree.Node _ _ r, true :: p => valueAtPath r p

  def pathLt : List Bool → List Bool → Prop
    | [], [] => False
    | [], _ :: _ => True
    | _ :: _, [] => False
    | false :: xs, false :: ys => pathLt xs ys
    | false :: _, true :: _ => True
    | true :: _, false :: _ => False
    | true :: xs, true :: ys => pathLt xs ys

  def RightmostAt (t : Tree) (d : Nat) (v : Std.I64) : Prop :=
    ∃ p : List Bool, p.length = d ∧ valueAtPath t p = some v ∧
      ∀ q : List Bool, q.length = d → valueAtPath t q ≠ none → ¬ pathLt p q

  def UniqueNodeAt (t : Tree) (d : Nat) (v : Std.I64) : Prop :=
    ∃ p : List Bool, p.length = d ∧ valueAtPath t p = some v ∧
      ∀ q : List Bool, q.length = d → valueAtPath t q ≠ none → q = p

  def AtMostOneChild : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r => (l = Tree.Null ∨ r = Tree.Null) ∧ AtMostOneChild l ∧ AtMostOneChild r

  def Perfect : Tree → Nat → Prop
    | Tree.Null, _ => False
    | Tree.Node _ l r, 0 => l = Tree.Null ∧ r = Tree.Null
    | Tree.Node _ l r, n + 1 => Perfect l n ∧ Perfect r n

  def valueOnRightSpine : Tree → Nat → Option Std.I64
    | Tree.Null, _ => none
    | Tree.Node v _ _, 0 => some v
    | Tree.Node _ _ r, n + 1 => valueOnRightSpine r n

  /-- Let H be the set of depths d ≥ 0 for which root has at least one node at depth d (the root, when present, has depth 0; a child of a depth-d node has depth d+1). For nodes at the same depth, order them left-to-right by their root-to-node paths, where at the first differing step a left-child step is before a right-child step. Whenever right_side_view returns a result r, len(r) = |H|, and for every d with 0 ≤ d < len(r), r[d] is the value of the unique node at depth d that is rightmost at that depth, i.e. no node at depth d is to the right of it.
    Preconditions: root is a Tree with at most 100 Node constructors, and every node value v satisfies -100 ≤ v ≤ 100. -/
  theorem spec_1 (root : Tree)
      (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
        r.val.length = (depths root).card ∧
        ∀ (d : Nat) (hd : d < r.val.length), RightmostAt root d (r.val[d]'hd) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root), ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
          r.val.length = (depths root).card ∧
          ∀ (d : Nat) (hd : d < r.val.length), RightmostAt root d (r.val[d]'hd)) := by
    sorry

  /-- For every root satisfying the preconditions, right_side_view returns a result r and does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: root is a Tree with at most 100 Node constructors, and every node value v satisfies -100 ≤ v ≤ 100. -/
  theorem spec_2 (root : Tree)
      (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root) :
      ∃ r : alloc.vec.Vec Std.I64, right_side_view root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root), ∃ r : alloc.vec.Vec Std.I64, right_side_view root = ok r) := by
    sorry

  /-- Whenever right_side_view returns a result r, len(r) equals the number of nonnegative depths d at which root has at least one node. Equivalently, if root is Null then len(r) = 0, and if root is not Null then len(r) = 1 + max{d ≥ 0 | root has a node at depth d}, where depth 0 is the root.
    Preconditions: root is a Tree with at most 100 Node constructors, and every node value v satisfies -100 ≤ v ≤ 100. -/
  theorem spec_3 (root : Tree)
      (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
        r.val.length = (depths root).card ∧
        (root = Tree.Null → r.val.length = 0) ∧
        (root ≠ Tree.Null → r.val.length = height root) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root), ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
          r.val.length = (depths root).card ∧
          (root = Tree.Null → r.val.length = 0) ∧
          (root ≠ Tree.Null → r.val.length = height root)) := by
    sorry

  /-- Whenever right_side_view returns a result r, len(r) ≥ 1 and r[0] is the value stored at the root node of root.
    Preconditions: root is not Null, root has at most 100 nodes, and every node value in root satisfies -100 ≤ v ≤ 100. -/
  theorem spec_4 (v : Std.I64) (l rr : Tree)
      (hcount : nodeCount (Tree.Node v l rr) ≤ 100)
      (hbounded : AllValuesBounded (Tree.Node v l rr)) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view (Tree.Node v l rr) = ok r →
        1 ≤ r.val.length ∧
        ∀ (h0 : 0 < r.val.length), (r.val[0]'h0).val = v.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (v : Std.I64) (l rr : Tree)
        (hcount : nodeCount (Tree.Node v l rr) ≤ 100)
        (hbounded : AllValuesBounded (Tree.Node v l rr)), ∀ r : alloc.vec.Vec Std.I64, right_side_view (Tree.Node v l rr) = ok r →
          1 ≤ r.val.length ∧
          ∀ (h0 : 0 < r.val.length), (r.val[0]'h0).val = v.val) := by
    sorry

  /-- Whenever right_side_view returns a result r, for every i with 0 ≤ i < len(r), there exists a node n at depth i of root such that the value of n is r[i] and no node at depth i of root is strictly to the right of n. Nodes at the same depth are ordered left-to-right by their root-to-node paths: at the first step where two paths differ, a left-child step is to the left of a right-child step.
    Preconditions: root is a Tree with at most 100 Node constructors, and every node value v satisfies -100 ≤ v ≤ 100. -/
  theorem spec_5 (root : Tree)
      (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), RightmostAt root i (r.val[i]'hi) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root), ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
          ∀ (i : Nat) (hi : i < r.val.length), RightmostAt root i (r.val[i]'hi)) := by
    sorry

  /-- Whenever right_side_view returns a result r, for every i with 0 ≤ i < len(r), -100 ≤ r[i] ≤ 100.
    Preconditions: root is a Tree with at most 100 Node constructors, and every node value v satisfies -100 ≤ v ≤ 100. -/
  theorem spec_6 (root : Tree)
      (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          -100 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ 100 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root), ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
          ∀ (i : Nat) (hi : i < r.val.length),
            -100 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ 100) := by
    sorry

  /-- Whenever right_side_view returns a result r, len(r) is at most the number of Node constructors in root; in particular len(r) ≤ 100.
    Preconditions: root is a Tree with at most 100 Node constructors, and every node value v satisfies -100 ≤ v ≤ 100. -/
  theorem spec_7 (root : Tree)
      (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
        r.val.length ≤ nodeCount root ∧ r.val.length ≤ 100 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 100) (hbounded : AllValuesBounded root), ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
          r.val.length ≤ nodeCount root ∧ r.val.length ≤ 100) := by
    sorry

  /-- Whenever right_side_view returns a result r, len(r) ≥ 2, and r[1] = w, the value stored at the root of the right subtree of root.
    Preconditions: root = Node(v, L, Node(w, A, B)) for some value v, value w, and trees L, A, B; all node values are in [-100,100] and root has at most 100 nodes. -/
  theorem spec_8 (v w : Std.I64) (L A B : Tree)
      (hcount : nodeCount (Tree.Node v L (Tree.Node w A B)) ≤ 100)
      (hbounded : AllValuesBounded (Tree.Node v L (Tree.Node w A B))) :
      ∀ r : alloc.vec.Vec Std.I64,
        right_side_view (Tree.Node v L (Tree.Node w A B)) = ok r →
        2 ≤ r.val.length ∧
        ∀ (h1 : 1 < r.val.length), (r.val[1]'h1).val = w.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (v w : Std.I64) (L A B : Tree)
        (hcount : nodeCount (Tree.Node v L (Tree.Node w A B)) ≤ 100)
        (hbounded : AllValuesBounded (Tree.Node v L (Tree.Node w A B))), ∀ r : alloc.vec.Vec Std.I64,
          right_side_view (Tree.Node v L (Tree.Node w A B)) = ok r →
          2 ≤ r.val.length ∧
          ∀ (h1 : 1 < r.val.length), (r.val[1]'h1).val = w.val) := by
    sorry

  /-- Whenever right_side_view returns a result r, len(r) ≥ 2 and r[1] = w, the value stored at the root of the left subtree of root.
    Preconditions: root = Node(v, Node(w, A, B), Null) for some value v, value w, and trees A, B; all node values are in [-100,100] and root has at most 100 nodes. -/
  theorem spec_9 (v w : Std.I64) (A B : Tree)
      (hcount : nodeCount (Tree.Node v (Tree.Node w A B) Tree.Null) ≤ 100)
      (hbounded : AllValuesBounded (Tree.Node v (Tree.Node w A B) Tree.Null)) :
      ∀ r : alloc.vec.Vec Std.I64,
        right_side_view (Tree.Node v (Tree.Node w A B) Tree.Null) = ok r →
        2 ≤ r.val.length ∧
        ∀ (h1 : 1 < r.val.length), (r.val[1]'h1).val = w.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (v w : Std.I64) (A B : Tree)
        (hcount : nodeCount (Tree.Node v (Tree.Node w A B) Tree.Null) ≤ 100)
        (hbounded : AllValuesBounded (Tree.Node v (Tree.Node w A B) Tree.Null)), ∀ r : alloc.vec.Vec Std.I64,
          right_side_view (Tree.Node v (Tree.Node w A B) Tree.Null) = ok r →
          2 ≤ r.val.length ∧
          ∀ (h1 : 1 < r.val.length), (r.val[1]'h1).val = w.val) := by
    sorry

  /-- Whenever right_side_view returns a result r, len(r) equals the number of nodes in root, and for every i with 0 ≤ i < len(r), r[i] is the value of the unique node at depth i in root. Thus r lists the values along the unique root-to-leaf path from top to bottom, and r is empty when root is Null.
    Preconditions: Every node in root has at most one non-Null child (so root is either Null or a single downward path); every node value is in [-100,100]; root has at most 100 nodes. -/
  theorem spec_10 (root : Tree)
      (hpath : AtMostOneChild root)
      (hbounded : AllValuesBounded root) (hcount : nodeCount root ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
        r.val.length = nodeCount root ∧
        ∀ (i : Nat) (hi : i < r.val.length), UniqueNodeAt root i (r.val[i]'hi) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree)
        (hpath : AtMostOneChild root)
        (hbounded : AllValuesBounded root) (hcount : nodeCount root ≤ 100), ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
          r.val.length = nodeCount root ∧
          ∀ (i : Nat) (hi : i < r.val.length), UniqueNodeAt root i (r.val[i]'hi)) := by
    sorry

  /-- Whenever right_side_view returns a result r, for every depth d ≥ 1 with d < len(r), consider depth d-1 measured from the root of a subtree. If R has at least one node at depth d-1, then r[d] is the value of the rightmost node at depth d-1 in R, using the same left-to-right path order inside R; otherwise L has at least one node at depth d-1 and r[d] is the value of the rightmost node at depth d-1 in L.
    Preconditions: root = Node(v, L, R) for some value v and trees L, R; every node value is in [-100,100]; root has at most 100 nodes. -/
  theorem spec_11 (v : Std.I64) (L R : Tree)
      (hcount : nodeCount (Tree.Node v L R) ≤ 100)
      (hbounded : AllValuesBounded (Tree.Node v L R)) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view (Tree.Node v L R) = ok r →
        ∀ (d : Nat) (hd1 : 1 ≤ d) (hd : d < r.val.length),
          (HasNodeAtDepth R (d - 1) → RightmostAt R (d - 1) (r.val[d]'hd)) ∧
          (¬ HasNodeAtDepth R (d - 1) →
            HasNodeAtDepth L (d - 1) ∧ RightmostAt L (d - 1) (r.val[d]'hd)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (v : Std.I64) (L R : Tree)
        (hcount : nodeCount (Tree.Node v L R) ≤ 100)
        (hbounded : AllValuesBounded (Tree.Node v L R)), ∀ r : alloc.vec.Vec Std.I64, right_side_view (Tree.Node v L R) = ok r →
          ∀ (d : Nat) (hd1 : 1 ≤ d) (hd : d < r.val.length),
            (HasNodeAtDepth R (d - 1) → RightmostAt R (d - 1) (r.val[d]'hd)) ∧
            (¬ HasNodeAtDepth R (d - 1) →
              HasNodeAtDepth L (d - 1) ∧ RightmostAt L (d - 1) (r.val[d]'hd))) := by
    sorry

  /-- Let h be the height of the nonempty perfect tree root. Whenever right_side_view returns a result r, len(r) = h+1, and for every d with 0 ≤ d ≤ h, r[d] is the value of the node reached from the root by taking the right child exactly d times.
    Preconditions: root is a nonempty perfect binary tree of height h for some h ≥ 0: root is not Null, every node at depth < h has two non-Null children, every node at depth h is a leaf, and there are no nodes at depth > h. Every node value is in [-100,100], and root has at most 100 nodes. -/
  theorem spec_12 (root : Tree) (h : Nat)
      (hperfect : Perfect root h)
      (hbounded : AllValuesBounded root) (hcount : nodeCount root ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
        r.val.length = h + 1 ∧
        ∀ (d : Nat) (hd : d ≤ h), valueOnRightSpine root d = r.val[d]? := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (h : Nat)
        (hperfect : Perfect root h)
        (hbounded : AllValuesBounded root) (hcount : nodeCount root ≤ 100), ∀ r : alloc.vec.Vec Std.I64, right_side_view root = ok r →
          r.val.length = h + 1 ∧
          ∀ (d : Nat) (hd : d ≤ h), valueOnRightSpine root d = r.val[d]?) := by
    sorry

  end AegisSpec.RightSideView
