import Aegis.ReplaceValueInTree.Code.Funs

/-!
# Specifications of `Aegis.ReplaceValueInTree.replace_value_in_tree`

LeetCode problem `cousins-in-binary-tree-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ReplaceValueInTree

  inductive Dir where
    | L : Dir
    | R : Dir
    deriving DecidableEq, Repr

  abbrev Path := List Dir

  open Aegis.ReplaceValueInTree

  def subtree : Tree → Path → Tree
    | t, [] => t
    | Tree.Null, _ :: _ => Tree.Null
    | Tree.Node _ l _, Dir.L :: rest => subtree l rest
    | Tree.Node _ _ r, Dir.R :: rest => subtree r rest

  def valueAt (t : Tree) (p : Path) : Option Std.I64 :=
    match subtree t p with
    | Tree.Null => none
    | Tree.Node v _ _ => some v

  def HasNode (t : Tree) (p : Path) : Prop := (valueAt t p).isSome

  instance (t : Tree) (p : Path) : Decidable (HasNode t p) := by
    unfold HasNode; infer_instance

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def totalSum : Tree → Int
    | Tree.Null => 0
    | Tree.Node v l r => totalSum l + totalSum r + v.val

  def allPaths : Tree → List Path
    | Tree.Null => []
    | Tree.Node _ l r =>
      [] :: ((allPaths l).map (fun p => Dir.L :: p) ++ (allPaths r).map (fun p => Dir.R :: p))

  def cousin (p q : Path) : Prop :=
    p.length = q.length ∧ p ≠ q ∧ p.dropLast ≠ q.dropLast

  instance (p q : Path) : Decidable (cousin p q) := by
    unfold cousin; infer_instance

  def cousinValues (t : Tree) (p : Path) : List Int :=
    ((allPaths t).filter (fun q => decide (cousin p q))).filterMap
      (fun q => (valueAt t q).map (fun v => v.val))

  def cousinSum (t : Tree) (p : Path) : Int :=
    (cousinValues t p).foldl (fun a b => a + b) 0

  def hasCousin (t : Tree) (p : Path) : Prop :=
    ∃ q, HasNode t q ∧ cousin p q

  def valuesInBounds (t : Tree) : Prop :=
    ∀ p v, valueAt t p = some v → 1 ≤ v.val ∧ v.val ≤ 10000

  def ValidInput (t : Tree) : Prop :=
    1 ≤ nodeCount t ∧ nodeCount t ≤ 100000 ∧ valuesInBounds t

  def SameShape (s t : Tree) : Prop :=
    ∀ p, HasNode s p ↔ HasNode t p

  /-- Let a node occurrence be identified by the finite sequence p of L/R moves from the root; let depth(p) be the number of moves in p, and for nonempty p let parent(p) be p with its last move removed. Two existing node occurrences at paths p and q are cousins iff depth(p) = depth(q), p != q, and parent(p) != parent(q) (the root has no parent and therefore no cousins). For each path p at which root has a Node, let C(p) be the sum of the original values of all node occurrences q in root that are cousins of p, with C(p) = 0 if there are none. The function returns a result r such that for every finite L/R path p, r has a Node at p if and only if root has a Node at p; and whenever root has a Node at p, the value stored at that node in r is C(p).
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_1 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧
        (∀ p : Path, HasNode r p ↔ HasNode root p) ∧
        (∀ (p : Path) (v w : Std.I64), valueAt root p = some v → valueAt r p = some w →
          w.val = cousinSum root p) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧
          (∀ p : Path, HasNode r p ↔ HasNode root p) ∧
          (∀ (p : Path) (v w : Std.I64), valueAt root p = some v → valueAt r p = some w →
            w.val = cousinSum root p)) := by
    sorry

  /-- The function returns a result r, and r has exactly the same tree shape as root: for every finite L/R path p, r has a Node at p if and only if root has a Node at p. Equivalently, Null and Node positions in r are identical to those in root.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_2 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧ SameShape r root := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧ SameShape r root) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail (no arithmetic overflow, no out-of-bounds access, and no panic).
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_3 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r) := by
    sorry

  /-- The function returns a result r, and the value stored at the root of r (the node at the empty path) is 0.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_4 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧ ∃ w : Std.I64, valueAt r [] = some w ∧ w.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧ ∃ w : Std.I64, valueAt r [] = some w ∧ w.val = 0) := by
    sorry

  /-- The function returns a result r, and every node of r at depth 1 (every existing left or right child of the root) has value 0.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_5 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧
        ∀ (d : Dir) (w : Std.I64), valueAt r [d] = some w → w.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧
          ∀ (d : Dir) (w : Std.I64), valueAt r [d] = some w → w.val = 0) := by
    sorry

  /-- The function returns a result r, and every node value in r is 0.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, every Node value v satisfies 1 <= v <= 10000, and root has no node at depth 2 (equivalently, every child of the root is either Null or a leaf). -/
  theorem spec_6 (root : Tree) (hroot : ValidInput root)
      (hno_depth_two : ∀ p : Path, p.length = 2 → valueAt root p = none) :
      ∃ r, replace_value_in_tree root = ok r ∧
        ∀ (p : Path) (w : Std.I64), valueAt r p = some w → w.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root)
        (hno_depth_two : ∀ p : Path, p.length = 2 → valueAt root p = none), ∃ r, replace_value_in_tree root = ok r ∧
          ∀ (p : Path) (w : Std.I64), valueAt r p = some w → w.val = 0) := by
    sorry

  /-- The function returns a result r, and every node value in r is at least 0.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_7 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧
        ∀ (p : Path) (w : Std.I64), valueAt r p = some w → 0 ≤ w.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧
          ∀ (p : Path) (w : Std.I64), valueAt r p = some w → 0 ≤ w.val) := by
    sorry

  /-- The function returns a result r, and every node value in r is at most the sum of the original values of all Node occurrences in root.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_8 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧
        ∀ (p : Path) (w : Std.I64), valueAt r p = some w → w.val ≤ totalSum root := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧
          ∀ (p : Path) (w : Std.I64), valueAt r p = some w → w.val ≤ totalSum root) := by
    sorry

  /-- The function returns a result r. For every path p such that root has both a left child and a right child at p (that is, root has Nodes at pL and pR), r has Nodes at pL and pR and their values are equal.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_9 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧
        ∀ (p : Path) (vL vR : Std.I64),
          valueAt root (p ++ [Dir.L]) = some vL → valueAt root (p ++ [Dir.R]) = some vR →
          ∃ wL wR : Std.I64,
            valueAt r (p ++ [Dir.L]) = some wL ∧ valueAt r (p ++ [Dir.R]) = some wR ∧
              wL.val = wR.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧
          ∀ (p : Path) (vL vR : Std.I64),
            valueAt root (p ++ [Dir.L]) = some vL → valueAt root (p ++ [Dir.R]) = some vR →
            ∃ wL wR : Std.I64,
              valueAt r (p ++ [Dir.L]) = some wL ∧ valueAt r (p ++ [Dir.R]) = some wR ∧
                wL.val = wR.val) := by
    sorry

  /-- If replace_value_in_tree(root) returns r and replace_value_in_tree(root') returns r', then for every path p of depth d at which root has a Node, r and r' have Nodes at p and the values at p in r and r' are equal.
    Preconditions: root and root' are finite binary trees with between 1 and 100000 Node occurrences, every Node value in each is between 1 and 10000, they have the same shape (for every L/R path p, root has a Node at p iff root' has a Node at p), and for some depth d >= 0, for every path p of depth d at which root has a Node, the original value at p in root equals the original value at p in root'. -/
  theorem spec_10 (root root' : Tree) (d : Nat)
      (hroot : ValidInput root) (hroot' : ValidInput root')
      (hshape : SameShape root root')
      (hagree : ∀ (p : Path) (v : Std.I64), p.length = d → valueAt root p = some v →
        ∃ v' : Std.I64, valueAt root' p = some v' ∧ v.val = v'.val)
      (r r' : Tree) (hr : replace_value_in_tree root = ok r)
      (hr' : replace_value_in_tree root' = ok r') :
      ∀ (p : Path) (v : Std.I64), p.length = d → valueAt root p = some v →
        ∃ w w' : Std.I64, valueAt r p = some w ∧ valueAt r' p = some w' ∧ w.val = w'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root root' : Tree) (d : Nat)
        (hroot : ValidInput root) (hroot' : ValidInput root')
        (hshape : SameShape root root')
        (hagree : ∀ (p : Path) (v : Std.I64), p.length = d → valueAt root p = some v →
          ∃ v' : Std.I64, valueAt root' p = some v' ∧ v.val = v'.val)
        (r r' : Tree) (hr : replace_value_in_tree root = ok r)
        (hr' : replace_value_in_tree root' = ok r'), ∀ (p : Path) (v : Std.I64), p.length = d → valueAt root p = some v →
          ∃ w w' : Std.I64, valueAt r p = some w ∧ valueAt r' p = some w' ∧ w.val = w'.val) := by
    sorry

  /-- The function returns a result r. For every path p at which root has a Node, the value at p in r is 0 if and only if p has no cousin in root, that is, if and only if there is no path q such that root has a Node at q, depth(q) = depth(p), and parent(q) != parent(p), with the root defined to have no cousins.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_11 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧
        ∀ (p : Path) (v w : Std.I64), valueAt root p = some v → valueAt r p = some w →
          (w.val = 0 ↔ ¬ hasCousin root p) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧
          ∀ (p : Path) (v w : Std.I64), valueAt root p = some v → valueAt r p = some w →
            (w.val = 0 ↔ ¬ hasCousin root p)) := by
    sorry

  /-- The function returns r = Node(0, Null, Null).
    Preconditions: root = Node(v, Null, Null) for some integer v with 1 <= v <= 10000. -/
  theorem spec_12 (v : Std.I64) (hv_lower : 1 ≤ v.val) (hv_upper : v.val ≤ 10000) :
      replace_value_in_tree (Tree.Node v Tree.Null Tree.Null) =
        ok (Tree.Node 0#i64 Tree.Null Tree.Null) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (v : Std.I64) (hv_lower : 1 ≤ v.val) (hv_upper : v.val ≤ 10000), replace_value_in_tree (Tree.Node v Tree.Null Tree.Null) =
          ok (Tree.Node 0#i64 Tree.Null Tree.Null)) := by
    sorry

  /-- For root = Node(1, Node(2, Node(4, Null, Null), Node(5, Null, Null)), Node(3, Node(6, Null, Null), Node(7, Null, Null))), the function returns r = Node(0, Node(0, Node(13, Null, Null), Node(13, Null, Null)), Node(0, Node(9, Null, Null), Node(9, Null, Null))).
    Preconditions: This is a concrete input satisfying the problem constraints. -/
  theorem spec_13 :
      replace_value_in_tree
          (Tree.Node 1#i64
            (Tree.Node 2#i64 (Tree.Node 4#i64 Tree.Null Tree.Null)
              (Tree.Node 5#i64 Tree.Null Tree.Null))
            (Tree.Node 3#i64 (Tree.Node 6#i64 Tree.Null Tree.Null)
              (Tree.Node 7#i64 Tree.Null Tree.Null))) =
        ok
          (Tree.Node 0#i64
            (Tree.Node 0#i64 (Tree.Node 13#i64 Tree.Null Tree.Null)
              (Tree.Node 13#i64 Tree.Null Tree.Null))
            (Tree.Node 0#i64 (Tree.Node 9#i64 Tree.Null Tree.Null)
              (Tree.Node 9#i64 Tree.Null Tree.Null))) := by
    sorry

  theorem spec_13_neg :
      ¬ (replace_value_in_tree
            (Tree.Node 1#i64
              (Tree.Node 2#i64 (Tree.Node 4#i64 Tree.Null Tree.Null)
                (Tree.Node 5#i64 Tree.Null Tree.Null))
              (Tree.Node 3#i64 (Tree.Node 6#i64 Tree.Null Tree.Null)
                (Tree.Node 7#i64 Tree.Null Tree.Null))) =
          ok
            (Tree.Node 0#i64
              (Tree.Node 0#i64 (Tree.Node 13#i64 Tree.Null Tree.Null)
                (Tree.Node 13#i64 Tree.Null Tree.Null))
              (Tree.Node 0#i64 (Tree.Node 9#i64 Tree.Null Tree.Null)
                (Tree.Node 9#i64 Tree.Null Tree.Null)))) := by
    sorry

  /-- The function returns a result r. For any two paths p and q at which root has Nodes, if p and q are cousins (depth(p) = depth(q), p != q, and parent(p) != parent(q)), then r has Nodes at p and q, the value at p in r is at least the original value at q in root, and the value at q in r is at least the original value at p in root.
    Preconditions: root is a finite binary tree with between 1 and 100000 Node occurrences, and every Node value v satisfies 1 <= v <= 10000. -/
  theorem spec_14 (root : Tree) (hroot : ValidInput root) :
      ∃ r, replace_value_in_tree root = ok r ∧
        ∀ (p q : Path) (vp vq : Std.I64),
          valueAt root p = some vp → valueAt root q = some vq → cousin p q →
          ∃ wp wq : Std.I64,
            valueAt r p = some wp ∧ valueAt r q = some wq ∧ vq.val ≤ wp.val ∧ vp.val ≤ wq.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree) (hroot : ValidInput root), ∃ r, replace_value_in_tree root = ok r ∧
          ∀ (p q : Path) (vp vq : Std.I64),
            valueAt root p = some vp → valueAt root q = some vq → cousin p q →
            ∃ wp wq : Std.I64,
              valueAt r p = some wp ∧ valueAt r q = some wq ∧ vq.val ≤ wp.val ∧ vp.val ≤ wq.val) := by
    sorry

  end AegisSpec.ReplaceValueInTree
