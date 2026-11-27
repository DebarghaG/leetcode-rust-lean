import Aegis.DiameterOfBinaryTree.Code.Funs

/-!
# Specifications of `Aegis.DiameterOfBinaryTree.diameter_of_binary_tree`

LeetCode problem `diameter-of-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DiameterOfBinaryTree

  open Aegis.DiameterOfBinaryTree

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def ValuesSmall : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => -100 ≤ v.val ∧ v.val ≤ 100 ∧ ValuesSmall l ∧ ValuesSmall r

  def treeHeight : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ Tree.Null Tree.Null => 0
    | Tree.Node _ l r => max (treeHeight l) (treeHeight r) + 1

  inductive Shape where

    | null : Shape

    | node : Shape → Shape → Shape
    deriving DecidableEq

  def treeShape : Tree → Shape
    | Tree.Null => Shape.null
    | Tree.Node _ l r => Shape.node (treeShape l) (treeShape r)

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  def nodePositions : Tree → List (List Bool)
    | Tree.Null => []
    | Tree.Node _ l r =>
      [] :: ((nodePositions l).map (fun p => true :: p) ++ (nodePositions r).map (fun p => false :: p))

  def subtreeAt : Tree → List Bool → Tree
    | t, [] => t
    | Tree.Null, _ :: _ => Tree.Null
    | Tree.Node _ l _, true :: p => subtreeAt l p
    | Tree.Node _ _ r, false :: p => subtreeAt r p

  def commonPrefixLen : List Bool → List Bool → Nat
    | [], _ => 0
    | _, [] => 0
    | a :: p, b :: q => if a = b then commonPrefixLen p q + 1 else 0

  def dist (_t : Tree) (p q : List Bool) : Nat :=
    p.length + q.length - 2 * commonPrefixLen p q

  def diameter (t : Tree) : Nat :=
    ((nodePositions t).map
        (fun p => ((nodePositions t).map (fun q => dist t p q)).foldr max 0)).foldr max 0

  def atMostOneChildEach : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r => (l = Tree.Null ∨ r = Tree.Null) ∧ atMostOneChildEach l ∧ atMostOneChildEach r

  def pathLikeFromRoot : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r => atMostOneChildEach l ∧ atMostOneChildEach r

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, r is the diameter of root: r = max { dist(u,v) | u and v are nodes of root }, where dist(u,v) is the number of edges on the unique simple path between u and v in the tree (and dist(u,u)=0). Equivalently, r is the largest number of edges on any path whose endpoints are nodes of root. The maximum is over a nonempty finite set because root has at least one node.
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_1 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      r.val = ↑(diameter root) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), r.val = ↑(diameter root)) := by
    sorry

  /-- For every root satisfying the preconditions, diameter_of_binary_tree(root) returns Ok r for some 64-bit integer r; it does not return Err (no overflow, panic, or other failure).
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_2 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) :
      ∃ r : Std.I64, diameter_of_binary_tree root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root), ∃ r : Std.I64, diameter_of_binary_tree root = ok r) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, 0 ≤ r.
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_3 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), 0 ≤ r.val) := by
    sorry

  /-- Let n be the number of nodes in root. Whenever diameter_of_binary_tree(root) returns Ok r, r ≤ n - 1.
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_4 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      r.val ≤ ↑(nodeCount root) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), r.val ≤ ↑(nodeCount root) - 1) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, r = 0 if and only if root has exactly one node (equivalently, root = Node(v, Null, Null) for some value v).
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_5 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      r.val = 0 ↔ ∃ v : Std.I64, root = Tree.Node v Tree.Null Tree.Null := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), r.val = 0 ↔ ∃ v : Std.I64, root = Tree.Node v Tree.Null Tree.Null) := by
    sorry

  /-- Let n be the number of nodes in root. Whenever diameter_of_binary_tree(root) returns Ok r, r = n - 1 if and only if every node of root other than the top root node has at most one child (no non-root node has both a left child and a right child); equivalently, after forgetting orientation the tree is a simple path, including the case n = 1.
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_6 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      r.val = ↑(nodeCount root) - 1 ↔ pathLikeFromRoot root := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), r.val = ↑(nodeCount root) - 1 ↔ pathLikeFromRoot root) := by
    sorry

  /-- If diameter_of_binary_tree(root) returns Ok r and diameter_of_binary_tree(root2) returns Ok r2, then r = r2.
    Preconditions: root and root2 are non-null binary trees, each with at most 10000 nodes and all node values in [-100, 100], and root and root2 have the same shape ignoring values. This shape equality is defined recursively: shape(Null) = Null; shape(Node(_, L, R)) = Node(shape(L), shape(R)). -/
  theorem spec_7 (root root2 : Tree) (hne : root ≠ Tree.Null) (hne2 : root2 ≠ Tree.Null)
      (hsize : nodeCount root ≤ 10000) (hsize2 : nodeCount root2 ≤ 10000)
      (hval : ValuesSmall root) (hval2 : ValuesSmall root2)
      (hshape : treeShape root = treeShape root2)
      (r r2 : Std.I64) (hr : diameter_of_binary_tree root = ok r)
      (hr2 : diameter_of_binary_tree root2 = ok r2) :
      r = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root root2 : Tree) (hne : root ≠ Tree.Null) (hne2 : root2 ≠ Tree.Null)
        (hsize : nodeCount root ≤ 10000) (hsize2 : nodeCount root2 ≤ 10000)
        (hval : ValuesSmall root) (hval2 : ValuesSmall root2)
        (hshape : treeShape root = treeShape root2)
        (r r2 : Std.I64) (hr : diameter_of_binary_tree root = ok r)
        (hr2 : diameter_of_binary_tree root2 = ok r2), r = r2) := by
    sorry

  /-- If diameter_of_binary_tree(root) returns Ok r and diameter_of_binary_tree(mirror(root)) returns Ok r2, then r = r2.
    Preconditions: root is a non-null binary tree with at most 10000 nodes and all node values in [-100, 100]. The mirror of root is defined recursively by mirror(Null) = Null and mirror(Node(v, L, R)) = Node(v, mirror(R), mirror(L)). -/
  theorem spec_8 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r r2 : Std.I64) (hr : diameter_of_binary_tree root = ok r)
      (hr2 : diameter_of_binary_tree (mirror root) = ok r2) :
      r = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r r2 : Std.I64) (hr : diameter_of_binary_tree root = ok r)
        (hr2 : diameter_of_binary_tree (mirror root) = ok r2), r = r2) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, r ≥ height(root), where height(T) for a non-null tree T is the maximum number of edges on a path from the root of T to any node of T; thus a leaf has height 0.
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_9 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      ↑(treeHeight root) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), ↑(treeHeight root) ≤ r.val) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, r ≤ 2 * height(root), where height(root) is the maximum number of edges from the root of root to any node of root (a leaf has height 0).
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_10 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      r.val ≤ 2 * ↑(treeHeight root) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), r.val ≤ 2 * ↑(treeHeight root)) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, r ≥ height(L) + height(R) + 2, where height(T) for a non-null tree T is the maximum number of edges from the root of T to any node of T (a leaf has height 0).
    Preconditions: root is a non-null binary tree with at most 10000 nodes, every node value is in [-100, 100], and root = Node(v, L, R) with L ≠ Null and R ≠ Null (so the root has both a left and a right child). -/
  theorem spec_11 (root : Tree) (v : Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R)
      (hL : L ≠ Tree.Null) (hR : R ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      ↑(treeHeight L) + ↑(treeHeight R) + 2 ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R)
        (hL : L ≠ Tree.Null) (hR : R ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), ↑(treeHeight L) + ↑(treeHeight R) + 2 ≤ r.val) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, for every node x of root, r ≥ d_x, where T_x is the subtree of root consisting of x together with all descendants of x, and d_x is the diameter of T_x, i.e., the maximum of dist_Tx(u,v) over all nodes u and v of T_x (with d_x = 0 if T_x has only the node x).
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_12 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      ∀ p ∈ nodePositions root, ↑(diameter (subtreeAt root p)) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), ∀ p ∈ nodePositions root, ↑(diameter (subtreeAt root p)) ≤ r.val) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, there exist nodes u and v of root such that dist(u,v) = r, where dist(u,v) is the number of edges on the unique simple path between u and v in root, and dist(u,u) = 0.
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_13 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      ∃ p ∈ nodePositions root, ∃ q ∈ nodePositions root, ↑(dist root p q) = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), ∃ p ∈ nodePositions root, ∃ q ∈ nodePositions root, ↑(dist root p q) = r.val) := by
    sorry

  /-- Whenever diameter_of_binary_tree(root) returns Ok r, for every pair of nodes u and v of root, dist(u,v) ≤ r, where dist(u,v) is the number of edges on the unique simple path between u and v in root (and dist(u,u) = 0).
    Preconditions: root is a non-null binary tree (root ≠ Null) with at most 10000 nodes, and every node value is in [-100, 100]. -/
  theorem spec_14 (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
      (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r) :
      ∀ p ∈ nodePositions root, ∀ q ∈ nodePositions root, ↑(dist root p q) ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : nodeCount root ≤ 10000)
        (hval : ValuesSmall root) (r : Std.I64) (hr : diameter_of_binary_tree root = ok r), ∀ p ∈ nodePositions root, ∀ q ∈ nodePositions root, ↑(dist root p q) ≤ r.val) := by
    sorry

  end AegisSpec.DiameterOfBinaryTree
