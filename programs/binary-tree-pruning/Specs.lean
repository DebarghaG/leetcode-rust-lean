import Aegis.PruneTree.Code.Funs

/-!
# Specifications of `Aegis.PruneTree.prune_tree`

LeetCode problem `binary-tree-pruning`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PruneTree

  open Aegis.PruneTree

  inductive Dir where
    | L : Dir
    | R : Dir
  deriving DecidableEq, Repr

  def nodeAt : Tree → List Dir → Option Tree
    | Tree.Null, _ => none
    | t, [] => some t
    | Tree.Node _ l _, Dir.L :: p => nodeAt l p
    | Tree.Node _ _ r, Dir.R :: p => nodeAt r p

  def hasNode (t : Tree) (p : List Dir) : Prop := (nodeAt t p).isSome

  def valAt (t : Tree) (p : List Dir) : Option Int :=
    match nodeAt t p with
    | some (Tree.Node v _ _) => some v.val
    | _ => none

  def Values01 : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => (v.val = 0 ∨ v.val = 1) ∧ Values01 l ∧ Values01 r

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def ContainsOne : Tree → Prop
    | Tree.Null => False
    | Tree.Node v l r => v.val = 1 ∨ ContainsOne l ∨ ContainsOne r

  instance instDecidableContainsOne : (t : Tree) → Decidable (ContainsOne t)
    | Tree.Null => isFalse (fun h => h)
    | Tree.Node v l r =>
      haveI : Decidable (ContainsOne l) := instDecidableContainsOne l
      haveI : Decidable (ContainsOne r) := instDecidableContainsOne r
      inferInstanceAs (Decidable (v.val = 1 ∨ ContainsOne l ∨ ContainsOne r))

  def SubtreeHasOne (t : Tree) (p : List Dir) : Prop :=
    ∃ s, nodeAt t p = some s ∧ ContainsOne s

  def keptCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node v l r =>
      (if ContainsOne (Tree.Node v l r) then 1 else 0) + keptCount l + keptCount r

  /-- Whenever prune_tree root returns Ok r, then for every finite path p (a sequence of L and R steps from the root, with the empty path denoting the root), r has a node at path p if and only if root has a node at path p and the subtree of root rooted at that node contains at least one node with value 1. Moreover, for every such path p, the value of the node of r at p equals the value of the node of root at p. (A tree has a node at path p only when all prefixes of p exist; the subtree rooted at a node is that node together with all its descendants.)
    Preconditions: root is a finite binary tree (Null or Node(v,l,r)) with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_1 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      (∀ p : List Dir, hasNode r p ↔ hasNode root p ∧ SubtreeHasOne root p)
        ∧ (∀ p : List Dir, hasNode r p → valAt r p = valAt root p) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), (∀ p : List Dir, hasNode r p ↔ hasNode root p ∧ SubtreeHasOne root p)
          ∧ (∀ p : List Dir, hasNode r p → valAt r p = valAt root p)) := by
    sorry

  /-- prune_tree root returns Ok r for some tree r; in particular it does not fail by panic, overflow, or out-of-bounds access.
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_2 (root : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200) :
      ∃ r : Tree, prune_tree root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200), ∃ r : Tree, prune_tree root = ok r) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, the tree r contains a node with value 1 if and only if root contains a node with value 1. (A tree contains a 1 when some node in it has value 1.)
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_3 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      ContainsOne r ↔ ContainsOne root := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), ContainsOne r ↔ ContainsOne root) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, for every node x of r, the subtree of r rooted at x contains at least one node with value 1. If r = Null this condition is vacuous. (The subtree rooted at x is x together with all descendants of x.)
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_4 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      ∀ p : List Dir, hasNode r p → SubtreeHasOne r p := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), ∀ p : List Dir, hasNode r p → SubtreeHasOne r p) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, for every finite path p (a sequence of L and R steps from the root, empty path = root), if root has a node at path p with value 1, then r has a node at path p with value 1.
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_5 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      ∀ p : List Dir, valAt root p = some (1 : Int) → valAt r p = some (1 : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), ∀ p : List Dir, valAt root p = some (1 : Int) → valAt r p = some (1 : Int)) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, for every finite path p, if r has a node at path p, then root has a node at path p and the value of the node of r at p equals the value of the node of root at p.
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_6 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      ∀ p : List Dir, hasNode r p → hasNode root p ∧ valAt r p = valAt root p := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), ∀ p : List Dir, hasNode r p → hasNode root p ∧ valAt r p = valAt root p) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, for every finite path p, if root has a node at path p and the subtree of root rooted at that node contains at least one node with value 1, then r has a node at path p with the same value.
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_7 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      ∀ p : List Dir, hasNode root p → SubtreeHasOne root p →
        hasNode r p ∧ valAt r p = valAt root p := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), ∀ p : List Dir, hasNode root p → SubtreeHasOne root p →
          hasNode r p ∧ valAt r p = valAt root p) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, for every finite path p, if root has a node at path p and the subtree of root rooted at that node contains no node with value 1, then r has no node at path p.
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_8 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      ∀ p : List Dir, hasNode root p → ¬ SubtreeHasOne root p → ¬ hasNode r p := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), ∀ p : List Dir, hasNode root p → ¬ SubtreeHasOne root p → ¬ hasNode r p) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, the number of nodes in r equals the number of nodes x of root such that the subtree of root rooted at x contains at least one node with value 1.
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_9 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      nodeCount r = keptCount root := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), nodeCount r = keptCount root) := by
    sorry

  /-- Whenever prune_tree root returns Ok r, for every node x of r, if x has value 0 then x has at least one non-null child in r. Equivalently, every leaf of r has value 1 (unless r = Null).
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_10 (root r : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) :
      ∀ (p : List Dir) (v : Aeneas.Std.I64) (l rr : Tree),
        nodeAt r p = some (Tree.Node v l rr) → v.val = 0 →
          l ≠ Tree.Null ∨ rr ≠ Tree.Null := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root r : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r), ∀ (p : List Dir) (v : Aeneas.Std.I64) (l rr : Tree),
          nodeAt r p = some (Tree.Node v l rr) → v.val = 0 →
            l ≠ Tree.Null ∨ rr ≠ Tree.Null) := by
    sorry

  /-- Whenever prune_tree root returns Ok r and prune_tree r returns Ok r', then r' = r.
    Preconditions: root is a finite binary tree with every node value equal to 0 or 1, and the number of nodes in root is between 1 and 200 inclusive. -/
  theorem spec_11 (root r r' : Tree)
      (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
      (hres : prune_tree root = ok r) (hres' : prune_tree r = ok r') :
      r' = r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root r r' : Tree)
        (h01 : Values01 root) (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 200)
        (hres : prune_tree root = ok r) (hres' : prune_tree r = ok r'), r' = r) := by
    sorry

  end AegisSpec.PruneTree
