import Aegis.IsCompleteTree.Code.Funs

/-!
# Specifications of `Aegis.IsCompleteTree.is_complete_tree`

LeetCode problem `check-completeness-of-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsCompleteTree

  open Aegis.IsCompleteTree

  def nodeCount : Tree → Nat
    | .Null => 0
    | .Node _ l r => nodeCount l + nodeCount r + 1

  def valuesBounded : Tree → Prop
    | .Null => True
    | .Node v l r =>
        1 ≤ v.val ∧ v.val ≤ 1000 ∧ valuesBounded l ∧ valuesBounded r

  def ValidTree (t : Tree) : Prop :=
    1 ≤ nodeCount t ∧ nodeCount t ≤ 100 ∧ valuesBounded t

  def heapIndicesAux : Tree → Nat → List Nat
    | .Null, _ => []
    | .Node _ l r, i =>
        i :: (heapIndicesAux l (2 * i) ++ heapIndicesAux r (2 * i + 1))

  def heapIndices (t : Tree) : List Nat :=
    heapIndicesAux t 1

  def nodesAtDepth : Tree → Nat → List Tree
    | .Null, _ => []
    | .Node v l r, 0 => [.Node v l r]
    | .Node _ l r, d + 1 => nodesAtDepth l d ++ nodesAtDepth r d

  def slotsAtDepth : Tree → Nat → List Tree
    | .Null, 0 => [.Null]
    | .Null, _ + 1 => []
    | .Node v l r, 0 => [.Node v l r]
    | .Node _ l r, d + 1 => slotsAtDepth l d ++ slotsAtDepth r d

  def levels : Tree → Nat
    | .Null => 0
    | .Node _ l r => max (levels l) (levels r) + 1

  def height (t : Tree) : Nat := levels t - 1

  def bfsSlots (t : Tree) : List Tree :=
    (List.range (levels t + 1)).flatMap (slotsAtDepth t)

  def NoNodeAfterNull : List Tree → Prop
    | [] => True
    | .Null :: rest => ∀ s ∈ rest, s = .Null
    | .Node _ _ _ :: rest => NoNodeAfterNull rest

  def occupiedPositions : Tree → Nat → List Nat
    | .Null, _ => []
    | .Node _ _ _, 0 => [0]
    | .Node _ l r, d + 1 =>
        (occupiedPositions l d).map (fun p => 2 * p) ++
          (occupiedPositions r d).map (fun p => 2 * p + 1)

  def ShapeComplete (t : Tree) : Prop :=
    ∃ h : Nat,
      (∀ d : Nat, h < d → nodesAtDepth t d = []) ∧
      (∀ d : Nat, d < h → ∀ p : Nat, p < 2 ^ d → p ∈ occupiedPositions t d) ∧
      ∃ m : Nat,
        1 ≤ m ∧ m ≤ 2 ^ h ∧
          ∀ p : Nat, p ∈ occupiedPositions t h ↔ p < m

  def SameShape : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node _ l r, .Node _ l' r' => SameShape l l' ∧ SameShape r r'
    | _, _ => False

  def HasLeftNullRightNode : Tree → Prop
    | .Null => False
    | .Node _ l r =>
        (l = .Null ∧ ∃ v l' r', r = .Node v l' r') ∨
          HasLeftNullRightNode l ∨ HasLeftNullRightNode r

  /-- The function returns a result r : Bool, and r = true if and only if root is a complete binary tree. Equivalently, assign heap indices by giving the root index 1, the left child of a node with index i index 2*i, and the right child index 2*i+1; let I(root) be the set of indices of all nodes. Then r = true iff I(root) = {1, 2, ..., n}.
    Preconditions: root is a finite Tree built from Null and Node(v, left, right). Let n be the number of Node constructors in root. The problem constraints hold: 1 <= n <= 100, and every node value v satisfies 1 <= v <= 1000. -/
  theorem spec_1 (root : Tree) (hroot : ValidTree root) :
      ∃ r : Bool,
        is_complete_tree root = Result.ok r ∧
          (r = true ↔
            ∀ i : Nat, i ∈ heapIndices root ↔ 1 ≤ i ∧ i ≤ nodeCount root) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root), ∃ r : Bool,
          is_complete_tree root = Result.ok r ∧
            (r = true ↔
              ∀ i : Nat, i ∈ heapIndices root ↔ 1 ≤ i ∧ i ≤ nodeCount root)) := by
    sorry

  /-- For every such root, is_complete_tree(root) returns a result (an Ok Bool); it does not panic, overflow, or otherwise fail.
    Preconditions: root is a finite Tree built from Null and Node(v, left, right). Let n be the number of Node constructors in root. The problem constraints hold: 1 <= n <= 100, and every node value v satisfies 1 <= v <= 1000. -/
  theorem spec_2 (root : Tree) (hroot : ValidTree root) :
      ∃ r : Bool, is_complete_tree root = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root), ∃ r : Bool, is_complete_tree root = Result.ok r) := by
    sorry

  /-- The function returns r : Bool, and r = true if and only if there exists an integer h >= 0 such that: (i) no node has depth greater than h; (ii) for every depth d with 0 <= d < h, all 2^d positions at depth d are occupied (positions at a depth are numbered left-to-right starting at 0); and (iii) at depth h the occupied positions are exactly 0, 1, ..., m-1 for some integer m with 1 <= m <= 2^h.
    Preconditions: root is a finite Tree built from Null and Node(v, left, right). Let n be the number of Node constructors in root. The problem constraints hold: 1 <= n <= 100, and every node value v satisfies 1 <= v <= 1000. -/
  theorem spec_3 (root : Tree) (hroot : ValidTree root) :
      ∃ r : Bool,
        is_complete_tree root = Result.ok r ∧
          (r = true ↔ ShapeComplete root) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root), ∃ r : Bool,
          is_complete_tree root = Result.ok r ∧
            (r = true ↔ ShapeComplete root)) := by
    sorry

  /-- The function returns r : Bool, and r = true if and only if the following holds in the breadth-first listing of node slots. Start with the root. Whenever a Node is listed, append its left child slot and right child slot at the end of the listing (each slot is either a Node or Null). Whenever a Null slot is listed, append nothing. Then no Node slot occurs after the first Null slot in this listing.
    Preconditions: root is a finite Tree built from Null and Node(v, left, right). Let n be the number of Node constructors in root. The problem constraints hold: 1 <= n <= 100, and every node value v satisfies 1 <= v <= 1000. -/
  theorem spec_4 (root : Tree) (hroot : ValidTree root) :
      ∃ r : Bool,
        is_complete_tree root = Result.ok r ∧
          (r = true ↔ NoNodeAfterNull (bfsSlots root)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root), ∃ r : Bool,
          is_complete_tree root = Result.ok r ∧
            (r = true ↔ NoNodeAfterNull (bfsSlots root))) := by
    sorry

  /-- The function returns r : Bool, and r = false.
    Preconditions: root is a finite Tree satisfying the problem constraints: it has n nodes with 1 <= n <= 100 and all node values in [1,1000]. Additionally, root contains at least one node x whose left child is Null and whose right child is a Node. -/
  theorem spec_5 (root : Tree) (hroot : ValidTree root)
      (hbad : HasLeftNullRightNode root) :
      ∃ r : Bool, is_complete_tree root = Result.ok r ∧ r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root)
        (hbad : HasLeftNullRightNode root), ∃ r : Bool, is_complete_tree root = Result.ok r ∧ r = false) := by
    sorry

  /-- Let r = is_complete_tree(root) and r2 = is_complete_tree(root2). Both calls return results, and r = r2.
    Preconditions: root and root2 are finite Trees that have the same shape and both satisfy the problem constraints: each has n nodes with 1 <= n <= 100 and all node values in [1,1000]. Here same shape means root2 is obtained from root by replacing each node value by some value in [1,1000] while keeping the Null/Node structure and the left/right child positions unchanged. -/
  theorem spec_6 (root root2 : Tree) (hroot : ValidTree root)
      (hroot2 : ValidTree root2) (hsame : SameShape root root2) :
      ∃ r r2 : Bool,
        is_complete_tree root = Result.ok r ∧
          is_complete_tree root2 = Result.ok r2 ∧ r = r2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root root2 : Tree) (hroot : ValidTree root)
        (hroot2 : ValidTree root2) (hsame : SameShape root root2), ∃ r r2 : Bool,
          is_complete_tree root = Result.ok r ∧
            is_complete_tree root2 = Result.ok r2 ∧ r = r2) := by
    sorry

  /-- Whenever is_complete_tree(root) returns r = true, every node of root has a heap index i (root index 1, left child of index i has index 2*i, right child has index 2*i+1) satisfying 1 <= i <= n. Equivalently, no node has heap index greater than n.
    Preconditions: root is a finite Tree built from Null and Node(v, left, right). Let n be the number of Node constructors in root. The problem constraints hold: 1 <= n <= 100, and every node value v satisfies 1 <= v <= 1000. -/
  theorem spec_7 (root : Tree) (hroot : ValidTree root) :
      is_complete_tree root = Result.ok true →
        ∀ i : Nat, i ∈ heapIndices root → 1 ≤ i ∧ i ≤ nodeCount root := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root), is_complete_tree root = Result.ok true →
          ∀ i : Nat, i ∈ heapIndices root → 1 ≤ i ∧ i ≤ nodeCount root) := by
    sorry

  /-- Whenever is_complete_tree(root) returns r = false, there exist heap indices j and k (defined by root index 1, left child 2*i, right child 2*i+1) such that 1 <= j < k, j is not the index of any node of root, and k is the index of some node of root.
    Preconditions: root is a finite Tree built from Null and Node(v, left, right). Let n be the number of Node constructors in root. The problem constraints hold: 1 <= n <= 100, and every node value v satisfies 1 <= v <= 1000. -/
  theorem spec_8 (root : Tree) (hroot : ValidTree root) :
      is_complete_tree root = Result.ok false →
        ∃ j k : Nat,
          1 ≤ j ∧ j < k ∧ j ∉ heapIndices root ∧ k ∈ heapIndices root := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root), is_complete_tree root = Result.ok false →
          ∃ j k : Nat,
            1 ≤ j ∧ j < k ∧ j ∉ heapIndices root ∧ k ∈ heapIndices root) := by
    sorry

  /-- Whenever is_complete_tree(root) returns r = true, let h be the maximum depth of a node in root (the root has depth 0). Then h = floor(log2(n)), where n is the number of nodes. For every depth d with 0 <= d < h, the number of nodes at depth d is exactly 2^d. The number of nodes at depth h is n - (2^h - 1), and it satisfies 1 <= n - (2^h - 1) <= 2^h.
    Preconditions: root is a finite Tree built from Null and Node(v, left, right). Let n be the number of Node constructors in root. The problem constraints hold: 1 <= n <= 100, and every node value v satisfies 1 <= v <= 1000. -/
  theorem spec_9 (root : Tree) (hroot : ValidTree root) :
      is_complete_tree root = Result.ok true →
        let n := nodeCount root
        let h := height root
        h = Nat.log2 n ∧
          (∀ d : Nat, d < h → (nodesAtDepth root d).length = 2 ^ d) ∧
          (nodesAtDepth root h).length = n - (2 ^ h - 1) ∧
          1 ≤ n - (2 ^ h - 1) ∧ n - (2 ^ h - 1) ≤ 2 ^ h := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hroot : ValidTree root), is_complete_tree root = Result.ok true →
          let n := nodeCount root
          let h := height root
          h = Nat.log2 n ∧
            (∀ d : Nat, d < h → (nodesAtDepth root d).length = 2 ^ d) ∧
            (nodesAtDepth root h).length = n - (2 ^ h - 1) ∧
            1 ≤ n - (2 ^ h - 1) ∧ n - (2 ^ h - 1) ≤ 2 ^ h) := by
    sorry

  end AegisSpec.IsCompleteTree
