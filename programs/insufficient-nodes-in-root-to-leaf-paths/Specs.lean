import Aegis.SufficientSubset.Code.Funs

/-!
# Specifications of `Aegis.SufficientSubset.sufficient_subset`

LeetCode problem `insufficient-nodes-in-root-to-leaf-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SufficientSubset

  open Aegis.SufficientSubset

  inductive Move where
    | left : Move
    | right : Move
    deriving DecidableEq, Repr

  def follow (t : Tree) : List Move → Option Tree
    | [] =>
      match t with
      | Tree.Null => none
      | Tree.Node _ _ _ => some t
    | m :: rest =>
      match t with
      | Tree.Null => none
      | Tree.Node _ l r =>
        follow (match m with | Move.left => l | Move.right => r) rest

  def nodeValue : Tree → Option Int
    | Tree.Null => none
    | Tree.Node v _ _ => some v.val

  def valueAt (t : Tree) (d : List Move) : Option Int := (follow t d).bind nodeValue

  def isLeaf : Tree → Bool
    | Tree.Null => false
    | Tree.Node _ Tree.Null Tree.Null => true
    | Tree.Node _ _ _ => false

  def Occurs (t : Tree) (d : List Move) : Prop := (follow t d).isSome

  def ToLeaf (t : Tree) (d : List Move) : Prop :=
    ∃ u, follow t d = some u ∧ isLeaf u = true

  def pathValues (t : Tree) : List Move → List Int
    | [] =>
      match t with
      | Tree.Null => []
      | Tree.Node v _ _ => [v.val]
    | m :: rest =>
      match t with
      | Tree.Null => []
      | Tree.Node v l r =>
        v.val :: pathValues (match m with | Move.left => l | Move.right => r) rest

  def pathSum (t : Tree) (d : List Move) : Int := (pathValues t d).sum

  def Good (root : Tree) (limit : Int) (d : List Move) : Prop :=
    Occurs root d ∧ ∃ q, ToLeaf root (d ++ q) ∧ limit ≤ pathSum root (d ++ q)

  def IsPrefix (p d : List Move) : Prop := ∃ s, d = p ++ s

  def IsProperAncestor (p d : List Move) : Prop := ∃ s, s ≠ [] ∧ d = p ++ s

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + size l + size r

  def ValuesBounded : Tree → Int → Int → Prop
    | Tree.Null, _, _ => True
    | Tree.Node v l r, lo, hi =>
      lo ≤ v.val ∧ v.val ≤ hi ∧ ValuesBounded l lo hi ∧ ValuesBounded r lo hi

  /-- The function returns a result r and does not fail. Define a node occurrence n of root to be good if there exists a root-to-leaf path P of root (a sequence from the root to a node whose left and right children are both Null, following left/right child edges) such that n lies on P and the sum of the values of all nodes on P is at least limit. Then r is exactly the tree obtained from root by keeping every good node occurrence, deleting every non-good node occurrence, and preserving the original parent-child edges and left/right order among kept nodes; deleted nodes are replaced by Null. Equivalently, for every sequence d of left/right moves, d is a valid path to a node in r if and only if d is a valid path to a good node in root, and in that case the value at d in r equals the value at d in root; no other nodes occur in r. In particular, if root has no good node, equivalently every root-to-leaf path of root has sum strictly less than limit, then r = Null.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000, where size(T) is the number of Node constructors in T; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000, where limit is the integer represented by the Std.I64 argument. -/
  theorem spec_1 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000) :
      ∃ r : Tree,
        sufficient_subset root limit = ok r ∧
          (∀ d, Occurs r d ↔ Good root limit.val d) ∧
          (∀ d, Occurs r d → valueAt r d = valueAt root d) ∧
          (r = Tree.Null ↔ ∀ p, ToLeaf root p → pathSum root p < limit.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000), ∃ r : Tree,
          sufficient_subset root limit = ok r ∧
            (∀ d, Occurs r d ↔ Good root limit.val d) ∧
            (∀ d, Occurs r d → valueAt r d = valueAt root d) ∧
            (r = Tree.Null ↔ ∀ p, ToLeaf root p → pathSum root p < limit.val)) := by
    sorry

  /-- The function returns a result r and does not fail by integer overflow, out-of-bounds access, or panic for every root and limit satisfying the preconditions.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_2 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000) :
      ∃ r : Tree, sufficient_subset root limit = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000), ∃ r : Tree, sufficient_subset root limit = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = Null if and only if every root-to-leaf path of root has sum strictly less than limit, equivalently if and only if no root-to-leaf path of root has sum at least limit.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_3 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      (r = Tree.Null ↔ ∀ p, ToLeaf root p → pathSum root p < limit.val) ∧
        (r = Tree.Null ↔ ¬ ∃ p, ToLeaf root p ∧ limit.val ≤ pathSum root p) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), (r = Tree.Null ↔ ∀ p, ToLeaf root p → pathSum root p < limit.val) ∧
          (r = Tree.Null ↔ ¬ ∃ p, ToLeaf root p ∧ limit.val ≤ pathSum root p)) := by
    sorry

  /-- Whenever the function returns a result r, for every node occurrence n in root, if n appears in r at the same position (the same sequence of left/right moves from the root), then there exists a root-to-leaf path P in root containing n whose node-value sum is at least limit.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_4 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      ∀ d, Occurs root d → Occurs r d → Good root limit.val d := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), ∀ d, Occurs root d → Occurs r d → Good root limit.val d) := by
    sorry

  /-- Whenever the function returns a result r, for every node occurrence n in root, if n does not appear in r at its original position, then every root-to-leaf path P in root containing n has node-value sum strictly less than limit.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_5 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      ∀ d, Occurs root d → ¬ Occurs r d →
        ∀ q, ToLeaf root (d ++ q) → pathSum root (d ++ q) < limit.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), ∀ d, Occurs root d → ¬ Occurs r d →
          ∀ q, ToLeaf root (d ++ q) → pathSum root (d ++ q) < limit.val) := by
    sorry

  /-- Whenever the function returns a result r, for every node occurrence n in root that appears in r, every ancestor of n in root (every node on the unique path from the root of root to n, including the root if it is not n) also appears in r at its original position. Equivalently, if n appears in r and n is not the root of root, then the parent of n in root appears in r.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_6 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      (∀ d, Occurs r d → ∀ p, IsProperAncestor p d → Occurs r p) ∧
        (∀ d m, Occurs r (d ++ [m]) → Occurs r d) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), (∀ d, Occurs r d → ∀ p, IsProperAncestor p d → Occurs r p) ∧
          (∀ d m, Occurs r (d ++ [m]) → Occurs r d)) := by
    sorry

  /-- Whenever the function returns a result r, for every node occurrence n in root that appears in r, and for each side (left or right), let c be the child of n on that side in root, possibly Null. Then the child of n on that side in r is c if c is a good node (that is, some root-to-leaf path of root through c has sum at least limit), and is Null otherwise. If c = Null, the corresponding child in r is Null.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_7 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      ∀ d, Occurs root d → Occurs r d →
        ∀ m : Move,
          (Occurs r (d ++ [m]) ↔ Good root limit.val (d ++ [m])) ∧
            (¬ Occurs root (d ++ [m]) → ¬ Occurs r (d ++ [m])) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), ∀ d, Occurs root d → Occurs r d →
          ∀ m : Move,
            (Occurs r (d ++ [m]) ↔ Good root limit.val (d ++ [m])) ∧
              (¬ Occurs root (d ++ [m]) → ¬ Occurs r (d ++ [m]))) := by
    sorry

  /-- Whenever the function returns a result r, every root-to-leaf path Q of r, read as the same sequence of left/right moves from the root, is also a root-to-leaf path of root (it ends at a leaf of root and has the same node values), and the sum of the values along Q is at least limit.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_8 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      ∀ p, ToLeaf r p → ToLeaf root p ∧ pathValues r p = pathValues root p ∧
        limit.val ≤ pathSum root p := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), ∀ p, ToLeaf r p → ToLeaf root p ∧ pathValues r p = pathValues root p ∧
          limit.val ≤ pathSum root p) := by
    sorry

  /-- Whenever the function returns a result r, for every root-to-leaf path P of root whose node-value sum is at least limit, all nodes of P appear in r at their original positions, so following the same sequence of left/right moves from the root of r reaches the same leaf with the same values; hence P is also a root-to-leaf path of r.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_9 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      ∀ p, ToLeaf root p → limit.val ≤ pathSum root p →
        ToLeaf r p ∧ pathValues r p = pathValues root p := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), ∀ p, ToLeaf root p → limit.val ≤ pathSum root p →
          ToLeaf r p ∧ pathValues r p = pathValues root p) := by
    sorry

  /-- Whenever the function returns a result r, for every leaf occurrence l of root, l appears in r, necessarily as a leaf, if and only if the sum of the values on the unique path from the root of root to l is at least limit.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_10 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      ∀ d, ToLeaf root d →
        (Occurs r d ↔ limit.val ≤ pathSum root d) ∧ (Occurs r d → ToLeaf r d) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), ∀ d, ToLeaf root d →
          (Occurs r d ↔ limit.val ≤ pathSum root d) ∧ (Occurs r d → ToLeaf r d)) := by
    sorry

  /-- Whenever the function returns a result r, size(r) <= size(root), where size(T) is the number of Node constructors in T. In particular, if r != Null then 1 <= size(r) <= 5000.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_11 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      size r ≤ size root ∧ (r ≠ Tree.Null → 1 ≤ size r ∧ size r ≤ 5000) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), size r ≤ size root ∧ (r ≠ Tree.Null → 1 ≤ size r ∧ size r ≤ 5000)) := by
    sorry

  /-- Whenever the function returns a result r, for every sequence d of left/right moves that is valid in r (following d from the root of r does not hit Null before the end), the same sequence d is valid in root and the node reached in r has the same value as the node reached in root. Consequently r has no node occurrence that is not also a node occurrence of root at the same position.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 5000; every Node value v in root satisfies -100000 <= v <= 100000; and -1000000000 <= limit <= 1000000000. -/
  theorem spec_12 (root : Tree) (limit : Std.I64)
      (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
      (hvals : ValuesBounded root (-100000) 100000)
      (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
      (r : Tree) (hr : sufficient_subset root limit = ok r) :
      ∀ d, Occurs r d → Occurs root d ∧ valueAt r d = valueAt root d := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (limit : Std.I64)
        (hsize_pos : 1 ≤ size root) (hsize_le : size root ≤ 5000)
        (hvals : ValuesBounded root (-100000) 100000)
        (hlim_lo : -1000000000 ≤ limit.val) (hlim_hi : limit.val ≤ 1000000000)
        (r : Tree) (hr : sufficient_subset root limit = ok r), ∀ d, Occurs r d → Occurs root d ∧ valueAt r d = valueAt root d) := by
    sorry

  end AegisSpec.SufficientSubset
