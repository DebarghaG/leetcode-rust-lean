import Aegis.HasPathSum.Code.Funs

/-!
# Specifications of `Aegis.HasPathSum.has_path_sum`

LeetCode problem `path-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HasPathSum

open Aegis.HasPathSum

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => nodeCount l + nodeCount r + 1

def ValuesBetween (lo hi : Int) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    lo ≤ v.val ∧ v.val ≤ hi ∧ ValuesBetween lo hi l ∧ ValuesBetween lo hi r

def treeValues : Tree → List I64
  | Tree.Null => []
  | Tree.Node v l r => v :: (treeValues l ++ treeValues r)

def rootLeafPathValues : Tree → List (List Int)
  | Tree.Null => []
  | Tree.Node v Tree.Null Tree.Null => [[v.val]]
  | Tree.Node v l r =>
    (rootLeafPathValues l).map (fun xs => v.val :: xs) ++
      (rootLeafPathValues r).map (fun xs => v.val :: xs)

def RootLeafPathValues (t : Tree) (vals : List Int) : Prop :=
  vals ∈ rootLeafPathValues t

def HasRootLeafPathSum (t : Tree) (s : Int) : Prop :=
  ∃ vals, RootLeafPathValues t vals ∧ vals.sum = s

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

def ScaledTree (c : Int) : Tree → Tree → Prop
  | Tree.Null, t' => t' = Tree.Null
  | Tree.Node v l r, t' =>
    ∃ v' l' r',
      t' = Tree.Node v' l' r' ∧ v'.val = c * v.val ∧
        ScaledTree c l l' ∧ ScaledTree c r r'

def I64Repr (x : Int) : Prop :=
  ∃ y : I64, y.val = x

/-- Whenever the function returns a result r, r = true if and only if there exists a root-to-leaf path P in root such that the sum of the values of the nodes on P equals targetSum. A root-to-leaf path is a nonempty sequence of nodes n_0, ..., n_{k-1} (k >= 1) with n_0 the root of root, each n_{i+1} the left or right child of n_i, and n_{k-1} a leaf (a Node whose left and right children are both Null). If root = Null there is no such path, so r = false.
  Preconditions: The tree rooted at root has at most 5000 nodes; every node value is in [-1000,1000]; -1000 <= targetSum <= 1000. -/
theorem spec_1 (root : Tree) (targetSum : I64)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000) :
    ∀ r, has_path_sum root targetSum = .ok r →
      (r = true ↔ HasRootLeafPathSum root targetSum.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (targetSum : I64)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000), ∀ r, has_path_sum root targetSum = Result.ok r →
      (r = true ↔ HasRootLeafPathSum root targetSum.val)) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: The tree rooted at root has at most 5000 nodes; every node value is in [-1000,1000]; -1000 <= targetSum <= 1000. -/
theorem spec_2 (root : Tree) (targetSum : I64)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000) :
    ∃ r, has_path_sum root targetSum = .ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (targetSum : I64)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000), ∃ r, has_path_sum root targetSum = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if there exists a child c in {left, right} with c != Null and there exists a root-to-leaf path Q in the subtree c (Q starts at the root of c and ends at a leaf of c) such that the sum of the values of the nodes on Q equals targetSum - v.
  Preconditions: root = Node(v, left, right) for some i64 v with -1000 <= v <= 1000, and at least one of left and right is not Null; every node value in root is in [-1000,1000]; -1000 <= targetSum <= 1000. -/
theorem spec_3 (root : Tree) (v : I64) (left right : Tree) (targetSum : I64)
    (h_root : root = Tree.Node v left right)
    (h_v : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (h_child : left ≠ Tree.Null ∨ right ≠ Tree.Null)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000) :
    ∀ r, has_path_sum root targetSum = .ok r →
      (r = true ↔
        ∃ c, (c = left ∨ c = right) ∧ c ≠ Tree.Null ∧
          HasRootLeafPathSum c (targetSum.val - v.val)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (v : I64) (left right : Tree) (targetSum : I64)
    (h_root : root = Tree.Node v left right)
    (h_v : -1000 ≤ v.val ∧ v.val ≤ 1000)
    (h_child : left ≠ Tree.Null ∨ right ≠ Tree.Null)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000), ∀ r, has_path_sum root targetSum = Result.ok r →
      (r = true ↔
        ∃ c, (c = left ∨ c = right) ∧ c ≠ Tree.Null ∧
          HasRootLeafPathSum c (targetSum.val - v.val))) := by
  sorry

/-- Whenever the function returns a result r for (root, targetSum), r = true if and only if there exists a root-to-leaf path P in root_c such that the sum of the values of the nodes on P, taken in the mathematical integers (unbounded), equals t_c.
  Preconditions: Let c be any integer with c != 0. Let root_c be the tree obtained from root by replacing every node value x with c*x, and let t_c = c*targetSum. Assume root satisfies the problem constraints (at most 5000 nodes; every node value in [-1000,1000]); -1000 <= targetSum <= 1000; every c*x for node values x is representable as i64; and c*targetSum is representable as i64. Path sums in root_c are interpreted as mathematical integers, not checked i64 arithmetic. -/
theorem spec_4 (c : Int) (root root_c : Tree) (targetSum : I64)
    (h_c : c ≠ 0)
    (h_scaled : ScaledTree c root root_c)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (h_repr : ∀ v ∈ treeValues root, I64Repr (c * v.val))
    (h_repr_target : I64Repr (c * targetSum.val)) :
    ∀ r, has_path_sum root targetSum = .ok r →
      (r = true ↔ HasRootLeafPathSum root_c (c * targetSum.val)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (c : Int) (root root_c : Tree) (targetSum : I64)
    (h_c : c ≠ 0)
    (h_scaled : ScaledTree c root root_c)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (h_repr : ∀ v ∈ treeValues root, I64Repr (c * v.val))
    (h_repr_target : I64Repr (c * targetSum.val)), ∀ r, has_path_sum root targetSum = Result.ok r →
      (r = true ↔ HasRootLeafPathSum root_c (c * targetSum.val))) := by
  sorry

/-- Let mirror(root) be the tree defined by mirror(Null) = Null and mirror(Node(v, l, r)) = Node(v, mirror(r), mirror(l)). Whenever the function returns a result r for (root, targetSum), r = true if and only if there exists a root-to-leaf path P in mirror(root) such that the sum of the values of the nodes on P equals targetSum.
  Preconditions: root satisfies the problem constraints (at most 5000 nodes, values in [-1000,1000]); -1000 <= targetSum <= 1000. -/
theorem spec_5 (root : Tree) (targetSum : I64)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000) :
    ∀ r, has_path_sum root targetSum = .ok r →
      (r = true ↔ HasRootLeafPathSum (mirror root) targetSum.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (targetSum : I64)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000), ∀ r, has_path_sum root targetSum = Result.ok r →
      (r = true ↔ HasRootLeafPathSum (mirror root) targetSum.val)) := by
  sorry

/-- Whenever the function returns a result r for (root, targetSum), r = true if and only if there exists a root-to-leaf path P in root' such that the sum of the values of the nodes on P equals targetSum.
  Preconditions: root is not Null; let root' = Node(0, root, Null); root satisfies the problem constraints (at most 5000 nodes, values in [-1000,1000]); -1000 <= targetSum <= 1000. -/
theorem spec_6 (root : Tree) (targetSum : I64)
    (h_ne : root ≠ Tree.Null)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000) :
    ∀ r, has_path_sum root targetSum = .ok r →
      (r = true ↔ HasRootLeafPathSum (Tree.Node 0#i64 root Tree.Null) targetSum.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (targetSum : I64)
    (h_ne : root ≠ Tree.Null)
    (h_nodes : nodeCount root ≤ 5000)
    (h_values : ValuesBetween (-1000) 1000 root)
    (h_target : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000), ∀ r, has_path_sum root targetSum = Result.ok r →
      (r = true ↔ HasRootLeafPathSum (Tree.Node 0#i64 root Tree.Null) targetSum.val)) := by
  sorry

end AegisSpec.HasPathSum
