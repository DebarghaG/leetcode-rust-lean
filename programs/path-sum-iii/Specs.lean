import Aegis.PathSum.Code.Funs

/-!
# Specifications of `Aegis.PathSum.path_sum`

LeetCode problem `path-sum-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.PathSum

namespace AegisSpec.PathSum

def nodeValues : Tree → List Int
  | .Null => []
  | .Node v l r => v.val :: (nodeValues l ++ nodeValues r)

def numNodes : Tree → Nat
  | .Null => 0
  | .Node _ l r => numNodes l + numNodes r + 1

def AllValuesWithin (lo hi : Int) (t : Tree) : Prop :=
  ∀ v ∈ nodeValues t, lo ≤ v ∧ v ≤ hi

def AllValuesEq (c : Int) (t : Tree) : Prop :=
  ∀ v ∈ nodeValues t, v = c

def countValue (c : Int) : Tree → Nat
  | .Null => 0
  | .Node v l r => (if v.val = c then 1 else 0) + countValue c l + countValue c r

def countDownFrom (t : Tree) (target acc : Int) : Nat :=
  match t with
  | .Null => 0
  | .Node v l r =>
    (if acc + v.val = target then 1 else 0)
      + countDownFrom l target (acc + v.val)
      + countDownFrom r target (acc + v.val)

def numRootPaths (t : Tree) (target : Int) : Nat := countDownFrom t target 0

def numPaths (t : Tree) (target : Int) : Nat :=
  match t with
  | .Null => 0
  | .Node _ l r => numRootPaths t target + numPaths l target + numPaths r target

def numAncestorDescPairs : Tree → Nat
  | .Null => 0
  | .Node _ l r => (numNodes l + numNodes r + 1) + numAncestorDescPairs l + numAncestorDescPairs r

def mirror : Tree → Tree
  | .Null => .Null
  | .Node v l r => .Node v (mirror r) (mirror l)

def negI64 (v : Std.I64) : Std.I64 := ⟨-v.bv⟩

def negTree : Tree → Tree
  | .Null => .Null
  | .Node v l r => .Node (negI64 v) (negTree l) (negTree r)

def countRootPathsOrZero : Tree → Int → Nat
  | .Null, _ => 0
  | .Node v l r, t => numRootPaths (Tree.Node v l r) t

/-- Whenever the function returns a result r, r equals the number of ordered pairs (u, v) of nodes of root such that v is in the subtree rooted at u and the sum of the values of the nodes on the unique downward path from u to v equals targetSum. A downward path is nonempty (u = v is allowed and gives the one-node path), and different node positions are counted separately even if their value sequences coincide.
  Preconditions: root is a finite binary tree with at most 1000 nodes; every node value v satisfies -10^9 <= v <= 10^9; and -1000 <= targetSum <= 1000. -/
theorem spec_1 (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r) :
    r.val = (numPaths root targetSum.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r), r.val = (numPaths root targetSum.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= N*(N+1)/2, where N is the number of nodes in root. Moreover, r is at most the number P of ordered ancestor-descendant pairs (u, v) with v in the subtree rooted at u, including u = v; note that P <= N*(N+1)/2, and P can be strictly smaller depending on the shape of root.
  Preconditions: root is a finite binary tree with at most 1000 nodes; every node value v satisfies -10^9 <= v <= 10^9; and -1000 <= targetSum <= 1000. -/
theorem spec_2 (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r) :
    let N : Int := numNodes root
    let P : Int := numAncestorDescPairs root
    0 ≤ r.val ∧ r.val ≤ N * (N + 1) / 2 ∧ r.val ≤ P := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r), let N : Int := numNodes root
    let P : Int := numAncestorDescPairs root
    0 ≤ r.val ∧ r.val ≤ N * (N + 1) / 2 ∧ r.val ≤ P) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: root = Null and -1000 <= targetSum <= 1000. -/
theorem spec_3 (root : Tree) (targetSum : Std.I64)
    (hroot : root = Tree.Null)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r) :
    r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hroot : root = Tree.Null)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if v = targetSum, and r = 0 otherwise.
  Preconditions: root = Node(v, Null, Null), -10^9 <= v <= 10^9, and -1000 <= targetSum <= 1000. -/
theorem spec_4 (v : Std.I64) (targetSum : Std.I64)
    (hv : -(10 ^ 9) ≤ v.val ∧ v.val ≤ 10 ^ 9)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64)
    (hres : Aegis.PathSum.path_sum (Tree.Node v Tree.Null Tree.Null) targetSum = ok r) :
    r.val = if v.val = targetSum.val then 1 else 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (v : Std.I64) (targetSum : Std.I64)
    (hv : -(10 ^ 9) ≤ v.val ∧ v.val ≤ 10 ^ 9)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64)
    (hres : Aegis.PathSum.path_sum (Tree.Node v Tree.Null Tree.Null) targetSum = ok r), r.val = if v.val = targetSum.val then 1 else 0) := by
  sorry

/-- Whenever the function returns a result r, r equals the total number of nonempty downward paths in root, i.e. the number of ordered ancestor-descendant pairs (u, v) with v in the subtree rooted at u, including u = v.
  Preconditions: Every node of root has value 0, targetSum = 0, and root has at most 1000 nodes. -/
theorem spec_5 (root : Tree) (targetSum : Std.I64)
    (hzero : AllValuesEq 0 root)
    (htarget : targetSum.val = 0)
    (hsize : numNodes root ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r) :
    r.val = (numAncestorDescPairs root : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hzero : AllValuesEq 0 root)
    (htarget : targetSum.val = 0)
    (hsize : numNodes root ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r), r.val = (numAncestorDescPairs root : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= Z, where Z is the number of nodes of root whose value is 0.
  Preconditions: targetSum = 0; root has at most 1000 nodes; and every node value v satisfies -10^9 <= v <= 10^9. -/
theorem spec_6 (root : Tree) (targetSum : Std.I64)
    (htarget : targetSum.val = 0)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r) :
    (countValue 0 root : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (htarget : targetSum.val = 0)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r), (countValue 0 root : Int) ≤ r.val) := by
  sorry

/-- Let mirror(root) be the binary tree obtained from root by recursively exchanging the left and right children at every node. Whenever the function returns a result r for (root, targetSum) and a result r' for (mirror(root), targetSum), we have r = r'.
  Preconditions: root is a finite binary tree with at most 1000 nodes; every node value v satisfies -10^9 <= v <= 10^9; and -1000 <= targetSum <= 1000. -/
theorem spec_7 (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r r' : Std.I64)
    (hres : Aegis.PathSum.path_sum root targetSum = ok r)
    (hres' : Aegis.PathSum.path_sum (mirror root) targetSum = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r r' : Std.I64)
    (hres : Aegis.PathSum.path_sum root targetSum = ok r)
    (hres' : Aegis.PathSum.path_sum (mirror root) targetSum = ok r'), r.val = r'.val) := by
  sorry

/-- Let neg(root) be the tree obtained from root by replacing every node value v by -v. Whenever the function returns a result r for (root, targetSum) and a result r' for (neg(root), -targetSum), we have r = r'.
  Preconditions: root is a finite binary tree with at most 1000 nodes; every node value v satisfies -10^9 <= v <= 10^9; and -1000 <= targetSum <= 1000. -/
theorem spec_8 (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r r' : Std.I64)
    (hres : Aegis.PathSum.path_sum root targetSum = ok r)
    (hres' : Aegis.PathSum.path_sum (negTree root) (negI64 targetSum) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r r' : Std.I64)
    (hres : Aegis.PathSum.path_sum root targetSum = ok r)
    (hres' : Aegis.PathSum.path_sum (negTree root) (negI64 targetSum) = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r >= R, where R is the number of nodes v of root such that the unique downward path from the root of root to v has sum targetSum, including v = root itself.
  Preconditions: root is a finite binary tree with at most 1000 nodes; every node value v satisfies -10^9 <= v <= 10^9; and -1000 <= targetSum <= 1000. -/
theorem spec_9 (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r) :
    (numRootPaths root targetSum.val : Int) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (r : Std.I64) (hres : Aegis.PathSum.path_sum root targetSum = ok r), (numRootPaths root targetSum.val : Int) ≤ r.val) := by
  sorry

/-- Let T' = Node(c, root, Null). Define q = 0 if root = Null; otherwise let q be the number of nodes v of root, including the root of root, such that the unique downward path in root from the root of root to v has sum targetSum - c. Whenever the function returns a result r for (root, targetSum) and a result r' for (T', targetSum), we have r' = r + q + (1 if c = targetSum else 0).
  Preconditions: root is a finite binary tree with at most 999 nodes; every node value v satisfies -10^9 <= v <= 10^9; -1000 <= targetSum <= 1000; and -10^9 <= c <= 10^9. -/
theorem spec_10 (root : Tree) (targetSum c : Std.I64)
    (hsize : numNodes root ≤ 999)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (hc : -(10 ^ 9) ≤ c.val ∧ c.val ≤ 10 ^ 9)
    (r r' : Std.I64)
    (hres : Aegis.PathSum.path_sum root targetSum = ok r)
    (hres' : Aegis.PathSum.path_sum (Tree.Node c root Tree.Null) targetSum = ok r') :
    r'.val = r.val + (countRootPathsOrZero root (targetSum.val - c.val) : Int)
      + (if c.val = targetSum.val then 1 else 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (targetSum c : Std.I64)
    (hsize : numNodes root ≤ 999)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000)
    (hc : -(10 ^ 9) ≤ c.val ∧ c.val ≤ 10 ^ 9)
    (r r' : Std.I64)
    (hres : Aegis.PathSum.path_sum root targetSum = ok r)
    (hres' : Aegis.PathSum.path_sum (Tree.Node c root Tree.Null) targetSum = ok r'), r'.val = r.val + (countRootPathsOrZero root (targetSum.val - c.val) : Int)
      + (if c.val = targetSum.val then 1 else 0)) := by
  sorry

/-- The function returns a result r: it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: root is a finite binary tree with at most 1000 nodes; every node value v satisfies -10^9 <= v <= 10^9; and -1000 <= targetSum <= 1000. -/
theorem spec_11 (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000) :
    ∃ r : Std.I64, Aegis.PathSum.path_sum root targetSum = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (targetSum : Std.I64)
    (hsize : numNodes root ≤ 1000)
    (hvals : AllValuesWithin (-(10 ^ 9)) (10 ^ 9) root)
    (htarget : -1000 ≤ targetSum.val ∧ targetSum.val ≤ 1000), ∃ r : Std.I64, Aegis.PathSum.path_sum root targetSum = ok r) := by
  sorry

end AegisSpec.PathSum
