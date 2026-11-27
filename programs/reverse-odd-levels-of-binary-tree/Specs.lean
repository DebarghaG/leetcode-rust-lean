import Aegis.ReverseOddLevels.Code.Funs

/-!
# Specifications of `Aegis.ReverseOddLevels.reverse_odd_levels`

LeetCode problem `reverse-odd-levels-of-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ReverseOddLevels

namespace AegisSpec.ReverseOddLevels

def perfectLevels : Tree → Option Nat
  | Tree.Null => some 0
  | Tree.Node _ l r =>
    match perfectLevels l, perfectLevels r with
    | some a, some b => if a = b then some (a + 1) else none
    | _, _ => none

def IsPerfectTree (t : Tree) : Prop := ∃ n, 1 ≤ n ∧ perfectLevels t = some n

def height : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => max (height l) (height r) + 1

def maxDepth (t : Tree) : Nat := height t - 1

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => nodeCount l + nodeCount r + 1

def values : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (values l ++ values r)

def AllValuesIn (lo hi : Int) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    lo ≤ v.val ∧ v.val ≤ hi ∧ AllValuesIn lo hi l ∧ AllValuesIn lo hi r

def levelValues : Tree → Nat → List Int
  | Tree.Null, _ => []
  | Tree.Node v _ _, 0 => [v.val]
  | Tree.Node _ l r, d + 1 => levelValues l d ++ levelValues r d

def follow : Tree → List Bool → Option Tree
  | t, [] => some t
  | Tree.Null, _ :: _ => none
  | Tree.Node _ l _, false :: bs => follow l bs
  | Tree.Node _ _ r, true :: bs => follow r bs

def pathBits : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, p => p.testBit n :: pathBits n p

def nodeAt (t : Tree) (d p : Nat) : Option Tree := follow t (pathBits d p)

def valueAt (t : Tree) (d p : Nat) : Option Int :=
  (nodeAt t d p).bind fun s =>
    match s with
    | Tree.Null => none
    | Tree.Node v _ _ => some v.val

/-- Whenever reverse_odd_levels(root) returns a result r, let H be the maximum depth of a node in root. Then r has nodes exactly at depths 0 through H, with exactly 2^d nodes at each depth d, in the same left-to-right positions as root. For every d with 0 <= d <= H and every p with 0 <= p < 2^d, the value at depth d, left-to-right position p in r equals: (a) the value at depth d, position p in root when d is even; (b) the value at depth d, position 2^d - 1 - p in root when d is odd. At depth d, position p is the 0-based left-to-right index; equivalently it is the d-bit path from the root with L=0 and R=1.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_1 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    (∀ d, d ≤ maxDepth root → (levelValues r d).length = 2 ^ d) ∧
    (∀ d, maxDepth root < d → (levelValues r d).length = 0) ∧
    (∀ d, d ≤ maxDepth root → ∀ p, p < 2 ^ d → nodeAt r d p ≠ none) ∧
    (∀ d, d ≤ maxDepth root → ∀ p, p < 2 ^ d → d % 2 = 0 →
      valueAt r d p = valueAt root d p) ∧
    (∀ d, d ≤ maxDepth root → ∀ p, p < 2 ^ d → d % 2 = 1 →
      valueAt r d p = valueAt root d (2 ^ d - 1 - p)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), (∀ d, d ≤ maxDepth root → (levelValues r d).length = 2 ^ d) ∧
    (∀ d, maxDepth root < d → (levelValues r d).length = 0) ∧
    (∀ d, d ≤ maxDepth root → ∀ p, p < 2 ^ d → nodeAt r d p ≠ none) ∧
    (∀ d, d ≤ maxDepth root → ∀ p, p < 2 ^ d → d % 2 = 0 →
      valueAt r d p = valueAt root d p) ∧
    (∀ d, d ≤ maxDepth root → ∀ p, p < 2 ^ d → d % 2 = 1 →
      valueAt r d p = valueAt root d (2 ^ d - 1 - p))) := by
  sorry

/-- reverse_odd_levels(root) returns a result r; in particular it does not fail, panic, or overflow.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_2 (root : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root) :
    ∃ r, reverse_odd_levels root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root), ∃ r, reverse_odd_levels root = ok r) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, r is a non-null perfect binary tree: every node of r has either zero or two children, and all leaves of r have the same depth.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_3 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    IsPerfectTree r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), IsPerfectTree r) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, the number of Node constructors (nodes) in r equals the number of Node constructors in root.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_4 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    nodeCount r = nodeCount root := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), nodeCount r = nodeCount root) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, the maximum depth of a node in r equals the maximum depth of a node in root.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_5 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    maxDepth r = maxDepth root := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), maxDepth r = maxDepth root) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, for every d >= 0, the number of nodes at depth d in r equals the number of nodes at depth d in root (both are 0 when d exceeds the tree height).
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_6 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    ∀ d, (levelValues r d).length = (levelValues root d).length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), ∀ d, (levelValues r d).length = (levelValues root d).length) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, for every d >= 0 and every integer v, the number of nodes at depth d in r whose value is v equals the number of nodes at depth d in root whose value is v.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_7 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    ∀ d v, (levelValues r d).count v = (levelValues root d).count v := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), ∀ d v, (levelValues r d).count v = (levelValues root d).count v) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, for every integer v, the number of nodes in r whose value is v equals the number of nodes in root whose value is v.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_8 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    ∀ v, (values r).count v = (values root).count v := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), ∀ v, (values r).count v = (values root).count v) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, for every even depth d >= 0 and every p with 0 <= p < 2^d, if root has a node at depth d, position p, then r has a node at the same depth and position whose value equals the value of that node in root.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_9 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    ∀ d, d % 2 = 0 → ∀ p, p < 2 ^ d → nodeAt root d p ≠ none →
      nodeAt r d p ≠ none ∧ valueAt r d p = valueAt root d p := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), ∀ d, d % 2 = 0 → ∀ p, p < 2 ^ d → nodeAt root d p ≠ none →
      nodeAt r d p ≠ none ∧ valueAt r d p = valueAt root d p) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, for every odd depth d at which root has nodes, if the left-to-right sequence of values at depth d in root is [a_0, a_1, ..., a_{2^d-1}], then the left-to-right sequence of values at depth d in r is [a_{2^d-1}, ..., a_1, a_0].
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_10 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    ∀ d, d % 2 = 1 → d ≤ maxDepth root → levelValues r d = (levelValues root d).reverse := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), ∀ d, d % 2 = 1 → d ≤ maxDepth root → levelValues r d = (levelValues root d).reverse) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, for every odd depth d at which root has nodes and every p with 0 <= p < 2^{d-1}, the value at depth d, position p in r equals the value at depth d, position 2^d - 1 - p in root, and the value at depth d, position 2^d - 1 - p in r equals the value at depth d, position p in root.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_11 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    ∀ d, d % 2 = 1 → d ≤ maxDepth root → ∀ p, p < 2 ^ (d - 1) →
      valueAt r d p = valueAt root d (2 ^ d - 1 - p) ∧
      valueAt r d (2 ^ d - 1 - p) = valueAt root d p := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), ∀ d, d % 2 = 1 → d ≤ maxDepth root → ∀ p, p < 2 ^ (d - 1) →
      valueAt r d p = valueAt root d (2 ^ d - 1 - p) ∧
      valueAt r d (2 ^ d - 1 - p) = valueAt root d p) := by
  sorry

/-- For every input root satisfying the preconditions, if reverse_odd_levels(root) returns r and reverse_odd_levels(r) returns r2, then r2 = root (structural equality of Tree).
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_12 (root r r2 : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r)
    (hres2 : reverse_odd_levels r = ok r2) :
    r2 = root := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root r r2 : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r)
    (hres2 : reverse_odd_levels r = ok r2), r2 = root) := by
  sorry

/-- Whenever reverse_odd_levels(root) returns a result r, every value stored in r satisfies 0 <= value <= 100000.
  Preconditions: root is a non-null perfect binary tree: every node has either zero or two children and all leaves have the same depth. The number of nodes of root is between 1 and 2^14 - 1 inclusive (i.e., at most 16383). Every integer value v stored in root satisfies 0 <= v <= 100000. Levels/depths are 0-indexed: the root has depth 0, and the depth of any other node is one more than its parent's depth. -/
theorem spec_13 (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r) :
    AllValuesIn 0 100000 r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root r : Tree)
    (hperfect : IsPerfectTree root)
    (hcount_lb : 1 ≤ nodeCount root)
    (hcount_ub : nodeCount root ≤ 2 ^ 14 - 1)
    (hvalues : AllValuesIn 0 100000 root)
    (hres : reverse_odd_levels root = ok r), AllValuesIn 0 100000 r) := by
  sorry

end AegisSpec.ReverseOddLevels
