import Aegis.MinDiffInBst.Code.Funs

/-!
# Specifications of `Aegis.MinDiffInBst.min_diff_in_bst`

LeetCode problem `minimum-distance-between-bst-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinDiffInBst

namespace AegisSpec.MinDiffInBst

def nodeVals : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => nodeVals l ++ [v.val] ++ nodeVals r

def nodeCount (t : Tree) : Nat := (nodeVals t).length

def isBST : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
      isBST l ∧ isBST r ∧
        (∀ x, x ∈ nodeVals l → x < v.val) ∧
        (∀ x, x ∈ nodeVals r → v.val < x)

def StrictInc : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ StrictInc (y :: rest)

def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def adjacentDiffs : List Int → List Int
  | [] => []
  | [_] => []
  | x :: y :: rest => (y - x) :: adjacentDiffs (y :: rest)

def minAdjDiff (a : List Int) : Int :=
  match adjacentDiffs a with
  | [] => 0
  | d :: ds => ds.foldl min d

def HasPairDiffEq (t : Tree) (d : Int) : Prop :=
  ∃ i j : Fin (nodeVals t).length,
    i ≠ j ∧ |(nodeVals t).get i - (nodeVals t).get j| = d

def HasPairDiffLe (t : Tree) (d : Int) : Prop :=
  ∃ i j : Fin (nodeVals t).length,
    i ≠ j ∧ |(nodeVals t).get i - (nodeVals t).get j| ≤ d

def AllPairDiffGe (t : Tree) (d : Int) : Prop :=
  ∀ i j : Fin (nodeVals t).length,
    i ≠ j → d ≤ |(nodeVals t).get i - (nodeVals t).get j|

def IsShift : Tree → Tree → Int → Prop
  | Tree.Null, rc, _ => rc = Tree.Null
  | Tree.Node v l r, rc, c =>
      match rc with
      | Tree.Null => False
      | Tree.Node v' l' r' =>
          v'.val = v.val + c ∧ IsShift l l' c ∧ IsShift r r' c

/-- Whenever min_diff_in_bst(root) returns a result r, r is the least absolute difference between the values of two distinct nodes of root: there exist distinct nodes u and v of root with |val(u)-val(v)| = r, and for every pair of distinct nodes u and v of root, r <= |val(u)-val(v)|, where val(u) denotes the value stored at node u.
  Preconditions: root is a binary search tree (for every node, all values in its left subtree are strictly less than the node's value and all values in its right subtree are strictly greater), the number n of nodes in root satisfies 2 <= n <= 100, and every node value lies in [0, 100000]. -/
theorem spec_1 (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000) :
    ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      HasPairDiffEq root r.val ∧ AllPairDiffGe root r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000), ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      HasPairDiffEq root r.val ∧ AllPairDiffGe root r.val) := by
  sorry

/-- For every root satisfying the preconditions, the call min_diff_in_bst(root) returns a result r (Result.ok r); it does not fail, panic, or overflow.
  Preconditions: root is a binary search tree (for every node, all values in its left subtree are strictly less than the node's value and all values in its right subtree are strictly greater), the number n of nodes in root satisfies 2 <= n <= 100, and every node value lies in [0, 100000]. -/
theorem spec_2 (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000) :
    ∃ r, min_diff_in_bst root = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000), ∃ r, min_diff_in_bst root = Aeneas.Std.Result.ok r) := by
  sorry

/-- Whenever min_diff_in_bst(root) returns r, 1 <= r <= 100000.
  Preconditions: root is a binary search tree (for every node, all values in its left subtree are strictly less than the node's value and all values in its right subtree are strictly greater), the number n of nodes in root satisfies 2 <= n <= 100, and every node value lies in [0, 100000]. -/
theorem spec_3 (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000) :
    ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      1 ≤ r.val ∧ r.val ≤ 100000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000), ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      1 ≤ r.val ∧ r.val ≤ 100000) := by
  sorry

/-- Let a[0] < a[1] < ... < a[n-1] be all node values of root in strictly increasing order. Whenever min_diff_in_bst(root) returns r, r = min over i with 0 <= i < n-1 of (a[i+1] - a[i]).
  Preconditions: root is a binary search tree (for every node, all values in its left subtree are strictly less than the node's value and all values in its right subtree are strictly greater), the number n of nodes in root satisfies 2 <= n <= 100, and every node value lies in [0, 100000]. -/
theorem spec_4 (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000) :
    ∀ (a : List Int), StrictInc a → a.Perm (nodeVals root) →
      ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
        r.val = minAdjDiff a := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000), ∀ (a : List Int), StrictInc a → a.Perm (nodeVals root) →
      ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
        r.val = minAdjDiff a) := by
  sorry

/-- Let mn be the minimum node value in root and mx the maximum node value in root. Whenever min_diff_in_bst(root) returns r, r <= mx - mn.
  Preconditions: root is a binary search tree (for every node, all values in its left subtree are strictly less than the node's value and all values in its right subtree are strictly greater), the number n of nodes in root satisfies 2 <= n <= 100, and every node value lies in [0, 100000]. -/
theorem spec_5 (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000) :
    ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      r.val ≤ listMax (nodeVals root) - listMin (nodeVals root) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000), ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      r.val ≤ listMax (nodeVals root) - listMin (nodeVals root)) := by
  sorry

/-- For any two trees root1 and root2 satisfying the preconditions, if the multiset of node values of root1 equals the multiset of node values of root2, then whenever min_diff_in_bst(root1) returns r1 and min_diff_in_bst(root2) returns r2, r1 = r2.
  Preconditions: root1 and root2 are binary search trees (for every node, all values in its left subtree are strictly less than the node's value and all values in its right subtree are strictly greater), each has between 2 and 100 nodes inclusive, and every node value in each tree lies in [0, 100000]. -/
theorem spec_6 (root1 root2 : Tree)
    (hbst1 : isBST root1) (hbst2 : isBST root2)
    (hn1_2 : 2 ≤ nodeCount root1) (hn1_100 : nodeCount root1 ≤ 100)
    (hn2_2 : 2 ≤ nodeCount root2) (hn2_100 : nodeCount root2 ≤ 100)
    (hvals1 : ∀ x ∈ nodeVals root1, 0 ≤ x ∧ x ≤ 100000)
    (hvals2 : ∀ x ∈ nodeVals root2, 0 ≤ x ∧ x ≤ 100000)
    (hperm : (nodeVals root1).Perm (nodeVals root2)) :
    ∀ r1 r2,
      min_diff_in_bst root1 = Aeneas.Std.Result.ok r1 →
      min_diff_in_bst root2 = Aeneas.Std.Result.ok r2 → r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root1 root2 : Tree)
    (hbst1 : isBST root1) (hbst2 : isBST root2)
    (hn1_2 : 2 ≤ nodeCount root1) (hn1_100 : nodeCount root1 ≤ 100)
    (hn2_2 : 2 ≤ nodeCount root2) (hn2_100 : nodeCount root2 ≤ 100)
    (hvals1 : ∀ x ∈ nodeVals root1, 0 ≤ x ∧ x ≤ 100000)
    (hvals2 : ∀ x ∈ nodeVals root2, 0 ≤ x ∧ x ≤ 100000)
    (hperm : (nodeVals root1).Perm (nodeVals root2)), ∀ r1 r2,
      min_diff_in_bst root1 = Aeneas.Std.Result.ok r1 →
      min_diff_in_bst root2 = Aeneas.Std.Result.ok r2 → r1 = r2) := by
  sorry

/-- Whenever min_diff_in_bst(root) returns r, for every integer k with 0 <= k <= 100000, r <= k if and only if there exist two distinct nodes u and v of root such that |val(u)-val(v)| <= k, where val(u) denotes the value stored at node u.
  Preconditions: root is a binary search tree (for every node, all values in its left subtree are strictly less than the node's value and all values in its right subtree are strictly greater), the number n of nodes in root satisfies 2 <= n <= 100, and every node value lies in [0, 100000]. -/
theorem spec_7 (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000) :
    ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      ∀ k : Int, 0 ≤ k → k ≤ 100000 →
        (r.val ≤ k ↔ HasPairDiffLe root k) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000), ∀ r, min_diff_in_bst root = Aeneas.Std.Result.ok r →
      ∀ k : Int, 0 ≤ k → k ≤ 100000 →
        (r.val ≤ k ↔ HasPairDiffLe root k)) := by
  sorry

/-- Whenever min_diff_in_bst(root) returns r and min_diff_in_bst(root_c) returns r_c, r = r_c.
  Preconditions: root is a binary search tree with between 2 and 100 nodes inclusive and all node values in [0, 100000]; c is an integer such that v+c lies in [0, 100000] for every node value v of root; root_c is the tree obtained from root by replacing every node value v with v+c while keeping the same left/right shape. -/
theorem spec_8 (root root_c : Tree) (c : Int)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000)
    (hc : ∀ x ∈ nodeVals root, 0 ≤ x + c ∧ x + c ≤ 100000)
    (hshift : IsShift root root_c c) :
    ∀ r r_c,
      min_diff_in_bst root = Aeneas.Std.Result.ok r →
      min_diff_in_bst root_c = Aeneas.Std.Result.ok r_c → r = r_c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root root_c : Tree) (c : Int)
    (hbst : isBST root)
    (hn2 : 2 ≤ nodeCount root) (hn100 : nodeCount root ≤ 100)
    (hvals : ∀ x ∈ nodeVals root, 0 ≤ x ∧ x ≤ 100000)
    (hc : ∀ x ∈ nodeVals root, 0 ≤ x + c ∧ x + c ≤ 100000)
    (hshift : IsShift root root_c c), ∀ r r_c,
      min_diff_in_bst root = Aeneas.Std.Result.ok r →
      min_diff_in_bst root_c = Aeneas.Std.Result.ok r_c → r = r_c) := by
  sorry

end AegisSpec.MinDiffInBst
