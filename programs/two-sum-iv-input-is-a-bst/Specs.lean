import Aegis.FindTarget.Code.Funs

/-!
# Specifications of `Aegis.FindTarget.find_target`

LeetCode problem `two-sum-iv-input-is-a-bst`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindTarget

open Aegis.FindTarget

def mkI64 (n : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 n⟩

def nodeVals : Tree → List ℤ
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (nodeVals l ++ nodeVals r)

def treeAllInRange (lo hi : ℤ) (t : Tree) : Prop := ∀ x ∈ nodeVals t, lo ≤ x ∧ x ≤ hi

def treeIsBST : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    (∀ x ∈ nodeVals l, x < v.val) ∧ (∀ x ∈ nodeVals r, v.val < x) ∧
      treeIsBST l ∧ treeIsBST r

def HasPairSum (t : Tree) (k : ℤ) : Prop :=
  ∃ i j : Fin (nodeVals t).length, i < j ∧ (nodeVals t).get i + (nodeVals t).get j = k

def reflectNeg : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node (mkI64 (-v.val)) (reflectNeg r) (reflectNeg l)

def addC (c : ℤ) : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node (mkI64 (v.val + c)) (addC c l) (addC c r)

def scaleC (c : ℤ) : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node (mkI64 (c * v.val)) (scaleC c l) (scaleC c r)

/-- The function returns Result.ok r for some Boolean r, and r = true if and only if there exist two distinct node occurrences u and v in root (u is not the same occurrence as v) such that value(u) + value(v) = k, where value(p) is the i64 stored at node occurrence p. Addition here is mathematical integer addition; the preconditions ensure the compared sums are within i64 range.
  Preconditions: root is a valid non-empty binary search tree: it has between 1 and 10^4 node occurrences, every node value is an i64 in [-10^4, 10^4], and for every node all values in its left subtree are strictly less than its value and all values in its right subtree are strictly greater than its value; k is an i64 with -10^5 <= k <= 10^5. -/
theorem spec_1 (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
    ∃ r : Bool, find_target root k = ok r ∧ (r = true ↔ HasPairSum root k.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Bool, find_target root k = ok r ∧ (r = true ↔ HasPairSum root k.val)) := by
  sorry

/-- For every input satisfying the preconditions, find_target root k returns Result.ok r for some Boolean r; in particular it does not return an error and does not panic or overflow.
  Preconditions: root is a valid non-empty binary search tree: it has between 1 and 10^4 node occurrences, every node value is an i64 in [-10^4, 10^4], and for every node all values in its left subtree are strictly less than its value and all values in its right subtree are strictly greater than its value; k is an i64 with -10^5 <= k <= 10^5. -/
theorem spec_2 (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
    ∃ r : Bool, find_target root k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Bool, find_target root k = ok r) := by
  sorry

/-- Whenever find_target root k returns Result.ok true, there exist two distinct node occurrences u and v in root with value(u) + value(v) = k.
  Preconditions: root is a valid non-empty binary search tree: it has between 1 and 10^4 node occurrences, every node value is an i64 in [-10^4, 10^4], and for every node all values in its left subtree are strictly less than its value and all values in its right subtree are strictly greater than its value; k is an i64 with -10^5 <= k <= 10^5. -/
theorem spec_3 (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
    find_target root k = ok true → HasPairSum root k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), find_target root k = ok true → HasPairSum root k.val) := by
  sorry

/-- Whenever there exist two distinct node occurrences u and v in root with value(u) + value(v) = k, find_target root k returns Result.ok true.
  Preconditions: root is a valid non-empty binary search tree: it has between 1 and 10^4 node occurrences, every node value is an i64 in [-10^4, 10^4], and for every node all values in its left subtree are strictly less than its value and all values in its right subtree are strictly greater than its value; k is an i64 with -10^5 <= k <= 10^5. -/
theorem spec_4 (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
    HasPairSum root k.val → find_target root k = ok true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), HasPairSum root k.val → find_target root k = ok true) := by
  sorry

/-- find_target root1 k and find_target root2 k both return Result.ok, and their Boolean results are equal.
  Preconditions: root1 and root2 are valid non-empty binary search trees, each with between 1 and 10^4 nodes and node values in [-10^4, 10^4], and they have the same multiset of node values: for every integer x, the number of node occurrences with value x is the same in root1 and root2; k is an i64 with -10^5 <= k <= 10^5. -/
theorem spec_5 (root1 root2 : Tree) (k : Std.I64)
    (hsize1 : 1 ≤ (nodeVals root1).length ∧ (nodeVals root1).length ≤ 10000)
    (hbst1 : treeIsBST root1)
    (hrange1 : treeAllInRange (-10000) 10000 root1)
    (hsize2 : 1 ≤ (nodeVals root2).length ∧ (nodeVals root2).length ≤ 10000)
    (hbst2 : treeIsBST root2)
    (hrange2 : treeAllInRange (-10000) 10000 root2)
    (hmult : ∀ x : ℤ, (nodeVals root1).count x = (nodeVals root2).count x)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
    ∃ r1 r2 : Bool,
      find_target root1 k = ok r1 ∧ find_target root2 k = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root1 root2 : Tree) (k : Std.I64)
    (hsize1 : 1 ≤ (nodeVals root1).length ∧ (nodeVals root1).length ≤ 10000)
    (hbst1 : treeIsBST root1)
    (hrange1 : treeAllInRange (-10000) 10000 root1)
    (hsize2 : 1 ≤ (nodeVals root2).length ∧ (nodeVals root2).length ≤ 10000)
    (hbst2 : treeIsBST root2)
    (hrange2 : treeAllInRange (-10000) 10000 root2)
    (hmult : ∀ x : ℤ, (nodeVals root1).count x = (nodeVals root2).count x)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r1 r2 : Bool,
      find_target root1 k = ok r1 ∧ find_target root2 k = ok r2 ∧ r1 = r2) := by
  sorry

/-- find_target root k and find_target (reflectNeg(root)) (-k) both return Result.ok, and their Boolean results are equal.
  Preconditions: root is a valid non-empty binary search tree with between 1 and 10^4 nodes and node values in [-10^4, 10^4]; k is an i64 with -10^5 <= k <= 10^5. Let reflectNeg(root) be the tree obtained by replacing every node Node(v,L,R) with Node(-v, reflectNeg(R), reflectNeg(L)), negating every value and swapping left and right subtrees. -/
theorem spec_6 (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
    ∃ r1 r2 : Bool,
      find_target root k = ok r1 ∧
        find_target (reflectNeg root) (mkI64 (-k.val)) = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r1 r2 : Bool,
      find_target root k = ok r1 ∧
        find_target (reflectNeg root) (mkI64 (-k.val)) = ok r2 ∧ r1 = r2) := by
  sorry

/-- find_target root k and find_target (addC(root,c)) (k+2c) both return Result.ok, and their Boolean results are equal.
  Preconditions: root is a valid non-empty binary search tree with between 1 and 10^4 nodes and node values in [-10^4, 10^4]; k is an i64 with -10^5 <= k <= 10^5; c is an integer such that for every node value v of root, v+c is in [-10^4, 10^4], and k+2c is in [-10^5, 10^5]. Let addC(root,c) be the tree obtained by replacing every node Node(v,L,R) with Node(v+c, addC(L,c), addC(R,c)). -/
theorem spec_7 (root : Tree) (k : Std.I64) (c : ℤ)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000)
    (hc : ∀ v ∈ nodeVals root, -10000 ≤ v + c ∧ v + c ≤ 10000)
    (hkc : -100000 ≤ k.val + 2 * c ∧ k.val + 2 * c ≤ 100000) :
    ∃ r1 r2 : Bool,
      find_target root k = ok r1 ∧
        find_target (addC c root) (mkI64 (k.val + 2 * c)) = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (c : ℤ)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000)
    (hc : ∀ v ∈ nodeVals root, -10000 ≤ v + c ∧ v + c ≤ 10000)
    (hkc : -100000 ≤ k.val + 2 * c ∧ k.val + 2 * c ≤ 100000), ∃ r1 r2 : Bool,
      find_target root k = ok r1 ∧
        find_target (addC c root) (mkI64 (k.val + 2 * c)) = ok r2 ∧ r1 = r2) := by
  sorry

/-- find_target root k and find_target (scale(root,c)) (c*k) both return Result.ok, and their Boolean results are equal.
  Preconditions: root is a valid non-empty binary search tree with between 1 and 10^4 nodes and node values in [-10^4, 10^4]; k is an i64 with -10^5 <= k <= 10^5; c is a positive integer such that for every node value v of root, c*v is in [-10^4, 10^4], and c*k is in [-10^5, 10^5]. Let scale(root,c) be the tree obtained by replacing every node Node(v,L,R) with Node(c*v, scale(L,c), scale(R,c)). -/
theorem spec_8 (root : Tree) (k : Std.I64) (c : ℤ)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000)
    (hcpos : 0 < c)
    (hc : ∀ v ∈ nodeVals root, -10000 ≤ c * v ∧ c * v ≤ 10000)
    (hkc : -100000 ≤ c * k.val ∧ c * k.val ≤ 100000) :
    ∃ r1 r2 : Bool,
      find_target root k = ok r1 ∧
        find_target (scaleC c root) (mkI64 (c * k.val)) = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (c : ℤ)
    (hsize : 1 ≤ (nodeVals root).length ∧ (nodeVals root).length ≤ 10000)
    (hbst : treeIsBST root)
    (hrange : treeAllInRange (-10000) 10000 root)
    (hk : -100000 ≤ k.val ∧ k.val ≤ 100000)
    (hcpos : 0 < c)
    (hc : ∀ v ∈ nodeVals root, -10000 ≤ c * v ∧ c * v ≤ 10000)
    (hkc : -100000 ≤ c * k.val ∧ c * k.val ≤ 100000), ∃ r1 r2 : Bool,
      find_target root k = ok r1 ∧
        find_target (scaleC c root) (mkI64 (c * k.val)) = ok r2 ∧ r1 = r2) := by
  sorry

end AegisSpec.FindTarget
