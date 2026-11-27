import Aegis.GetMinimumDifference.Code.Funs

/-!
# Specifications of `Aegis.GetMinimumDifference.get_minimum_difference`

LeetCode problem `minimum-absolute-difference-in-bst`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetMinimumDifference

  open Aegis.GetMinimumDifference

  def inorderVals : Tree → List Std.I64
    | Tree.Null => []
    | Tree.Node v l r => inorderVals l ++ v :: inorderVals r

  def IsStrictBST : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
      IsStrictBST l ∧ IsStrictBST r ∧
        (∀ x ∈ inorderVals l, x.val < v.val) ∧ (∀ y ∈ inorderVals r, v.val < y.val)

  def AtLeastTwoNodes (root : Tree) : Prop := 2 ≤ (inorderVals root).length

  def ValuesInRange (root : Tree) : Prop :=
    ∀ x ∈ inorderVals root, 0 ≤ x.val ∧ x.val ≤ 100000

  def ValueSet (root : Tree) : Set Int :=
    { x | ∃ a ∈ inorderVals root, x = a.val }

  def AbsDiffSet (root : Tree) : Set Int :=
    { d | ∃ (i j : Nat) (a b : Std.I64),
            (inorderVals root)[i]? = some a ∧ (inorderVals root)[j]? = some b ∧
              i ≠ j ∧ d = |a.val - b.val| }

  def IsLeast (D : Set Int) (m : Int) : Prop := m ∈ D ∧ ∀ d ∈ D, m ≤ d

  def ConsecGapSet (root : Tree) : Set Int :=
    { d | ∃ (i : Nat) (a b : Std.I64),
            (inorderVals root)[i]? = some a ∧ (inorderVals root)[i + 1]? = some b ∧
              d = b.val - a.val }

  def InorderSorted (root : Tree) : Prop :=
    ∀ (i j : Nat) (a b : Std.I64), (inorderVals root)[i]? = some a →
      (inorderVals root)[j]? = some b → i < j → a.val < b.val

  def HasGapOne (root : Tree) : Prop :=
    ∃ (i j : Nat) (a b : Std.I64),
      (inorderVals root)[i]? = some a ∧ (inorderVals root)[j]? = some b ∧
        i ≠ j ∧ |a.val - b.val| = 1

  /-- Let D be the set of all integers |val(u) - val(v)| where u and v are two distinct nodes of root. The set D is finite and nonempty because root has at least two nodes. Whenever get_minimum_difference(root) returns a result r, r is the minimum element of D: r is in D, and for every d in D, r <= d.
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_1 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) :
      ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
        IsLeast (AbsDiffSet root) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root), ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
          IsLeast (AbsDiffSet root) r.val) := by
    sorry

  /-- For every root satisfying the preconditions, get_minimum_difference(root) returns a result r (that is, it does not fail, panic, overflow, or return an error).
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_2 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) :
      ∃ r : Std.I64, get_minimum_difference root = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root), ∃ r : Std.I64, get_minimum_difference root = Result.ok r) := by
    sorry

  /-- Whenever get_minimum_difference(root) returns a result r, there exist two distinct nodes u and v of root such that r = |val(u) - val(v)|.
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_3 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) :
      ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
        ∃ (i j : Nat) (a b : Std.I64),
          (inorderVals root)[i]? = some a ∧ (inorderVals root)[j]? = some b ∧
            i ≠ j ∧ r.val = |a.val - b.val| := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root), ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
          ∃ (i j : Nat) (a b : Std.I64),
            (inorderVals root)[i]? = some a ∧ (inorderVals root)[j]? = some b ∧
              i ≠ j ∧ r.val = |a.val - b.val|) := by
    sorry

  /-- Whenever get_minimum_difference(root) returns a result r, for every two distinct nodes u and v of root, r <= |val(u) - val(v)|.
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_4 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) :
      ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
        ∀ (i j : Nat) (a b : Std.I64),
          (inorderVals root)[i]? = some a → (inorderVals root)[j]? = some b → i ≠ j →
            r.val ≤ |a.val - b.val| := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root), ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
          ∀ (i j : Nat) (a b : Std.I64),
            (inorderVals root)[i]? = some a → (inorderVals root)[j]? = some b → i ≠ j →
              r.val ≤ |a.val - b.val|) := by
    sorry

  /-- Whenever get_minimum_difference(root) returns a result r, r is an integer satisfying 1 <= r <= 100000.
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_5 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) :
      ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
        1 ≤ r.val ∧ r.val ≤ 100000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root), ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
          1 ≤ r.val ∧ r.val ≤ 100000) := by
    sorry

  /-- Let v_0, v_1, ..., v_{n-1} be the node values of root listed in in-order traversal: recursively the left subtree, then the root node, then the right subtree, with n at least 2. This sequence is strictly increasing. Whenever get_minimum_difference(root) returns a result r, r = min over i with 0 <= i < n-1 of (v_{i+1} - v_i).
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_6 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) :
      InorderSorted root ∧
        ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
          IsLeast (ConsecGapSet root) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root), InorderSorted root ∧
          ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
            IsLeast (ConsecGapSet root) r.val) := by
    sorry

  /-- Let v_0, v_1, ..., v_{n-1} be the node values of root in in-order traversal, so n >= 2 and v_0 < v_1 < ... < v_{n-1}. Whenever get_minimum_difference(root) returns a result r, there exists an index i with 0 <= i < n-1 such that r = v_{i+1} - v_i.
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_7 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) :
      InorderSorted root ∧
        ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
          ∃ (i : Nat) (a b : Std.I64),
            (inorderVals root)[i]? = some a ∧ (inorderVals root)[i + 1]? = some b ∧
              r.val = b.val - a.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root), InorderSorted root ∧
          ∀ r : Std.I64, get_minimum_difference root = Result.ok r →
            ∃ (i : Nat) (a b : Std.I64),
              (inorderVals root)[i]? = some a ∧ (inorderVals root)[i + 1]? = some b ∧
                r.val = b.val - a.val) := by
    sorry

  /-- Whenever get_minimum_difference(root) returns a result r, r = 1.
    Preconditions: root is a finite strict binary search tree (BST): for every node n of root, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); root contains at least 2 nodes; every node value is an integer in [0, 100000]; there exist two distinct nodes u and v of root with |val(u) - val(v)| = 1. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_8 (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
      (hrange : ValuesInRange root) (hgap : HasGapOne root) :
      ∀ r : Std.I64, get_minimum_difference root = Result.ok r → r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hbst : IsStrictBST root) (hnodes : AtLeastTwoNodes root)
        (hrange : ValuesInRange root) (hgap : HasGapOne root), ∀ r : Std.I64, get_minimum_difference root = Result.ok r → r.val = 1) := by
    sorry

  /-- Whenever get_minimum_difference(root1) returns a result r1 and get_minimum_difference(root2) returns a result r2, r1 = r2.
    Preconditions: root1 and root2 are finite strict binary search trees (BSTs): for every node n of either tree, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); each tree contains at least 2 nodes; every node value in either tree is an integer in [0, 100000]; and the set of node values of root1 equals the set of node values of root2. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_9 (root1 root2 : Tree)
      (hbst1 : IsStrictBST root1) (hbst2 : IsStrictBST root2)
      (hnodes1 : AtLeastTwoNodes root1) (hnodes2 : AtLeastTwoNodes root2)
      (hrange1 : ValuesInRange root1) (hrange2 : ValuesInRange root2)
      (hvals : ValueSet root1 = ValueSet root2) :
      ∀ r1 r2 : Std.I64, get_minimum_difference root1 = Result.ok r1 →
        get_minimum_difference root2 = Result.ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : IsStrictBST root1) (hbst2 : IsStrictBST root2)
        (hnodes1 : AtLeastTwoNodes root1) (hnodes2 : AtLeastTwoNodes root2)
        (hrange1 : ValuesInRange root1) (hrange2 : ValuesInRange root2)
        (hvals : ValueSet root1 = ValueSet root2), ∀ r1 r2 : Std.I64, get_minimum_difference root1 = Result.ok r1 →
          get_minimum_difference root2 = Result.ok r2 → r1.val = r2.val) := by
    sorry

  /-- Whenever get_minimum_difference(root1) returns a result r1 and get_minimum_difference(root2) returns a result r2, r2 <= r1.
    Preconditions: root1 and root2 are finite strict binary search trees (BSTs): for every node n of either tree, every node value in n's left subtree is strictly less than val(n), and every node value in n's right subtree is strictly greater than val(n); each tree contains at least 2 nodes; every node value in either tree is an integer in [0, 100000]; and every node value occurring in root1 also occurs in root2. Here val(n) denotes the integer stored at node n, and Null contributes no node values. -/
  theorem spec_10 (root1 root2 : Tree)
      (hbst1 : IsStrictBST root1) (hbst2 : IsStrictBST root2)
      (hnodes1 : AtLeastTwoNodes root1) (hnodes2 : AtLeastTwoNodes root2)
      (hrange1 : ValuesInRange root1) (hrange2 : ValuesInRange root2)
      (hsub : ValueSet root1 ⊆ ValueSet root2) :
      ∀ r1 r2 : Std.I64, get_minimum_difference root1 = Result.ok r1 →
        get_minimum_difference root2 = Result.ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : IsStrictBST root1) (hbst2 : IsStrictBST root2)
        (hnodes1 : AtLeastTwoNodes root1) (hnodes2 : AtLeastTwoNodes root2)
        (hrange1 : ValuesInRange root1) (hrange2 : ValuesInRange root2)
        (hsub : ValueSet root1 ⊆ ValueSet root2), ∀ r1 r2 : Std.I64, get_minimum_difference root1 = Result.ok r1 →
          get_minimum_difference root2 = Result.ok r2 → r2.val ≤ r1.val) := by
    sorry

  end AegisSpec.GetMinimumDifference
