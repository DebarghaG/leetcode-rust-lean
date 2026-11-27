import Aegis.InsertIntoBst.Code.Funs

/-!
# Specifications of `Aegis.InsertIntoBst.insert_into_bst`

LeetCode problem `insert-into-a-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.InsertIntoBst

  open Aegis.InsertIntoBst

  def occurs (x : ℤ) : Tree → Prop
    | Tree.Null => False
    | Tree.Node v l r => v.val = x ∨ occurs x l ∨ occurs x r

  def values : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (values l ++ values r)

  def numNodes : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + numNodes l + numNodes r

  def IsBst : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
      (∀ x, occurs x l → x < v.val) ∧ (∀ x, occurs x r → v.val < x) ∧
        IsBst l ∧ IsBst r

  def valueSet (t : Tree) : Set ℤ := {x | occurs x t}

  def IsMin (m : ℤ) (s : Set ℤ) : Prop := m ∈ s ∧ ∀ y ∈ s, m ≤ y

  def IsMax (m : ℤ) (s : Set ℤ) : Prop := m ∈ s ∧ ∀ y ∈ s, y ≤ m

  /-- Whenever the function returns a result r, r is a binary search tree (for every node Node(v, l, r') occurring in r, every value occurring in l is strictly less than v, every value occurring in r' is strictly greater than v, and l and r' are binary search trees), and for every integer x, x occurs in r if and only if x occurs in root or x = val.
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. (Strict BST ordering implies all values in root are distinct, matching the uniqueness guarantee; the numeric-range constraints do not affect correctness.) -/
  theorem spec_1 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r →
        IsBst r ∧ ∀ x : ℤ, occurs x r ↔ occurs x root ∨ x = val.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r →
          IsBst r ∧ ∀ x : ℤ, occurs x r ↔ occurs x root ∨ x = val.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it never fails).
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_2 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∃ r, insert_into_bst root val = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∃ r, insert_into_bst root val = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every node Node(v, l, r') occurring in r: every value occurring in l is strictly less than v, every value occurring in r' is strictly greater than v, and l and r' are themselves binary search trees.
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_3 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r → IsBst r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r → IsBst r) := by
    sorry

  /-- Whenever the function returns a result r, every integer x that occurs in root also occurs in r (values(root) is a subset of values(r)).
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_4 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r → ∀ x : ℤ, occurs x root → occurs x r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r → ∀ x : ℤ, occurs x root → occurs x r) := by
    sorry

  /-- Whenever the function returns a result r, the value val occurs in r.
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_5 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r → occurs val.val r := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r → occurs val.val r) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x, if x occurs in r then x occurs in root or x = val (values(r) is a subset of values(root) ∪ {val}).
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_6 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r →
        ∀ x : ℤ, occurs x r → occurs x root ∨ x = val.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r →
          ∀ x : ℤ, occurs x r → occurs x root ∨ x = val.val) := by
    sorry

  /-- Whenever the function returns a result r, the number of nodes of r equals the number of nodes of root plus one, where the number of nodes is defined by num(Null) = 0 and num(Node(_, l, r')) = 1 + num(l) + num(r').
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_7 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r → numNodes r = numNodes root + 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r → numNodes r = numNodes root + 1) := by
    sorry

  /-- Whenever the function returns a result r, r is not the null tree; that is, r = Node(v, l, r') for some integer v and some trees l and r'.
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_8 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r → ∃ v : Std.I64, ∃ l r' : Tree, r = Tree.Node v l r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r → ∃ v : Std.I64, ∃ l r' : Tree, r = Tree.Node v l r') := by
    sorry

  /-- Whenever the function returns a result r, no integer occurs more than once in r (all node values of r are distinct).
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_9 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r → (values r).Nodup := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r → (values r).Nodup) := by
    sorry

  /-- Whenever the function returns a result r, r is not the null tree and the smallest integer occurring in r equals the smallest element of S = { x : x occurs in root } union { val }.
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_10 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r →
        r ≠ Tree.Null ∧
          ∃ m : ℤ, IsMin m (valueSet r) ∧ IsMin m (valueSet root ∪ {val.val}) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r →
          r ≠ Tree.Null ∧
            ∃ m : ℤ, IsMin m (valueSet r) ∧ IsMin m (valueSet root ∪ {val.val})) := by
    sorry

  /-- Whenever the function returns a result r, r is not the null tree and the largest integer occurring in r equals the largest element of S = { x : x occurs in root } union { val }.
    Preconditions: An integer x occurs in a tree t if t = Node(x, _, _), or t = Node(_, l, r) and x occurs in l or in r. root is a binary search tree: for every node Node(v, l, r) occurring in root, every value occurring in l is strictly less than v, every value occurring in r is strictly greater than v, and both l and r are binary search trees; and val does not occur in root. -/
  theorem spec_11 (root : Tree) (val : Std.I64) (hbst : IsBst root)
      (hnotin : ¬ occurs val.val root) :
      ∀ r, insert_into_bst root val = Result.ok r →
        r ≠ Tree.Null ∧
          ∃ m : ℤ, IsMax m (valueSet r) ∧ IsMax m (valueSet root ∪ {val.val}) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (val : Std.I64) (hbst : IsBst root)
        (hnotin : ¬ occurs val.val root), ∀ r, insert_into_bst root val = Result.ok r →
          r ≠ Tree.Null ∧
            ∃ m : ℤ, IsMax m (valueSet r) ∧ IsMax m (valueSet root ∪ {val.val})) := by
    sorry

  end AegisSpec.InsertIntoBst
