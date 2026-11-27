import Aegis.RemoveLeafNodes.Code.Funs

/-!
# Specifications of `Aegis.RemoveLeafNodes.remove_leaf_nodes`

LeetCode problem `delete-leaves-with-a-given-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.RemoveLeafNodes

  namespace AegisSpec.RemoveLeafNodes

  abbrev Path := List Bool

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => size l + size r + 1

  def nodeAt : Tree → Path → Option Tree
    | Tree.Null, _ => none
    | Tree.Node v l r, [] => some (Tree.Node v l r)
    | Tree.Node _ l _, false :: rest => nodeAt l rest
    | Tree.Node _ _ r, true :: rest => nodeAt r rest

  def valueAt : Tree → Path → Option Int
    | Tree.Null, _ => none
    | Tree.Node v _ _, [] => some v.val
    | Tree.Node _ l _, false :: rest => valueAt l rest
    | Tree.Node _ _ r, true :: rest => valueAt r rest

  def ValidAt (t : Tree) (p : Path) : Prop := ∃ v, valueAt t p = some v

  def IsLeaf (t : Tree) : Prop := ∃ v, t = Tree.Node v Tree.Null Tree.Null

  def LeafAt (t : Tree) (p : Path) : Prop := ∃ x, nodeAt t p = some x ∧ IsLeaf x

  def AllValuesEq (t : Tree) (n : Int) : Prop := ∀ p v, valueAt t p = some v → v = n

  def ValuesBetween (t : Tree) (lo hi : Int) : Prop :=
    ∀ p v, valueAt t p = some v → lo ≤ v ∧ v ≤ hi

  def NoValueEq (t : Tree) (n : Int) : Prop := ∀ p v, valueAt t p = some v → v ≠ n

  def allValuesEqB : Tree → Int → Bool
    | Tree.Null, _ => true
    | Tree.Node v l r, n => (v.val == n) && allValuesEqB l n && allValuesEqB r n

  def countAllValuesEq : Tree → Int → Nat
    | Tree.Null, _ => 0
    | Tree.Node v l r, n =>
      let k := countAllValuesEq l n + countAllValuesEq r n
      if allValuesEqB (Tree.Node v l r) n then k + 1 else k

  def prune : Tree → Int → Tree
    | Tree.Null, _ => Tree.Null
    | Tree.Node v l r, target =>
      match prune l target, prune r target with
      | Tree.Null, Tree.Null =>
        if v.val = target then Tree.Null else Tree.Node v Tree.Null Tree.Null
      | pl, pr => Tree.Node v pl pr

  def NoTargetLeaf : Tree → Int → Prop
    | Tree.Null, _ => True
    | Tree.Node v l r, n =>
      ¬ (v.val = n ∧ l = Tree.Null ∧ r = Tree.Null) ∧ NoTargetLeaf l n ∧ NoTargetLeaf r n

  def inorder : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => inorder l ++ v.val :: inorder r

  inductive Induced : Tree → Tree → Prop where

    | null (t : Tree) : Induced t Tree.Null

    | node (v : Std.I64) (tl tr l r : Tree) :
        Induced tl l → Induced tr r → Induced (Tree.Node v tl tr) (Tree.Node v l r)

  def Pre (root : Tree) (target : Std.I64) : Prop :=
    1 ≤ size root ∧ size root ≤ 3000 ∧ ValuesBetween root 1 1000 ∧
      1 ≤ target.val ∧ target.val ≤ 1000

  /-- The function returns a result r, and r equals the tree obtained by the following recursive pruning operation: prune(Null) = Null; for a node Node(v, l, r), first prune l and r to pl and pr, then prune(Node(v, l, r)) = Null if v = target and pl = Null and pr = Null, and prune(Node(v, l, r)) = Node(v, pl, pr) otherwise.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_1 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∃ r, remove_leaf_nodes root target = ok r ∧ r = prune root target.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∃ r, remove_leaf_nodes root target = ok r ∧ r = prune root target.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_2 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∃ r, remove_leaf_nodes root target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∃ r, remove_leaf_nodes root target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there is no node in r that is a leaf of r (i.e., has both children Null) and whose value is target.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_3 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r → NoTargetLeaf r target.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r → NoTargetLeaf r target.val) := by
    sorry

  /-- For every path p valid in root, if the node at p in root has value different from target, then p is valid in r and the node at p in r has the same value as the node at p in root.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_4 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r →
        ∀ (p : Path) (v : Int), valueAt root p = some v → v ≠ target.val →
          valueAt r p = some v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r →
          ∀ (p : Path) (v : Int), valueAt root p = some v → v ≠ target.val →
            valueAt r p = some v) := by
    sorry

  /-- For every path p valid in root with value_root(p) = target, p is valid in r if and only if there exists a finite path q such that p@q is valid in root and value_root(p@q) != target.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_5 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r →
        ∀ p : Path, valueAt root p = some target.val →
          (ValidAt r p ↔
            ∃ q : Path, ∃ v : Int, valueAt root (p ++ q) = some v ∧ v ≠ target.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r →
          ∀ p : Path, valueAt root p = some target.val →
            (ValidAt r p ↔
              ∃ q : Path, ∃ v : Int, valueAt root (p ++ q) = some v ∧ v ≠ target.val)) := by
    sorry

  /-- Whenever the function returns a result r, the nodes of r can be identified with a subset S of the nodes of root such that: every node in S has the same value as the corresponding node of root; for every x in S, the left child of x in r is the node corresponding to x's left child in root if that child belongs to S, and is Null otherwise, and similarly for the right child; if root belongs to S then the root of r corresponds to root, and if root does not belong to S then r = Null.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_6 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r → Induced root r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r → Induced root r) := by
    sorry

  /-- Whenever the function returns a result r, let D be the set of nodes x of root such that x.value = target and every node in the subtree of root rooted at x has value target. Then the number of nodes of r equals the number of nodes of root minus the number of nodes in D.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_7 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r →
        size r = size root - countAllValuesEq root target.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r →
          size r = size root - countAllValuesEq root target.val) := by
    sorry

  /-- Whenever the function returns a result r, r = Null if and only if every node of root has value target.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_8 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r →
        (r = Tree.Null ↔ AllValuesEq root target.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r →
          (r = Tree.Null ↔ AllValuesEq root target.val)) := by
    sorry

  /-- Whenever the function returns a result r, if no node of root has value target, then r = root.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_9 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r →
        NoValueEq root target.val → r = root := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r →
          NoValueEq root target.val → r = root) := by
    sorry

  /-- For every path p valid in root with value_root(p) != target, p is valid in r, and p is a leaf of r if and only if no nonempty extension p@q is valid in root with value_root(p@q) != target.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_10 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r →
        ∀ (p : Path) (v : Int), valueAt root p = some v → v ≠ target.val →
          ValidAt r p ∧
            (LeafAt r p ↔
              ∀ q : Path, q ≠ [] →
                ∀ w : Int, valueAt root (p ++ q) = some w → w = target.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r →
          ∀ (p : Path) (v : Int), valueAt root p = some v → v ≠ target.val →
            ValidAt r p ∧
              (LeafAt r p ↔
                ∀ q : Path, q ≠ [] →
                  ∀ w : Int, valueAt root (p ++ q) = some w → w = target.val)) := by
    sorry

  /-- Whenever the function returns a result r, the in-order sequence of values of r is a subsequence of the in-order sequence of values of root.
    Preconditions: root has between 1 and 3000 nodes inclusive, every node value in root is in [1, 1000], and target is in [1, 1000]. -/
  theorem spec_11 (root : Tree) (target : Std.I64)
      (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
      (hvals : ValuesBetween root 1 1000)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r, remove_leaf_nodes root target = ok r → (inorder r).Sublist (inorder root) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (target : Std.I64)
        (hsize1 : 1 ≤ size root) (hsize2 : size root ≤ 3000)
        (hvals : ValuesBetween root 1 1000)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 1000), ∀ r, remove_leaf_nodes root target = ok r → (inorder r).Sublist (inorder root)) := by
    sorry

  end AegisSpec.RemoveLeafNodes
