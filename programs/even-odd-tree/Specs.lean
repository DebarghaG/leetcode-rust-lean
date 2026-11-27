import Aegis.IsEvenOddTree.Code.Funs

/-!
# Specifications of `Aegis.IsEvenOddTree.is_even_odd_tree`

LeetCode problem `even-odd-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsEvenOddTree

  open Aegis.IsEvenOddTree

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def allValues : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (allValues l ++ allValues r)

  def levelValues : Tree → Nat → List ℤ
    | Tree.Null, _ => []
    | Tree.Node v _ _, 0 => [v.val]
    | Tree.Node _ l r, d + 1 => levelValues l d ++ levelValues r d

  def valueOf : Tree → Option ℤ
    | Tree.Null => none
    | Tree.Node v _ _ => some v.val

  def valuesInRange (lo hi : ℤ) : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        lo ≤ v.val ∧ v.val ≤ hi ∧ valuesInRange lo hi l ∧ valuesInRange lo hi r

  def uniformValue (a : ℤ) : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => v.val = a ∧ uniformValue a l ∧ uniformValue a r

  def atMostOneChild : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r =>
        (l = Tree.Null ∨ r = Tree.Null) ∧ atMostOneChild l ∧ atMostOneChild r

  def strictlyIncreasing : List ℤ → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => a < b ∧ strictlyIncreasing (b :: t)

  def strictlyDecreasing : List ℤ → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => b < a ∧ strictlyDecreasing (b :: t)

  def levelCondition (d : Nat) (l : List ℤ) : Prop :=
    if d % 2 = 0 then (∀ x ∈ l, Odd x) ∧ strictlyIncreasing l
    else (∀ x ∈ l, Even x) ∧ strictlyDecreasing l

  def depthParityOK : Tree → Nat → Prop
    | Tree.Null, _ => True
    | Tree.Node v l r, d =>
        (if d % 2 = 0 then Odd v.val else Even v.val) ∧
          depthParityOK l (d + 1) ∧ depthParityOK r (d + 1)

  def witnessTree : Tree :=
    Tree.Node 1#i64
      (Tree.Node 10#i64
        (Tree.Node 3#i64 (Tree.Node 12#i64 Tree.Null Tree.Null)
          (Tree.Node 8#i64 Tree.Null Tree.Null))
        Tree.Null)
      (Tree.Node 4#i64
        (Tree.Node 7#i64 (Tree.Node 6#i64 Tree.Null Tree.Null) Tree.Null)
        (Tree.Node 9#i64 Tree.Null (Tree.Node 2#i64 Tree.Null Tree.Null)))

  /-- Let L_d be the list of values of all nodes at depth d in the tree, ordered from left to right (i.e., by a breadth-first traversal that visits left children before right children). The function returns a result r, and r is true if and only if for every integer d >= 0: if d is even, then every value in L_d is odd and for every i with 0 <= i < len(L_d) - 1, L_d[i] < L_d[i+1]; if d is odd, then every value in L_d is even and for every i with 0 <= i < len(L_d) - 1, L_d[i] > L_d[i+1]. (For levels beyond the height of the tree, L_d is empty and the conditions are vacuously true.)
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node value is an integer in [1, 10^6]. -/
  theorem spec_1 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hrange : valuesInRange 1 1000000 root) :
      ∃ r, is_even_odd_tree root = ok r ∧
        (r = true ↔ ∀ d : Nat, levelCondition d (levelValues root d)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hrange : valuesInRange 1 1000000 root), ∃ r, is_even_odd_tree root = ok r ∧
          (r = true ↔ ∀ d : Nat, levelCondition d (levelValues root d))) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node value is an integer in [1, 10^6]. -/
  theorem spec_2 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hrange : valuesInRange 1 1000000 root) :
      ∃ r, is_even_odd_tree root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hrange : valuesInRange 1 1000000 root), ∃ r, is_even_odd_tree root = ok r) := by
    sorry

  /-- The function returns a result r, and r is true if and only if v0 is odd and v1 is even.
    Preconditions: root is a Node with value v0; exactly one of its children is a Node with value v1 and the other child is Null; that child v1 has both children Null (so the tree has exactly two nodes); v0 and v1 are integers in [1, 10^6]. -/
  theorem spec_3 (root : Tree) (v0 v1 : Std.I64)
      (hroot : root = Tree.Node v0 (Tree.Node v1 Tree.Null Tree.Null) Tree.Null ∨
        root = Tree.Node v0 Tree.Null (Tree.Node v1 Tree.Null Tree.Null))
      (hv0 : 1 ≤ v0.val ∧ v0.val ≤ 1000000)
      (hv1 : 1 ≤ v1.val ∧ v1.val ≤ 1000000) :
      ∃ r, is_even_odd_tree root = ok r ∧ (r = true ↔ Odd v0.val ∧ Even v1.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (v0 v1 : Std.I64)
        (hroot : root = Tree.Node v0 (Tree.Node v1 Tree.Null Tree.Null) Tree.Null ∨
          root = Tree.Node v0 Tree.Null (Tree.Node v1 Tree.Null Tree.Null))
        (hv0 : 1 ≤ v0.val ∧ v0.val ≤ 1000000)
        (hv1 : 1 ≤ v1.val ∧ v1.val ≤ 1000000), ∃ r, is_even_odd_tree root = ok r ∧ (r = true ↔ Odd v0.val ∧ Even v1.val)) := by
    sorry

  /-- The function returns a result r, and r is true if and only if v0 is odd, v1 is even, v2 is even, and v1 > v2.
    Preconditions: root is a Node with value v0; both its left child (value v1) and right child (value v2) are Nodes; both children are leaves (each has both children Null, so the tree has exactly three nodes); v0, v1, and v2 are integers in [1, 10^6]. -/
  theorem spec_4 (v0 v1 v2 : Std.I64)
      (hv0 : 1 ≤ v0.val ∧ v0.val ≤ 1000000)
      (hv1 : 1 ≤ v1.val ∧ v1.val ≤ 1000000)
      (hv2 : 1 ≤ v2.val ∧ v2.val ≤ 1000000) :
      ∃ r,
        is_even_odd_tree (Tree.Node v0 (Tree.Node v1 Tree.Null Tree.Null)
            (Tree.Node v2 Tree.Null Tree.Null)) = ok r ∧
          (r = true ↔ Odd v0.val ∧ Even v1.val ∧ Even v2.val ∧ v2.val < v1.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (v0 v1 v2 : Std.I64)
        (hv0 : 1 ≤ v0.val ∧ v0.val ≤ 1000000)
        (hv1 : 1 ≤ v1.val ∧ v1.val ≤ 1000000)
        (hv2 : 1 ≤ v2.val ∧ v2.val ≤ 1000000), ∃ r,
          is_even_odd_tree (Tree.Node v0 (Tree.Node v1 Tree.Null Tree.Null)
              (Tree.Node v2 Tree.Null Tree.Null)) = ok r ∧
            (r = true ↔ Odd v0.val ∧ Even v1.val ∧ Even v2.val ∧ v2.val < v1.val)) := by
    sorry

  /-- Whenever the function returns a result r and r is true, the root is a Node and its value is odd.
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node value is an integer in [1, 10^6]. -/
  theorem spec_5 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hrange : valuesInRange 1 1000000 root)
      (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true) :
      ∃ v l rr, root = Tree.Node v l rr ∧ Odd v.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hrange : valuesInRange 1 1000000 root)
        (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true), ∃ v l rr, root = Tree.Node v l rr ∧ Odd v.val) := by
    sorry

  /-- Whenever the function returns a result r and r is true, every node at depth 1 (i.e., every child of the root) has an even value.
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node value is an integer in [1, 10^6]. -/
  theorem spec_6 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hrange : valuesInRange 1 1000000 root)
      (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true) :
      ∀ x ∈ levelValues root 1, Even x := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hrange : valuesInRange 1 1000000 root)
        (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true), ∀ x ∈ levelValues root 1, Even x) := by
    sorry

  /-- Whenever the function returns a result r and r is true, if the root has both a left child and a right child, then the value of the left child is strictly greater than the value of the right child.
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node value is an integer in [1, 10^6]. -/
  theorem spec_7 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hrange : valuesInRange 1 1000000 root)
      (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true) :
      ∀ (v v1 v2 : Std.I64) (ll lr rl rr : Tree),
        root = Tree.Node v (Tree.Node v1 ll lr) (Tree.Node v2 rl rr) → v2.val < v1.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hrange : valuesInRange 1 1000000 root)
        (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true), ∀ (v v1 v2 : Std.I64) (ll lr rl rr : Tree),
          root = Tree.Node v (Tree.Node v1 ll lr) (Tree.Node v2 rl rr) → v2.val < v1.val) := by
    sorry

  /-- Whenever the function returns a result r and r is true, every node at depth 2 has an odd value.
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node value is an integer in [1, 10^6]. -/
  theorem spec_8 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hrange : valuesInRange 1 1000000 root)
      (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true) :
      ∀ x ∈ levelValues root 2, Odd x := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hrange : valuesInRange 1 1000000 root)
        (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true), ∀ x ∈ levelValues root 2, Odd x) := by
    sorry

  /-- Whenever the function returns a result r and r is true, the values of the nodes at depth 2, taken in left-to-right order, form a strictly increasing sequence (i.e., if v_0, v_1, ..., v_{k-1} are these values in left-to-right order, then v_0 < v_1 < ... < v_{k-1}).
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node value is an integer in [1, 10^6]. -/
  theorem spec_9 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hrange : valuesInRange 1 1000000 root)
      (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true) :
      strictlyIncreasing (levelValues root 2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hrange : valuesInRange 1 1000000 root)
        (r : Bool) (hres : is_even_odd_tree root = ok r) (hr : r = true), strictlyIncreasing (levelValues root 2)) := by
    sorry

  /-- The function returns a result r, and r is false.
    Preconditions: root is not Null; the tree has between 2 and 10^5 nodes; every node in the tree has the same integer value v, with v in [1, 10^6]. -/
  theorem spec_10 (root : Tree) (v : Std.I64)
      (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (huniform : uniformValue v.val root)
      (hv : 1 ≤ v.val ∧ v.val ≤ 1000000) :
      ∃ r, is_even_odd_tree root = ok r ∧ r = false := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (v : Std.I64)
        (hcount : 2 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (huniform : uniformValue v.val root)
        (hv : 1 ≤ v.val ∧ v.val ≤ 1000000), ∃ r, is_even_odd_tree root = ok r ∧ r = false) := by
    sorry

  /-- The function returns a result r, and r is true.
    Preconditions: root is the binary tree whose level-order representation (including Null for missing children) is [1,10,4,3,null,7,9,12,8,6,null,null,2]. -/
  theorem spec_11 (root : Tree) (hroot : root = witnessTree) :
      ∃ r, is_even_odd_tree root = ok r ∧ r = true := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hroot : root = witnessTree), ∃ r, is_even_odd_tree root = ok r ∧ r = true) := by
    sorry

  /-- The function returns a result r, and r is true if and only if for every node in the tree at depth d, its value is odd when d is even and even when d is odd.
    Preconditions: root is not Null; the tree has between 1 and 10^5 nodes; every node in the tree has at most one child (i.e., for every Node, at least one of its children is Null); every node value is an integer in [1, 10^6]. -/
  theorem spec_12 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
      (hone : atMostOneChild root)
      (hrange : valuesInRange 1 1000000 root) :
      ∃ r, is_even_odd_tree root = ok r ∧ (r = true ↔ depthParityOK root 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 100000)
        (hone : atMostOneChild root)
        (hrange : valuesInRange 1 1000000 root), ∃ r, is_even_odd_tree root = ok r ∧ (r = true ↔ depthParityOK root 0)) := by
    sorry

  end AegisSpec.IsEvenOddTree
