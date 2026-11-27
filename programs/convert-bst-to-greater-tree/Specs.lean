import Aegis.ConvertBst.Code.Funs

/-!
# Specifications of `Aegis.ConvertBst.convert_bst`

LeetCode problem `convert-bst-to-greater-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ConvertBst

  open Aegis.ConvertBst (Tree convert_bst)

  inductive PathStep where
    | L : PathStep
    | R : PathStep
  deriving DecidableEq, Repr

  def treeValues : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (treeValues l ++ treeValues r)

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def valAt : Tree → List PathStep → Option Int
    | Tree.Null, _ => none
    | Tree.Node v _ _, [] => some v.val
    | Tree.Node _ l _, PathStep.L :: p => valAt l p
    | Tree.Node _ _ r, PathStep.R :: p => valAt r p

  def PathExists (t : Tree) (p : List PathStep) : Prop := ∃ x : Int, valAt t p = some x

  def IsBst : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        (∀ z ∈ treeValues l, z < v.val) ∧
        (∀ z ∈ treeValues r, v.val < z) ∧
        IsBst l ∧ IsBst r

  def treeSum (t : Tree) : Int := (treeValues t).sum

  def sumValuesGE (t : Tree) (x : Int) : Int :=
    ((treeValues t).filter (fun z => decide (x ≤ z))).sum

  def sumInRange (t : Tree) (lo hi : Int) : Int :=
    ((treeValues t).filter (fun z => decide (lo ≤ z ∧ z < hi))).sum

  def insertInt (x : Int) : List Int → List Int
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInt x ys

  def sortInts : List Int → List Int
    | [] => []
    | x :: xs => insertInt x (sortInts xs)

  def sortedValues (t : Tree) : List Int := sortInts (treeValues t)

  def suffixSums : List Int → List Int
    | [] => []
    | a :: rest => (a + rest.sum) :: suffixSums rest

  /-- Let a path be a finite sequence of L/R choices. A path p exists in a tree t if following p from the root reaches a Node, and val_t(p) is that node's i64 value. The function returns a result r (not a failure) such that: (i) for every path p, p exists in root if and only if p exists in r; (ii) for every path p that exists in root, val_r(p) equals the sum of val_root(q) over all paths q that exist in root and satisfy val_root(q) >= val_root(p).
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive. -/
  theorem spec_1 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000) :
      ∃ r : Tree, convert_bst root = ok r ∧
        (∀ p : List PathStep, PathExists root p ↔ PathExists r p) ∧
        (∀ (p : List PathStep) (x : Int), valAt root p = some x →
          valAt r p = some (sumValuesGE root x)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000), ∃ r : Tree, convert_bst root = ok r ∧
          (∀ p : List PathStep, PathExists root p ↔ PathExists r p) ∧
          (∀ (p : List PathStep) (x : Int), valAt root p = some x →
            valAt r p = some (sumValuesGE root x))) := by
    sorry

  /-- The function returns a result r (not a failure) and r has exactly the same tree shape as root: for every finite path p over L/R, p exists in root if and only if p exists in r. Equivalently, r is Null exactly when root is Null, and the two trees have the same number of nodes in every corresponding subtree.
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive. -/
  theorem spec_2 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000) :
      ∃ r : Tree, convert_bst root = ok r ∧
        (∀ p : List PathStep, PathExists root p ↔ PathExists r p) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000), ∃ r : Tree, convert_bst root = ok r ∧
          (∀ p : List PathStep, PathExists root p ↔ PathExists r p)) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds, or panic) on any input satisfying the preconditions.
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive. -/
  theorem spec_3 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000) :
      ∃ r : Tree, convert_bst root = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000), ∃ r : Tree, convert_bst root = ok r) := by
    sorry

  /-- The function returns a result r and every node value in r lies in the interval [-100000000, 100000000].
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive. -/
  theorem spec_4 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000) :
      ∃ r : Tree, convert_bst root = ok r ∧
        (∀ z ∈ treeValues r, -100000000 ≤ z ∧ z ≤ 100000000) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000), ∃ r : Tree, convert_bst root = ok r ∧
          (∀ z ∈ treeValues r, -100000000 ≤ z ∧ z ≤ 100000000)) := by
    sorry

  /-- The function returns Null.
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive; root = Null. -/
  theorem spec_5 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
      (hnull : root = Tree.Null) :
      convert_bst root = ok Tree.Null := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
        (hnull : root = Tree.Null), convert_bst root = ok Tree.Null) := by
    sorry

  /-- The function returns Node(x, Null, Null).
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive; root = Node(x, Null, Null) for some i64 x with -10000 <= x <= 10000. -/
  theorem spec_6 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
      (x : Aeneas.Std.I64) (hx : root = Tree.Node x Tree.Null Tree.Null)
      (hxb : -10000 ≤ x.val ∧ x.val ≤ 10000) :
      convert_bst root = ok (Tree.Node x Tree.Null Tree.Null) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
        (x : Aeneas.Std.I64) (hx : root = Tree.Node x Tree.Null Tree.Null)
        (hxb : -10000 ≤ x.val ∧ x.val ≤ 10000), convert_bst root = ok (Tree.Node x Tree.Null Tree.Null)) := by
    sorry

  /-- Let m be the maximum node value in root and let p_m be the unique path in root with val_root(p_m) = m (unique because values are distinct). The function returns a result r such that path p_m exists in r and val_r(p_m) = m.
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive; root is not Null. -/
  theorem spec_7 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
      (hne : root ≠ Tree.Null)
      (m : Int) (pm : List PathStep)
      (hm : valAt root pm = some m)
      (hmax : ∀ (q : List PathStep) (y : Int), valAt root q = some y → y ≤ m) :
      ∃ r : Tree, convert_bst root = ok r ∧ valAt r pm = some m := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
        (hne : root ≠ Tree.Null)
        (m : Int) (pm : List PathStep)
        (hm : valAt root pm = some m)
        (hmax : ∀ (q : List PathStep) (y : Int), valAt root q = some y → y ≤ m), ∃ r : Tree, convert_bst root = ok r ∧ valAt r pm = some m) := by
    sorry

  /-- Let a be the minimum node value in root and let p_a be the unique path in root with val_root(p_a) = a. The function returns a result r such that path p_a exists in r and val_r(p_a) equals the sum of all node values of root.
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive; root is not Null. -/
  theorem spec_8 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
      (hne : root ≠ Tree.Null)
      (a : Int) (pa : List PathStep)
      (ha : valAt root pa = some a)
      (hmin : ∀ (q : List PathStep) (y : Int), valAt root q = some y → a ≤ y) :
      ∃ r : Tree, convert_bst root = ok r ∧ valAt r pa = some (treeSum root) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
        (hne : root ≠ Tree.Null)
        (a : Int) (pa : List PathStep)
        (ha : valAt root pa = some a)
        (hmin : ∀ (q : List PathStep) (y : Int), valAt root q = some y → a ≤ y), ∃ r : Tree, convert_bst root = ok r ∧ valAt r pa = some (treeSum root)) := by
    sorry

  /-- The function returns a result r whose root value equals v plus the sum of all node values in R (the original right subtree of root; the empty sum is 0).
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive; root = Node(v, L, R) for some i64 v and trees L, R. -/
  theorem spec_9 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
      (v : Aeneas.Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R) :
      ∃ r : Tree, convert_bst root = ok r ∧
        valAt r [] = some (v.val + treeSum R) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
        (v : Aeneas.Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R), ∃ r : Tree, convert_bst root = ok r ∧
          valAt r [] = some (v.val + treeSum R)) := by
    sorry

  /-- The function returns a result r. Let val_R(q) denote the value at path q in the original subtree R. For every path p that exists in R, the corresponding path R/p (the same path inside the right subtree of r) exists in r and its value equals the sum of val_R(q) over all paths q that exist in R and satisfy val_R(q) >= val_R(p).
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive; root = Node(v, L, R) for some i64 v and trees L, R. -/
  theorem spec_10 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
      (v : Aeneas.Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R) :
      ∃ r : Tree, convert_bst root = ok r ∧
        ∀ (p : List PathStep) (x : Int), valAt R p = some x →
          valAt r (PathStep.R :: p) = some (sumValuesGE R x) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
        (v : Aeneas.Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R), ∃ r : Tree, convert_bst root = ok r ∧
          ∀ (p : List PathStep) (x : Int), valAt R p = some x →
            valAt r (PathStep.R :: p) = some (sumValuesGE R x)) := by
    sorry

  /-- The function returns a result r. Let S = v + (the sum of all node values in R). Let val_L(q) denote the value at path q in the original subtree L. For every path p that exists in L, the corresponding path L/p (the same path inside the left subtree of r) exists in r and its value equals S plus the sum of val_L(q) over all paths q that exist in L and satisfy val_L(q) >= val_L(p).
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive; root = Node(v, L, R) for some i64 v and trees L, R. -/
  theorem spec_11 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
      (v : Aeneas.Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R) :
      ∃ r : Tree, convert_bst root = ok r ∧
        ∀ (p : List PathStep) (x : Int), valAt L p = some x →
          valAt r (PathStep.L :: p) =
            some (v.val + treeSum R + sumValuesGE L x) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000)
        (v : Aeneas.Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R), ∃ r : Tree, convert_bst root = ok r ∧
          ∀ (p : List PathStep) (x : Int), valAt L p = some x →
            valAt r (PathStep.L :: p) =
              some (v.val + treeSum R + sumValuesGE L x)) := by
    sorry

  /-- The function returns a result r. If the node values of root sorted in strictly increasing order are a_1 < a_2 < ... < a_n (with n >= 0), then the multiset of node values of r is exactly the multiset {a_i + a_{i+1} + ... + a_n | 1 <= i <= n}.
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive. -/
  theorem spec_12 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000) :
      ∃ r : Tree, convert_bst root = ok r ∧
        (treeValues r).Perm (suffixSums (sortedValues root)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000), ∃ r : Tree, convert_bst root = ok r ∧
          (treeValues r).Perm (suffixSums (sortedValues root))) := by
    sorry

  /-- Whenever the function returns a result r, for any two paths p and q that exist in root, if x = val_root(p) and y = val_root(q) with x < y, then the same paths p and q exist in r and val_r(p) - val_r(q) equals the sum of all node values z of root such that x <= z < y.
    Preconditions: root is a valid binary search tree: for every node, all values in its left subtree are strictly less than the node's value, all values in its right subtree are strictly greater than the node's value, and both subtrees are valid BSTs; all node values in root are distinct; the number of nodes in root is between 0 and 10000 inclusive; every node value is between -10000 and 10000 inclusive. -/
  theorem spec_13 (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
      (hcount : nodeCount root ≤ 10000)
      (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000) :
      ∀ (r : Tree), convert_bst root = ok r →
        ∀ (p q : List PathStep) (x y : Int),
          valAt root p = some x → valAt root q = some y → x < y →
          ∃ x' y' : Int, valAt r p = some x' ∧ valAt r q = some y' ∧
            x' - y' = sumInRange root x y := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (hbst : IsBst root) (hnd : (treeValues root).Nodup)
        (hcount : nodeCount root ≤ 10000)
        (hbounds : ∀ z ∈ treeValues root, -10000 ≤ z ∧ z ≤ 10000), ∀ (r : Tree), convert_bst root = ok r →
          ∀ (p q : List PathStep) (x y : Int),
            valAt root p = some x → valAt root q = some y → x < y →
            ∃ x' y' : Int, valAt r p = some x' ∧ valAt r q = some y' ∧
              x' - y' = sumInRange root x y) := by
    sorry

  end AegisSpec.ConvertBst
