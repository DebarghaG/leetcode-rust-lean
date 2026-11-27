import Aegis.DeepestLeavesSum.Code.Funs

/-!
# Specifications of `Aegis.DeepestLeavesSum.deepest_leaves_sum`

LeetCode problem `deepest-leaves-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.DeepestLeavesSum

  namespace AegisSpec.DeepestLeavesSum

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def nodeValues : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (nodeValues l ++ nodeValues r)

  def totalValueSum (t : Tree) : Int := (nodeValues t).sum

  def leavesFromDepth : Nat → Tree → List (Nat × Int)
    | _, Tree.Null => []
    | d, Tree.Node v Tree.Null Tree.Null => [(d, v.val)]
    | d, Tree.Node _ l r => leavesFromDepth (d + 1) l ++ leavesFromDepth (d + 1) r

  def leaves (t : Tree) : List (Nat × Int) := leavesFromDepth 0 t

  def maxLeafDepth (t : Tree) : Nat :=
    (leaves t).foldr (fun p acc => max p.1 acc) 0

  def leafValuesAtDepth (t : Tree) (d : Nat) : List Int :=
    ((leaves t).filter (fun p => p.1 = d)).map (fun p => p.2)

  def leafSumAtDepth (t : Tree) (d : Nat) : Int := (leafValuesAtDepth t d).sum

  def leafCountAtDepth (t : Tree) (d : Nat) : Nat := (leafValuesAtDepth t d).length

  def deepestLeafSum (t : Tree) : Int := leafSumAtDepth t (maxLeafDepth t)

  def deepestLeafCount (t : Tree) : Nat := leafCountAtDepth t (maxLeafDepth t)

  def IsLeafAtDepth (d : Nat) (v : Int) (t : Tree) : Prop := (d, v) ∈ leaves t

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  def SameShape : Tree → Tree → Prop
    | Tree.Null, Tree.Null => True
    | Tree.Node _ l r, Tree.Node _ l' r' => SameShape l l' ∧ SameShape r r'
    | _, _ => False

  def AgreeFromDepth : Nat → Tree → Tree → Prop
    | _, Tree.Null, Tree.Null => True
    | 0, Tree.Node v l r, Tree.Node v' l' r' =>
        v = v' ∧ AgreeFromDepth 0 l l' ∧ AgreeFromDepth 0 r r'
    | d + 1, Tree.Node _ l r, Tree.Node _ l' r' =>
        AgreeFromDepth d l l' ∧ AgreeFromDepth d r r'
    | _, _, _ => False

  def ValuesLe : Tree → Tree → Prop
    | Tree.Null, Tree.Null => True
    | Tree.Node v l r, Tree.Node v' l' r' => v'.val ≤ v.val ∧ ValuesLe l l' ∧ ValuesLe r r'
    | _, _ => False

  def PerfectAtDepth : Nat → Tree → Prop
    | 0, Tree.Null => True
    | 0, Tree.Node _ _ _ => False
    | _ + 1, Tree.Null => False
    | d + 1, Tree.Node _ l r => PerfectAtDepth d l ∧ PerfectAtDepth d r

  def RootPre (root : Tree) : Prop :=
    root ≠ Tree.Null ∧ 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000 ∧
      (∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100)

  /-- The function returns a result r, and r equals the sum of v over all nodes Node(v, Null, Null) in root whose depth equals D, where D is the maximum depth among all leaf nodes of root (a leaf is a node Node(v, Null, Null); the root has depth 0 and each child has depth one greater than its parent).
    Preconditions: root is not Null; the number of Node constructors in root is between 1 and 10000; every Node value v satisfies 1 <= v <= 100. -/
  theorem spec_1 (root : Tree) (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100) :
      ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧
        r.val = deepestLeafSum root := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100), ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧
          r.val = deepestLeafSum root) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every root satisfying the preconditions.
    Preconditions: root is not Null; the number of Node constructors in root is between 1 and 10000; every Node value v satisfies 1 <= v <= 100. -/
  theorem spec_2 (root : Tree) (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100) :
      ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100), ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r) := by
    sorry

  /-- Whenever the function returns a result r, m <= r <= 100 * m, where m is the number of leaves of root at depth D, and D is the maximum depth among all leaves of root.
    Preconditions: root is not Null; the number of Node constructors in root is between 1 and 10000; every Node value v satisfies 1 <= v <= 100. -/
  theorem spec_3 (root : Tree) (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        (deepestLeafCount root : Int) ≤ r.val ∧
          r.val ≤ 100 * (deepestLeafCount root : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          (deepestLeafCount root : Int) ≤ r.val ∧
            r.val ≤ 100 * (deepestLeafCount root : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= S, where S is the sum of v over all nodes Node(v, _, _) in root.
    Preconditions: root is not Null; the number of Node constructors in root is between 1 and 10000; every Node value v satisfies 1 <= v <= 100. -/
  theorem spec_4 (root : Tree) (hne : root ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        r.val ≤ totalValueSum root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          r.val ≤ totalValueSum root) := by
    sorry

  /-- The function returns a result r and r = v.
    Preconditions: root = Node(v, Null, Null) with 1 <= v <= 100. -/
  theorem spec_5 (root : Tree) (v : Std.I64)
      (hroot : root = Tree.Node v Tree.Null Tree.Null)
      (hv : 1 ≤ v.val ∧ v.val ≤ 100) :
      ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧ r.val = v.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (v : Std.I64)
        (hroot : root = Tree.Node v Tree.Null Tree.Null)
        (hv : 1 ≤ v.val ∧ v.val ≤ 100), ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧ r.val = v.val) := by
    sorry

  /-- The function returns a result r and r = a.
    Preconditions: root is Node(v, Node(a, Null, Null), Null) or Node(v, Null, Node(a, Null, Null)), with 1 <= v <= 100 and 1 <= a <= 100. -/
  theorem spec_6 (root : Tree) (v a : Std.I64)
      (hroot : root = Tree.Node v (Tree.Node a Tree.Null Tree.Null) Tree.Null ∨
        root = Tree.Node v Tree.Null (Tree.Node a Tree.Null Tree.Null))
      (hv : 1 ≤ v.val ∧ v.val ≤ 100) (ha : 1 ≤ a.val ∧ a.val ≤ 100) :
      ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧ r.val = a.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (v a : Std.I64)
        (hroot : root = Tree.Node v (Tree.Node a Tree.Null Tree.Null) Tree.Null ∨
          root = Tree.Node v Tree.Null (Tree.Node a Tree.Null Tree.Null))
        (hv : 1 ≤ v.val ∧ v.val ≤ 100) (ha : 1 ≤ a.val ∧ a.val ≤ 100), ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧ r.val = a.val) := by
    sorry

  /-- The function returns a result r and r = a + b.
    Preconditions: root = Node(v, Node(a, Null, Null), Node(b, Null, Null)) with 1 <= v <= 100, 1 <= a <= 100, and 1 <= b <= 100. -/
  theorem spec_7 (root : Tree) (v a b : Std.I64)
      (hroot : root =
        Tree.Node v (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null))
      (hv : 1 ≤ v.val ∧ v.val ≤ 100) (ha : 1 ≤ a.val ∧ a.val ≤ 100)
      (hb : 1 ≤ b.val ∧ b.val ≤ 100) :
      ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧
        r.val = a.val + b.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (v a b : Std.I64)
        (hroot : root =
          Tree.Node v (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null))
        (hv : 1 ≤ v.val ∧ v.val ≤ 100) (ha : 1 ≤ a.val ∧ a.val ≤ 100)
        (hb : 1 ≤ b.val ∧ b.val ≤ 100), ∃ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r ∧
          r.val = a.val + b.val) := by
    sorry

  /-- Whenever the function returns a result r, r equals the sum of v over all nodes Node(v, _, _) in root that are at depth h.
    Preconditions: root is not Null and is a perfect binary tree of height h with h >= 2: every internal node has exactly two non-null children, and every leaf is at depth h. Every Node value is in [1,100], and the number of Node constructors is at most 10000. -/
  theorem spec_8 (root : Tree) (h : Nat) (hperfect : PerfectAtDepth h root) (hh : 2 ≤ h)
      (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100) (hcount : nodeCount root ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        r.val = leafSumAtDepth root h := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (h : Nat) (hperfect : PerfectAtDepth h root) (hh : 2 ≤ h)
        (hvals : ∀ v ∈ nodeValues root, 1 ≤ v ∧ v ≤ 100) (hcount : nodeCount root ≤ 10000), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          r.val = leafSumAtDepth root h) := by
    sorry

  /-- Whenever the function returns a result r, r equals the sum of values x over all leaves Node(x, Null, Null) in left whose depth within left equals D_left.
    Preconditions: root = Node(v, left, right) with left and right both not Null; every Node value in root is in [1,100]; the number of Node constructors in root is at most 10000; let D_left be the maximum depth of a leaf in left when the root of left has depth 0, and let D_right be the maximum depth of a leaf in right when the root of right has depth 0; assume D_left > D_right. -/
  theorem spec_9 (root left right : Tree) (v : Std.I64)
      (hroot : root = Tree.Node v left right)
      (hleft : left ≠ Tree.Null) (hright : right ≠ Tree.Null)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000)
      (hD : maxLeafDepth right < maxLeafDepth left) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        r.val = leafSumAtDepth left (maxLeafDepth left) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root left right : Tree) (v : Std.I64)
        (hroot : root = Tree.Node v left right)
        (hleft : left ≠ Tree.Null) (hright : right ≠ Tree.Null)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000)
        (hD : maxLeafDepth right < maxLeafDepth left), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          r.val = leafSumAtDepth left (maxLeafDepth left)) := by
    sorry

  /-- Whenever the function returns a result r, r equals (the sum of values x over all leaves Node(x, Null, Null) in left whose depth within left equals D_left) + (the sum of values y over all leaves Node(y, Null, Null) in right whose depth within right equals D_right).
    Preconditions: root = Node(v, left, right) with left and right both not Null; every Node value in root is in [1,100]; the number of Node constructors in root is at most 10000; let D_left be the maximum depth of a leaf in left when the root of left has depth 0, and let D_right be the maximum depth of a leaf in right when the root of right has depth 0; assume D_left = D_right and D_left >= 1. -/
  theorem spec_10 (root left right : Tree) (v : Std.I64)
      (hroot : root = Tree.Node v left right)
      (hleft : left ≠ Tree.Null) (hright : right ≠ Tree.Null)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000)
      (hD : maxLeafDepth left = maxLeafDepth right) (hD1 : 1 ≤ maxLeafDepth left) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        r.val = leafSumAtDepth left (maxLeafDepth left) +
          leafSumAtDepth right (maxLeafDepth right) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root left right : Tree) (v : Std.I64)
        (hroot : root = Tree.Node v left right)
        (hleft : left ≠ Tree.Null) (hright : right ≠ Tree.Null)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000)
        (hD : maxLeafDepth left = maxLeafDepth right) (hD1 : 1 ≤ maxLeafDepth left), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          r.val = leafSumAtDepth left (maxLeafDepth left) +
            leafSumAtDepth right (maxLeafDepth right)) := by
    sorry

  /-- Whenever the function returns r on root and r' on mirror(root), r = r'.
    Preconditions: root is not Null; every Node value in root is in [1,100]; the number of Node constructors in root is at most 10000; let mirror(root) be the tree obtained from root by recursively swapping the left and right children at every Node. -/
  theorem spec_11 (root : Tree) (hne : root ≠ Tree.Null)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000) :
      ∀ (r r' : Std.I64), Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        Aegis.DeepestLeavesSum.deepest_leaves_sum (mirror root) = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000), ∀ (r r' : Std.I64), Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          Aegis.DeepestLeavesSum.deepest_leaves_sum (mirror root) = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on root and r' on root', r = r'.
    Preconditions: root is not Null; every Node value in root is in [1,100]; the number of Node constructors in root is at most 10000; let D be the maximum depth of a leaf in root; let root' be any tree obtained from root by changing the values of zero or more nodes whose depth is less than D, keeping the same shape and keeping every value in [1,100]. -/
  theorem spec_12 (root root' : Tree) (hne : root ≠ Tree.Null)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000)
      (hagree : AgreeFromDepth (maxLeafDepth root) root root')
      (hvals' : ∀ x ∈ nodeValues root', 1 ≤ x ∧ x ≤ 100) :
      ∀ (r r' : Std.I64), Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        Aegis.DeepestLeavesSum.deepest_leaves_sum root' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root root' : Tree) (hne : root ≠ Tree.Null)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000)
        (hagree : AgreeFromDepth (maxLeafDepth root) root root')
        (hvals' : ∀ x ∈ nodeValues root', 1 ≤ x ∧ x ≤ 100), ∀ (r r' : Std.I64), Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          Aegis.DeepestLeavesSum.deepest_leaves_sum root' = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r = c * m.
    Preconditions: root is not Null; every Node value in root equals c for some integer c with 1 <= c <= 100; root has at least 4 Node constructors and at most 10000; let m be the number of leaves of root at the maximum leaf depth D. -/
  theorem spec_13 (root : Tree) (c : Int) (hne : root ≠ Tree.Null)
      (hval : ∀ x ∈ nodeValues root, x = c) (hc : 1 ≤ c ∧ c ≤ 100)
      (hcount : 4 ≤ nodeCount root ∧ nodeCount root ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        r.val = c * (deepestLeafCount root : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (c : Int) (hne : root ≠ Tree.Null)
        (hval : ∀ x ∈ nodeValues root, x = c) (hc : 1 ≤ c ∧ c ≤ 100)
        (hcount : 4 ≤ nodeCount root ∧ nodeCount root ≤ 10000), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          r.val = c * (deepestLeafCount root : Int)) := by
    sorry

  /-- Whenever the function returns r on root and r' on root', r' <= r.
    Preconditions: root and root' are not Null, have the same shape, and each has between 1 and 10000 Node constructors; every node value in both trees is in [1,100]; for every corresponding pair of nodes Node(v, _, _) in root and Node(v', _, _) in root', v' <= v. -/
  theorem spec_14 (root root' : Tree) (hne : root ≠ Tree.Null) (hne' : root' ≠ Tree.Null)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hcount' : 1 ≤ nodeCount root' ∧ nodeCount root' ≤ 10000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100)
      (hvals' : ∀ x ∈ nodeValues root', 1 ≤ x ∧ x ≤ 100)
      (hshape : SameShape root root') (hle : ValuesLe root root') :
      ∀ (r r' : Std.I64), Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        Aegis.DeepestLeavesSum.deepest_leaves_sum root' = ok r' → r'.val ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root root' : Tree) (hne : root ≠ Tree.Null) (hne' : root' ≠ Tree.Null)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hcount' : 1 ≤ nodeCount root' ∧ nodeCount root' ≤ 10000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100)
        (hvals' : ∀ x ∈ nodeValues root', 1 ≤ x ∧ x ≤ 100)
        (hshape : SameShape root root') (hle : ValuesLe root root'), ∀ (r r' : Std.I64), Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          Aegis.DeepestLeavesSum.deepest_leaves_sum root' = ok r' → r'.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every leaf Node(v, Null, Null) in root at depth D, v <= r.
    Preconditions: root is not Null; every Node value in root is in [1,100]; the number of Node constructors in root is at most 10000; let D be the maximum depth of a leaf in root. -/
  theorem spec_15 (root : Tree) (hne : root ≠ Tree.Null)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        ∀ v : Int, IsLeafAtDepth (maxLeafDepth root) v root → v ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          ∀ v : Int, IsLeafAtDepth (maxLeafDepth root) v root → v ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r equals the sum of values x over all leaves Node(x, Null, Null) in child whose depth within child equals D_child.
    Preconditions: root is Node(v, child, Null) or Node(v, Null, child) with child not Null; every Node value in root is in [1,100]; the number of Node constructors in root is at most 10000; let D_child be the maximum depth of a leaf in child when the root of child has depth 0. -/
  theorem spec_16 (root child : Tree) (v : Std.I64)
      (hroot : root = Tree.Node v child Tree.Null ∨ root = Tree.Node v Tree.Null child)
      (hchild : child ≠ Tree.Null)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000) :
      ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
        r.val = leafSumAtDepth child (maxLeafDepth child) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (root child : Tree) (v : Std.I64)
        (hroot : root = Tree.Node v child Tree.Null ∨ root = Tree.Node v Tree.Null child)
        (hchild : child ≠ Tree.Null)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 100) (hcount : nodeCount root ≤ 10000), ∀ r : Std.I64, Aegis.DeepestLeavesSum.deepest_leaves_sum root = ok r →
          r.val = leafSumAtDepth child (maxLeafDepth child)) := by
    sorry

  end AegisSpec.DeepestLeavesSum
