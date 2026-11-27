import Aegis.IsSubPath.Code.Funs

/-!
# Specifications of `Aegis.IsSubPath.is_sub_path`

LeetCode problem `linked-list-in-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace Aegis.IsSubPath

  def List.val : List → _root_.List ℤ
    | .Nil => []
    | .Cons v rest => v.val :: rest.val

  namespace Tree

  def numNodes : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + numNodes l + numNodes r

  def nodeVals : Tree → _root_.List ℤ
    | .Null => []
    | .Node v l r => v.val :: (nodeVals l ++ nodeVals r)

  def spineVals : Tree → _root_.List ℤ
    | .Null => []
    | .Node v l r => v.val :: (spineVals l ++ spineVals r)

  def mirror : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirror r) (mirror l)

  def IsPathShaped : Tree → Prop
    | .Null => True
    | .Node _ l r => (l = .Null ∨ r = .Null) ∧ IsPathShaped l ∧ IsPathShaped r

  def IsSubtreeOf : Tree → Tree → Prop
    | _, .Null => False
    | t, .Node v l r => t = .Node v l r ∨ IsSubtreeOf t l ∨ IsSubtreeOf t r

  def PathMatch : Tree → List → Prop
    | .Null, l => l = .Nil
    | (.Node v l' r'), l =>
      match l with
      | .Nil => True
      | .Cons w rest => w.val = v.val ∧ (PathMatch l' rest ∨ PathMatch r' rest)

  end Tree

  end Aegis.IsSubPath

  namespace AegisSpec.IsSubPath

  open Aegis.IsSubPath (Tree is_sub_path)

  def countOcc (v : ℤ) : List ℤ → Nat
    | [] => 0
    | x :: xs => (if x = v then 1 else 0) + countOcc v xs

  def IsContiguousSubarray (sub sup : List ℤ) : Prop :=
    ∃ pre post : List ℤ, sup = pre ++ sub ++ post

  /-- The function returns a result `r` (a boolean). Let `k` be the number of nodes in `head`, and let `(v_0, v_1, ..., v_{k-1})` be the values of the nodes in `head` from head to tail (so `head = Cons(v_0, Cons(v_1, ... Cons(v_{k-1}, Nil)...))`). Then `r = true` if and only if there exists a sequence of nodes `(t_0, t_1, ..., t_{k-1})` in `root` such that: (1) `t_0` is a node in `root` (i.e., a non-null subtree reachable from `root`); (2) for every `i` with `0 <= i < k-1`, `t_{i+1}` is either the left child or the right child of `t_i`; (3) all `t_i` are non-null; and (4) the value of `t_i` equals `v_i` for every `i` with `0 <= i < k`. In other words, the sequence of values along a downward path in `root` equals the sequence of values in `head`.
    Preconditions: The list `head` is not `Nil` and has between 1 and 100 nodes inclusive. The tree `root` is not `Null` and has between 1 and 2500 nodes inclusive. Every node value in `head` and `root` is an integer between 1 and 100 inclusive. -/
  theorem spec_1 (head : Aegis.IsSubPath.List) (root : Tree)
      (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
      (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
      (hroot_ne : root ≠ Tree.Null)
      (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
      (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
      (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100) :
      ∃ r : Bool, is_sub_path head root = ok r ∧
        (r = true ↔ ∃ t : Tree, t.IsSubtreeOf root ∧ t.PathMatch head) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : Aegis.IsSubPath.List) (root : Tree)
        (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
        (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
        (hroot_ne : root ≠ Tree.Null)
        (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
        (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
        (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100), ∃ r : Bool, is_sub_path head root = ok r ∧
          (r = true ↔ ∃ t : Tree, t.IsSubtreeOf root ∧ t.PathMatch head)) := by
    sorry

  /-- The function returns a result `r` (i.e., there exists a boolean `r` such that `is_sub_path(head, root) = Result.ok r`). In particular, the function does not fail, panic, or overflow.
    Preconditions: Same as spec_1: `head` is a non-empty list with at most 100 nodes, `root` is a non-empty tree with at most 2500 nodes, and all node values are between 1 and 100 inclusive. -/
  theorem spec_2 (head : Aegis.IsSubPath.List) (root : Tree)
      (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
      (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
      (hroot_ne : root ≠ Tree.Null)
      (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
      (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
      (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100) :
      ∃ r : Bool, is_sub_path head root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : Aegis.IsSubPath.List) (root : Tree)
        (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
        (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
        (hroot_ne : root ≠ Tree.Null)
        (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
        (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
        (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100), ∃ r : Bool, is_sub_path head root = ok r) := by
    sorry

  /-- If `is_sub_path(head, root) = true`, then `is_sub_path(head', root) = true`.
    Preconditions: `head` and `head'` are non-empty lists such that `head'` is a prefix of `head` (i.e., there exists a list `rest` with `head = head' ++ rest`). Both `head` and `head'` have at most 100 nodes, `root` is a non-empty tree with at most 2500 nodes, and all node values are between 1 and 100 inclusive. -/
  theorem spec_3 (head head' : Aegis.IsSubPath.List) (root : Tree)
      (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
      (hhead'_ne : head' ≠ Aegis.IsSubPath.List.Nil)
      (hprefix : ∃ rest : List ℤ, head.val = head'.val ++ rest)
      (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
      (hhead'_nodes : 1 ≤ head'.val.length ∧ head'.val.length ≤ 100)
      (hroot_ne : root ≠ Tree.Null)
      (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
      (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
      (hhead'_vals : ∀ v ∈ head'.val, 1 ≤ v ∧ v ≤ 100)
      (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100) :
      is_sub_path head root = ok true → is_sub_path head' root = ok true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head head' : Aegis.IsSubPath.List) (root : Tree)
        (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
        (hhead'_ne : head' ≠ Aegis.IsSubPath.List.Nil)
        (hprefix : ∃ rest : List ℤ, head.val = head'.val ++ rest)
        (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
        (hhead'_nodes : 1 ≤ head'.val.length ∧ head'.val.length ≤ 100)
        (hroot_ne : root ≠ Tree.Null)
        (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
        (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
        (hhead'_vals : ∀ v ∈ head'.val, 1 ≤ v ∧ v ≤ 100)
        (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100), is_sub_path head root = ok true → is_sub_path head' root = ok true) := by
    sorry

  /-- If `is_sub_path(head, root) = true`, then `is_sub_path(head, root') = true`.
    Preconditions: `root` and `root'` are non-empty trees such that `root` is a subtree of `root'` (i.e., there exists a node in `root'` whose subtree is exactly `root`). Both trees have at most 2500 nodes, `head` is a non-empty list with at most 100 nodes, and all node values are between 1 and 100 inclusive. -/
  theorem spec_4 (head : Aegis.IsSubPath.List) (root root' : Tree)
      (hroot_ne : root ≠ Tree.Null)
      (hroot'_ne : root' ≠ Tree.Null)
      (hsub : root.IsSubtreeOf root')
      (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
      (hroot'_nodes : 1 ≤ root'.numNodes ∧ root'.numNodes ≤ 2500)
      (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
      (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
      (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
      (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100)
      (hroot'_vals : ∀ v ∈ root'.nodeVals, 1 ≤ v ∧ v ≤ 100) :
      is_sub_path head root = ok true → is_sub_path head root' = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : Aegis.IsSubPath.List) (root root' : Tree)
        (hroot_ne : root ≠ Tree.Null)
        (hroot'_ne : root' ≠ Tree.Null)
        (hsub : root.IsSubtreeOf root')
        (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
        (hroot'_nodes : 1 ≤ root'.numNodes ∧ root'.numNodes ≤ 2500)
        (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
        (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
        (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
        (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100)
        (hroot'_vals : ∀ v ∈ root'.nodeVals, 1 ≤ v ∧ v ≤ 100), is_sub_path head root = ok true → is_sub_path head root' = ok true) := by
    sorry

  /-- Let `mirror(root)` be the tree obtained from `root` by recursively swapping the left and right children of every node: `mirror(Null) = Null` and `mirror(Node(v, l, r)) = Node(v, mirror(r), mirror(l))`. Then `is_sub_path(head, root) = is_sub_path(head, mirror(root))`.
    Preconditions: Same as spec_1. -/
  theorem spec_5 (head : Aegis.IsSubPath.List) (root : Tree)
      (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
      (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
      (hroot_ne : root ≠ Tree.Null)
      (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
      (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
      (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100) :
      is_sub_path head root = is_sub_path head root.mirror := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : Aegis.IsSubPath.List) (root : Tree)
        (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
        (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
        (hroot_ne : root ≠ Tree.Null)
        (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
        (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
        (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100), is_sub_path head root = is_sub_path head root.mirror) := by
    sorry

  /-- If `is_sub_path(head, root) = true`, then for every integer `v`, the number of occurrences of `v` in `head` is at most the number of nodes in `root` whose value is `v`. (Here 'occurrences in `head`' means the number of nodes in the linked list with value `v`.)
    Preconditions: Same as spec_1. -/
  theorem spec_6 (head : Aegis.IsSubPath.List) (root : Tree)
      (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
      (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
      (hroot_ne : root ≠ Tree.Null)
      (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
      (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
      (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100) :
      is_sub_path head root = ok true →
        ∀ v : ℤ, countOcc v head.val ≤ countOcc v root.nodeVals := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : Aegis.IsSubPath.List) (root : Tree)
        (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
        (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
        (hroot_ne : root ≠ Tree.Null)
        (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
        (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
        (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100), is_sub_path head root = ok true →
          ∀ v : ℤ, countOcc v head.val ≤ countOcc v root.nodeVals) := by
    sorry

  /-- Let `(w_0, w_1, ..., w_{n-1})` be the sequence of node values along the unique root-to-leaf path of `root` (from the root down to the only leaf). Then `is_sub_path(head, root) = true` if and only if the sequence of values of `head` is a contiguous subarray of `(w_0, ..., w_{n-1})`, i.e., there exist indices `i` and `j` with `0 <= i <= j < n` such that `j - i + 1 = len(head)` and for every `k` with `0 <= k < len(head)`, the value of the `(i+k)`-th node on the path equals the `k`-th value of `head`.
    Preconditions: `root` is a tree such that every node has at most one child (i.e., `root` is a path-shaped tree). `head` is a non-empty list with at most 100 nodes, `root` is non-empty with at most 2500 nodes, and all node values are between 1 and 100 inclusive. -/
  theorem spec_7 (head : Aegis.IsSubPath.List) (root : Tree)
      (hpath : root.IsPathShaped)
      (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
      (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
      (hroot_ne : root ≠ Tree.Null)
      (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
      (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
      (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100) :
      is_sub_path head root = ok true ↔ IsContiguousSubarray head.val root.spineVals := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : Aegis.IsSubPath.List) (root : Tree)
        (hpath : root.IsPathShaped)
        (hhead_ne : head ≠ Aegis.IsSubPath.List.Nil)
        (hhead_nodes : 1 ≤ head.val.length ∧ head.val.length ≤ 100)
        (hroot_ne : root ≠ Tree.Null)
        (hroot_nodes : 1 ≤ root.numNodes ∧ root.numNodes ≤ 2500)
        (hhead_vals : ∀ v ∈ head.val, 1 ≤ v ∧ v ≤ 100)
        (hroot_vals : ∀ v ∈ root.nodeVals, 1 ≤ v ∧ v ≤ 100), is_sub_path head root = ok true ↔ IsContiguousSubarray head.val root.spineVals) := by
    sorry

  end AegisSpec.IsSubPath
