import Aegis.BoundaryOfBinaryTree.Code.Funs

/-!
# Specifications of `Aegis.BoundaryOfBinaryTree.boundary_of_binary_tree`

LeetCode problem `boundary-of-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BoundaryOfBinaryTree

  open Aegis.BoundaryOfBinaryTree

  def nodeValue : Tree → ℤ
    | Tree.Null => 0
    | Tree.Node v _ _ => v.val

  def leftChild : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node _ l _ => l

  def rightChild : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node _ _ r => r

  def isNullTree : Tree → Bool
    | Tree.Null => true
    | Tree.Node _ _ _ => false

  def isLeaf : Tree → Prop
    | Tree.Null => False
    | Tree.Node _ l r => l = Tree.Null ∧ r = Tree.Null

  def hasTwoChildren (t : Tree) : Prop :=
    leftChild t ≠ Tree.Null ∧ rightChild t ≠ Tree.Null

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def boundedValues : Tree → ℤ → ℤ → Prop
    | Tree.Null, _, _ => True
    | Tree.Node v l r, lo, hi =>
      lo ≤ v.val ∧ v.val ≤ hi ∧ boundedValues l lo hi ∧ boundedValues r lo hi

  def occurs : Tree → Tree → Prop
    | Tree.Null, _ => False
    | Tree.Node v l r, x => x = Tree.Node v l r ∨ occurs l x ∨ occurs r x

  def values (ns : List Tree) : List ℤ := ns.map nodeValue

  def vecVal (v : alloc.vec.Vec I64) (i : Nat) : ℤ :=
    ((v.val[i]?).map (fun x => x.val)).getD 0

  def vecValues (v : alloc.vec.Vec I64) : List ℤ := v.val.map (fun x => x.val)

  def nodesValAt (ns : List Tree) (i : Nat) : ℤ := ((ns[i]?).map nodeValue).getD 0

  def leftBoundaryN : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r =>
      if isNullTree l && isNullTree r then []
      else Tree.Node v l r :: (match l with
        | Tree.Null => leftBoundaryN r
        | Tree.Node _ _ _ => leftBoundaryN l)

  def rightBoundaryN : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r =>
      if isNullTree l && isNullTree r then []
      else Tree.Node v l r :: (match r with
        | Tree.Null => rightBoundaryN l
        | Tree.Node _ _ _ => rightBoundaryN r)

  def leavesN : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r =>
      if isNullTree l && isNullTree r then [Tree.Node v l r]
      else leavesN l ++ leavesN r

  def nonRootLeaves (root : Tree) : List Tree :=
    match root with
    | Tree.Null => []
    | Tree.Node v l r =>
      if isNullTree l && isNullTree r then [] else leavesN (Tree.Node v l r)

  def precedes (l : List Tree) (a b : Tree) : Prop :=
    ∃ i j, i < l.length ∧ j < l.length ∧ l[i]? = some a ∧ l[j]? = some b ∧ i < j

  /-- Whenever the function returns Ok v, v = [root.val] ++ values(LB) ++ values(L) ++ reverse(values(RB)), where values(...) maps a sequence of nodes to the sequence of their integer values, and LB, L, RB are defined as follows. LB (left boundary): if root.left is Null, LB is empty; otherwise LB is the sequence of non-leaf nodes obtained by starting at root.left and repeatedly moving to the left child if it exists, otherwise to the right child, stopping before the first leaf (a node with no children). L (leaves): the sequence of all leaves (nodes with no children) in the tree except that the root is not considered a leaf even if it has no children, ordered from left to right (for any node, all leaves in its left subtree precede all leaves in its right subtree). RB (right boundary): if root.right is Null, RB is empty; otherwise RB is the sequence of non-leaf nodes obtained by starting at root.right and repeatedly moving to the right child if it exists, otherwise to the left child, stopping before the first leaf.
    Preconditions: root is not Null. The number of nodes in the tree is at least 1 and at most 10^4; every node value is in [-1000, 1000]. -/
  theorem spec_1 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
      (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      vecValues v
        = [nodeValue root] ++ values (leftBoundaryN (leftChild root))
            ++ values (nonRootLeaves root)
            ++ (values (rightBoundaryN (rightChild root))).reverse := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
        (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), vecValues v
          = [nodeValue root] ++ values (leftBoundaryN (leftChild root))
              ++ values (nonRootLeaves root)
              ++ (values (rightBoundaryN (rightChild root))).reverse) := by
    sorry

  /-- The function returns Ok v for some vector v; it never fails (no overflow, no out-of-bounds, no panic).
    Preconditions: root is not Null. The number of nodes in the tree is at least 1 and at most 10^4; every node value is in [-1000, 1000]. -/
  theorem spec_2 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
      (hbound : boundedValues root (-1000) 1000) :
      ∃ v, boundary_of_binary_tree root = ok v := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
        (hbound : boundedValues root (-1000) 1000), ∃ v, boundary_of_binary_tree root = ok v) := by
    sorry

  /-- Whenever the function returns Ok v, len(v) <= N, where N is the number of nodes in the tree rooted at root.
    Preconditions: root is not Null. The number of nodes in the tree is at least 1 and at most 10^4. -/
  theorem spec_3 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      v.val.length ≤ nodeCount root := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), v.val.length ≤ nodeCount root) := by
    sorry

  /-- Whenever the function returns Ok v, for every index i with 0 <= i < len(v), -1000 <= v[i] <= 1000.
    Preconditions: root is not Null. The number of nodes in the tree is at least 1 and at most 10^4; every node value is in [-1000, 1000]. -/
  theorem spec_4 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
      (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      ∀ (i : Nat), i < v.val.length → -1000 ≤ vecVal v i ∧ vecVal v i ≤ 1000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
        (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), ∀ (i : Nat), i < v.val.length → -1000 ≤ vecVal v i ∧ vecVal v i ≤ 1000) := by
    sorry

  /-- Whenever the function returns Ok v, len(v) >= 1 and v[0] = root.val.
    Preconditions: root is not Null. The number of nodes in the tree is at least 1 and at most 10^4; every node value is in [-1000, 1000]. -/
  theorem spec_5 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
      (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      1 ≤ v.val.length ∧ vecVal v 0 = nodeValue root := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize1 : 1 ≤ nodeCount root) (hsize : nodeCount root ≤ 10 ^ 4)
        (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), 1 ≤ v.val.length ∧ vecVal v 0 = nodeValue root) := by
    sorry

  /-- Whenever the function returns Ok v, len(v) >= 2 and v[1] = root.left.val.
    Preconditions: root is not Null, root.left is not Null, and root.left is not a leaf (i.e., root.left has at least one child). The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_6 (root : Tree) (hne : root ≠ Tree.Null)
      (hleft : leftChild root ≠ Tree.Null) (hleft_nl : ¬ isLeaf (leftChild root))
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      2 ≤ v.val.length ∧ vecVal v 1 = nodeValue (leftChild root) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hleft : leftChild root ≠ Tree.Null) (hleft_nl : ¬ isLeaf (leftChild root))
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), 2 ≤ v.val.length ∧ vecVal v 1 = nodeValue (leftChild root)) := by
    sorry

  /-- Whenever the function returns Ok v, len(v) >= 1 and v[len(v)-1] = root.right.val.
    Preconditions: root is not Null, root.right is not Null, and root.right is not a leaf (i.e., root.right has at least one child). The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_7 (root : Tree) (hne : root ≠ Tree.Null)
      (hright : rightChild root ≠ Tree.Null) (hright_nl : ¬ isLeaf (rightChild root))
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      1 ≤ v.val.length ∧ vecVal v (v.val.length - 1) = nodeValue (rightChild root) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hright : rightChild root ≠ Tree.Null) (hright_nl : ¬ isLeaf (rightChild root))
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), 1 ≤ v.val.length ∧ vecVal v (v.val.length - 1) = nodeValue (rightChild root)) := by
    sorry

  /-- Whenever the function returns Ok v, len(v) = 1 + len(LB) + len(L) + len(RB), where LB is the left boundary (non-leaf nodes from root.left preferring left then right until before a leaf), L is the leaves list (all nodes with no children except the root, in left-to-right order), and RB is the right boundary (non-leaf nodes from root.right preferring right then left until before a leaf).
    Preconditions: root is not Null. The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_8 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      v.val.length
        = 1 + (leftBoundaryN (leftChild root)).length + (nonRootLeaves root).length
            + (rightBoundaryN (rightChild root)).length := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), v.val.length
          = 1 + (leftBoundaryN (leftChild root)).length + (nonRootLeaves root).length
              + (rightBoundaryN (rightChild root)).length) := by
    sorry

  /-- Whenever the function returns Ok v, let L be the sequence of all non-root leaves in left-to-right order (as defined in spec_1). Then the leaves segment of v (the contiguous subvector of v consisting of the leaf values) has length len(L) and equals values(L); in particular, every non-root leaf is represented by a distinct occurrence in that segment.
    Preconditions: root is not Null. The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_9 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      (((vecValues v).drop (1 + (leftBoundaryN (leftChild root)).length)).take
            (nonRootLeaves root).length).length
          = (nonRootLeaves root).length
        ∧ ((vecValues v).drop
              (1 + (leftBoundaryN (leftChild root)).length)).take
            (nonRootLeaves root).length = values (nonRootLeaves root) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), (((vecValues v).drop (1 + (leftBoundaryN (leftChild root)).length)).take
              (nonRootLeaves root).length).length
            = (nonRootLeaves root).length
          ∧ ((vecValues v).drop
                (1 + (leftBoundaryN (leftChild root)).length)).take
              (nonRootLeaves root).length = values (nonRootLeaves root)) := by
    sorry

  /-- Whenever the function returns Ok v, the last len(RB) elements of v are exactly the values of RB in reverse order, where RB is defined as: starting at root.right, repeatedly move to the right child if it exists, otherwise to the left child, appending each non-leaf node visited, and stop before the first leaf.
    Preconditions: root is not Null, root.right is not Null, and root.right is not a leaf (i.e., root.right has at least one child). The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_10 (root : Tree) (hne : root ≠ Tree.Null)
      (hright : rightChild root ≠ Tree.Null) (hright_nl : ¬ isLeaf (rightChild root))
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v) :
      (vecValues v).drop
          (v.val.length - (rightBoundaryN (rightChild root)).length)
        = (values (rightBoundaryN (rightChild root))).reverse := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hright : rightChild root ≠ Tree.Null) (hright_nl : ¬ isLeaf (rightChild root))
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (v : alloc.vec.Vec I64) (hv : boundary_of_binary_tree root = ok v), (vecValues v).drop
            (v.val.length - (rightBoundaryN (rightChild root)).length)
          = (values (rightBoundaryN (rightChild root))).reverse) := by
    sorry

  /-- Whenever the function returns Ok out, len(out) >= 2 and out[1] = l.
    Preconditions: root = Node(v, Node(l, Null, Null), R) for some integers v, l with -1000 <= v, l <= 1000 and some tree R (possibly Null). The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_11 (root : Tree) (v : I64) (l : I64) (R : Tree)
      (hroot : root = Tree.Node v (Tree.Node l Tree.Null Tree.Null) R)
      (hvlo : -1000 ≤ v.val) (hvhi : v.val ≤ 1000)
      (hllo : -1000 ≤ l.val) (hlhi : l.val ≤ 1000)
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (out : alloc.vec.Vec I64) (hout : boundary_of_binary_tree root = ok out) :
      2 ≤ out.val.length ∧ vecVal out 1 = l.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (v : I64) (l : I64) (R : Tree)
        (hroot : root = Tree.Node v (Tree.Node l Tree.Null Tree.Null) R)
        (hvlo : -1000 ≤ v.val) (hvhi : v.val ≤ 1000)
        (hllo : -1000 ≤ l.val) (hlhi : l.val ≤ 1000)
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (out : alloc.vec.Vec I64) (hout : boundary_of_binary_tree root = ok out), 2 ≤ out.val.length ∧ vecVal out 1 = l.val) := by
    sorry

  /-- Whenever the function returns Ok out, len(out) >= 1 and out[len(out)-1] = r.
    Preconditions: root = Node(v, L, Node(r, Null, Null)) for some integers v, r with -1000 <= v, r <= 1000 and some tree L (possibly Null). The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_12 (root : Tree) (v : I64) (L : Tree) (r : I64)
      (hroot : root = Tree.Node v L (Tree.Node r Tree.Null Tree.Null))
      (hvlo : -1000 ≤ v.val) (hvhi : v.val ≤ 1000)
      (hrlo : -1000 ≤ r.val) (hrhi : r.val ≤ 1000)
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (out : alloc.vec.Vec I64) (hout : boundary_of_binary_tree root = ok out) :
      1 ≤ out.val.length ∧ vecVal out (out.val.length - 1) = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (v : I64) (L : Tree) (r : I64)
        (hroot : root = Tree.Node v L (Tree.Node r Tree.Null Tree.Null))
        (hvlo : -1000 ≤ v.val) (hvhi : v.val ≤ 1000)
        (hrlo : -1000 ≤ r.val) (hrhi : r.val ≤ 1000)
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (out : alloc.vec.Vec I64) (hout : boundary_of_binary_tree root = ok out), 1 ≤ out.val.length ∧ vecVal out (out.val.length - 1) = r.val) := by
    sorry

  /-- Whenever the function returns Ok out, let LB be the left boundary as defined in spec_1. Then the segment of out immediately after the root, out[1 .. 1+len(LB)), is exactly values(LB) in order; i.e., for every 0 <= i < len(LB), out[1+i] = (the i-th node of LB).val.
    Preconditions: root is not Null. The number of nodes is at most 10^4 and all node values are in [-1000, 1000]. -/
  theorem spec_13 (root : Tree) (hne : root ≠ Tree.Null)
      (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
      (out : alloc.vec.Vec I64) (hout : boundary_of_binary_tree root = ok out) :
      ∀ (i : Nat), i < (leftBoundaryN (leftChild root)).length →
        vecVal out (1 + i) = nodesValAt (leftBoundaryN (leftChild root)) i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null)
        (hsize : nodeCount root ≤ 10 ^ 4) (hbound : boundedValues root (-1000) 1000)
        (out : alloc.vec.Vec I64) (hout : boundary_of_binary_tree root = ok out), ∀ (i : Nat), i < (leftBoundaryN (leftChild root)).length →
          vecVal out (1 + i) = nodesValAt (leftBoundaryN (leftChild root)) i) := by
    sorry

  end AegisSpec.BoundaryOfBinaryTree
