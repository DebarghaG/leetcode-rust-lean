import Aegis.InorderTraversal.Code.Funs

/-!
# Specifications of `Aegis.InorderTraversal.inorder_traversal`

LeetCode problem `binary-tree-inorder-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.InorderTraversal

namespace AegisSpec.InorderTraversal

def inorderList : Tree → List I64
  | Tree.Null => []
  | Tree.Node v l r => inorderList l ++ [v] ++ inorderList r

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

def allNodesP (p : I64 → Prop) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => p v ∧ allNodesP p l ∧ allNodesP p r

def boundedValues (t : Tree) : Prop :=
  allNodesP (fun v => -100 ≤ v.val ∧ v.val ≤ 100) t

def problemConstraints (t : Tree) : Prop :=
  0 ≤ nodeCount t ∧ nodeCount t ≤ 100 ∧ boundedValues t

def nodeCountConstraint (t : Tree) : Prop :=
  0 ≤ nodeCount t ∧ nodeCount t ≤ 100

def listValueCount (x : Int) (l : List I64) : Nat :=
  l.countP (fun v => v.val == x)

def treeValueCount (x : Int) : Tree → Nat
  | Tree.Null => 0
  | Tree.Node v l r =>
    (if v.val = x then 1 else 0) + treeValueCount x l + treeValueCount x r

def leftSpine : Tree → List I64
  | Tree.Null => []
  | Tree.Node v l _ => v :: leftSpine l

def rightSpine : Tree → List I64
  | Tree.Null => []
  | Tree.Node v _ r => v :: rightSpine r

def leftmostValue? : Tree → Option I64
  | Tree.Null => none
  | Tree.Node v l _ =>
    match leftmostValue? l with
    | none => some v
    | some w => some w

def rightmostValue? : Tree → Option I64
  | Tree.Null => none
  | Tree.Node v _ r =>
    match rightmostValue? r with
    | none => some v
    | some w => some w

def IsSubtreeOf (sub : Tree) : Tree → Prop
  | Tree.Null => sub = Tree.Null
  | Tree.Node v l r => sub = Tree.Node v l r ∨ IsSubtreeOf sub l ∨ IsSubtreeOf sub r

def NoLeftChild : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r => l = Tree.Null ∧ NoLeftChild l ∧ NoLeftChild r

def NoRightChild : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r => r = Tree.Null ∧ NoRightChild l ∧ NoRightChild r

/-- The function returns a result r and the sequence of elements of r equals the inorder sequence of root. Define inorder(t) recursively: inorder(Null) = [] and inorder(Node(v, l, r)) = inorder(l) ++ [v] ++ inorder(r). Then len(r) = len(inorder(root)) and for every i with 0 <= i < len(r), r[i] = (inorder(root))[i].
  Preconditions: The number of nodes in root is between 0 and 100 inclusive, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_1 (root : Tree) (h : problemConstraints root) :
    ∃ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r ∧
        r.val.length = (inorderList root).length ∧
        ∀ i : Nat, i < r.val.length → (r.val[i]!).val = ((inorderList root)[i]!).val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (h : problemConstraints root), ∃ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r ∧
        r.val.length = (inorderList root).length ∧
        ∀ i : Nat, i < r.val.length → (r.val[i]!).val = ((inorderList root)[i]!).val) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of nodes in root, where the number of nodes is defined by nodes(Null) = 0 and nodes(Node(v, l, r)) = 1 + nodes(l) + nodes(r).
  Preconditions: None (the property holds for every tree). -/
theorem spec_2 :
    ∀ (root : Tree) (r : alloc.vec.Vec I64),
      inorder_traversal root = ok r → r.val.length = nodeCount root := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64),
      inorder_traversal root = ok r → r.val.length = nodeCount root) := by
  sorry

/-- Whenever the function returns a result r, for every integer x, the number of occurrences of x in r equals the number of nodes in root whose value is x.
  Preconditions: The number of nodes in root is between 0 and 100 inclusive, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_3 (root : Tree) (h : problemConstraints root) :
    ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∀ x : Int, listValueCount x r.val = treeValueCount x root := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (h : problemConstraints root), ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∀ x : Int, listValueCount x r.val = treeValueCount x root) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), -100 <= r[i] <= 100.
  Preconditions: The number of nodes in root is between 0 and 100 inclusive, and every node value v satisfies -100 <= v <= 100. -/
theorem spec_4 (root : Tree) (h : problemConstraints root) :
    ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          -100 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ 100 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (h : problemConstraints root), ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          -100 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, len(r) > 0, and r[0] equals the value of the leftmost node of root (the node reached by starting at root and repeatedly taking the left child until there is no left child), and r[len(r)-1] equals the value of the rightmost node of root (the node reached by starting at root and repeatedly taking the right child until there is no right child).
  Preconditions: root ≠ Null and the tree satisfies the problem constraints: at most 100 nodes and every node value v with -100 <= v <= 100. -/
theorem spec_5 (root : Tree) (hne : root ≠ Tree.Null) (h : problemConstraints root) :
    ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∃ lv rv : I64,
          leftmostValue? root = some lv ∧ rightmostValue? root = some rv ∧
            0 < r.val.length ∧
            (r.val[0]!).val = lv.val ∧ (r.val[r.val.length - 1]!).val = rv.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (h : problemConstraints root), ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∃ lv rv : I64,
          leftmostValue? root = some lv ∧ rightmostValue? root = some rv ∧
            0 < r.val.length ∧
            (r.val[0]!).val = lv.val ∧ (r.val[r.val.length - 1]!).val = rv.val) := by
  sorry

/-- Whenever the function returns a result r, the sequence of elements of r equals inorder(L) ++ [v] ++ inorder(R), where inorder is the standard inorder sequence (inorder(Null)=[]; inorder(Node(w, a, b))=inorder(a)++[w]++inorder(b)).
  Preconditions: root = Node(v, L, R) for some value v and subtrees L and R; the tree satisfies the problem constraints. -/
theorem spec_6 (root : Tree) (v : I64) (L R : Tree) (hroot : root = Tree.Node v L R)
    (h : problemConstraints root) :
    ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r → r.val = inorderList L ++ [v] ++ inorderList R := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (v : I64) (L R : Tree) (hroot : root = Tree.Node v L R)
    (h : problemConstraints root), ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r → r.val = inorderList L ++ [v] ++ inorderList R) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: The number of nodes in root is between 0 and 100 inclusive. -/
theorem spec_7 (root : Tree) (h : nodeCountConstraint root) :
    ∃ r : alloc.vec.Vec I64, inorder_traversal root = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (h : nodeCountConstraint root), ∃ r : alloc.vec.Vec I64, inorder_traversal root = ok r) := by
  sorry

/-- Whenever the function returns a result r, the elements of r are exactly the values along the unique right-descending path from root to the deepest node, in order from root to leaf. If root = Null, r is empty.
  Preconditions: Every node in root has no left child (i.e., for every node, its left subtree is Null); the tree satisfies the problem constraints. -/
theorem spec_8 (root : Tree) (hleft : NoLeftChild root) (h : problemConstraints root) :
    ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r → r.val = rightSpine root := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (hleft : NoLeftChild root) (h : problemConstraints root), ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r → r.val = rightSpine root) := by
  sorry

/-- Whenever the function returns a result r, the elements of r are exactly the values along the unique left-descending path from root to the deepest node, in order from deepest to root. If root = Null, r is empty.
  Preconditions: Every node in root has no right child (i.e., for every node, its right subtree is Null); the tree satisfies the problem constraints. -/
theorem spec_9 (root : Tree) (hright : NoRightChild root) (h : problemConstraints root) :
    ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r → r.val = (leftSpine root).reverse := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (hright : NoRightChild root) (h : problemConstraints root), ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r → r.val = (leftSpine root).reverse) := by
  sorry

/-- Define inorder(Null) = [] and inorder(Node(w, A, B)) = inorder(A) ++ [w] ++ inorder(B). Whenever the function returns Ok r, for every subtree occurrence Node(w, L, R) of root there exist sequences P and Q such that r = P ++ inorder(L) ++ [w] ++ inorder(R) ++ Q.
  Preconditions: The tree root satisfies the problem constraints: 0 <= nodes(root) <= 100 and every node value v satisfies -100 <= v <= 100. -/
theorem spec_10 (root : Tree) (h : problemConstraints root) :
    ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∀ (w : I64) (L R : Tree),
          IsSubtreeOf (Tree.Node w L R) root →
            ∃ P Q : List I64, r.val = P ++ inorderList L ++ [w] ++ inorderList R ++ Q := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (h : problemConstraints root), ∀ r : alloc.vec.Vec I64,
      inorder_traversal root = ok r →
        ∀ (w : I64) (L R : Tree),
          IsSubtreeOf (Tree.Node w L R) root →
            ∃ P Q : List I64, r.val = P ++ inorderList L ++ [w] ++ inorderList R ++ Q) := by
  sorry

end AegisSpec.InorderTraversal
