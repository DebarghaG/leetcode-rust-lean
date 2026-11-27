import Aegis.PreorderTraversal.Code.Funs

/-!
# Specifications of `Aegis.PreorderTraversal.preorder_traversal`

LeetCode problem `binary-tree-preorder-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PreorderTraversal

  open Aegis.PreorderTraversal

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ left right => nodeCount left + nodeCount right + 1

  def IsFiniteTree (_root : Tree) : Prop := True

  def valuesBounded : Tree → Prop
    | Tree.Null => True
    | Tree.Node v left right =>
      (-100 : Int) ≤ v.val ∧ v.val ≤ 100 ∧ valuesBounded left ∧ valuesBounded right

  def preorderVals : Tree → List Int
    | Tree.Null => []
    | Tree.Node v left right => v.val :: (preorderVals left ++ preorderVals right)

  def preorderNth (root : Tree) (i : Nat) : Int := (preorderVals root).getD i 0

  def listValueCount (x : Int) (l : List Aeneas.Std.I64) : Nat :=
    (l.filter (fun v => v.val = x)).length

  def treeValueCount (x : Int) : Tree → Nat
    | Tree.Null => 0
    | Tree.Node v left right =>
      (if v.val = x then 1 else 0) + treeValueCount x left + treeValueCount x right

  /-- Whenever `preorder_traversal(root)` returns `Ok(r)`, the vector r is exactly the preorder traversal of root. Define P(Tree.Null) = [] and P(Tree.Node(v,L,R)) = [v] concatenated with P(L) concatenated with P(R). Then len(r) = n and for every index i with 0 <= i < len(r), r[i] is the i-th element (0-indexed) of P(root). Equivalently, the values are visited in the order: root (if present), then the entire preorder traversal of the left subtree, then the entire preorder traversal of the right subtree.
    Preconditions: root is a finite binary tree. Let n be the number of Tree.Node constructors in root. The problem constraints hold: 0 <= n <= 100, and every node value v stored in root satisfies -100 <= v <= 100. -/
  theorem spec_1 (root : Aegis.PreorderTraversal.Tree)
      (hfinite : IsFiniteTree root)
      (hsize : nodeCount root ≤ 100)
      (hbounded : valuesBounded root) :
      ∀ r, preorder_traversal root = ok r →
        r.val.map (fun v => v.val) = preorderVals root ∧
        r.val.length = nodeCount root ∧
        (∀ (i : Nat) (hi : i < r.val.length), r.val[i].val = preorderNth root i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Aegis.PreorderTraversal.Tree)
        (hfinite : IsFiniteTree root)
        (hsize : nodeCount root ≤ 100)
        (hbounded : valuesBounded root), ∀ r, preorder_traversal root = ok r →
          r.val.map (fun v => v.val) = preorderVals root ∧
          r.val.length = nodeCount root ∧
          (∀ (i : Nat) (hi : i < r.val.length), r.val[i].val = preorderNth root i)) := by
    sorry

  /-- The call `preorder_traversal(root)` returns `Ok(r)` for some vector r of 64-bit integers; it never returns `Err`.
    Preconditions: root is a finite binary tree. Let n be the number of Tree.Node constructors in root. The problem constraints hold: 0 <= n <= 100, and every node value v stored in root satisfies -100 <= v <= 100. -/
  theorem spec_2 (root : Aegis.PreorderTraversal.Tree)
      (hfinite : IsFiniteTree root)
      (hsize : nodeCount root ≤ 100)
      (hbounded : valuesBounded root) :
      ∃ r : alloc.vec.Vec Aeneas.Std.I64, preorder_traversal root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Aegis.PreorderTraversal.Tree)
        (hfinite : IsFiniteTree root)
        (hsize : nodeCount root ≤ 100)
        (hbounded : valuesBounded root), ∃ r : alloc.vec.Vec Aeneas.Std.I64, preorder_traversal root = ok r) := by
    sorry

  /-- Whenever `preorder_traversal(root)` returns `Ok(r)`, for every 64-bit integer x, the number of indices i with 0 <= i < len(r) and r[i] = x equals the number of nodes in root whose stored value is x.
    Preconditions: root is a finite binary tree. Let n be the number of Tree.Node constructors in root. The problem constraints hold: 0 <= n <= 100, and every node value v stored in root satisfies -100 <= v <= 100. -/
  theorem spec_3 (root : Aegis.PreorderTraversal.Tree)
      (hfinite : IsFiniteTree root)
      (hsize : nodeCount root ≤ 100)
      (hbounded : valuesBounded root) :
      ∀ r, preorder_traversal root = ok r →
        ∀ x : Aeneas.Std.I64, listValueCount x.val r.val = treeValueCount x.val root := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Aegis.PreorderTraversal.Tree)
        (hfinite : IsFiniteTree root)
        (hsize : nodeCount root ≤ 100)
        (hbounded : valuesBounded root), ∀ r, preorder_traversal root = ok r →
          ∀ x : Aeneas.Std.I64, listValueCount x.val r.val = treeValueCount x.val root) := by
    sorry

  /-- Whenever `preorder_traversal(root)` returns `Ok(r)`, for every index i with 0 <= i < len(r), -100 <= r[i] <= 100.
    Preconditions: root is a finite binary tree. Let n be the number of Tree.Node constructors in root. The problem constraints hold: 0 <= n <= 100, and every node value v stored in root satisfies -100 <= v <= 100. -/
  theorem spec_4 (root : Aegis.PreorderTraversal.Tree)
      (hfinite : IsFiniteTree root)
      (hsize : nodeCount root ≤ 100)
      (hbounded : valuesBounded root) :
      ∀ r, preorder_traversal root = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), (-100 : Int) ≤ r.val[i].val ∧ r.val[i].val ≤ 100 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Aegis.PreorderTraversal.Tree)
        (hfinite : IsFiniteTree root)
        (hsize : nodeCount root ≤ 100)
        (hbounded : valuesBounded root), ∀ r, preorder_traversal root = ok r →
          ∀ (i : Nat) (hi : i < r.val.length), (-100 : Int) ≤ r.val[i].val ∧ r.val[i].val ≤ 100) := by
    sorry

  end AegisSpec.PreorderTraversal
