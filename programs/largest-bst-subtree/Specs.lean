import Aegis.LargestBstSubtree.Code.Funs

/-!
# Specifications of `Aegis.LargestBstSubtree.largest_bst_subtree`

LeetCode problem `largest-bst-subtree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LargestBstSubtree

  namespace AegisSpec.LargestBstSubtree

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => size l + size r + 1

  def inorder : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => inorder l ++ [v.val] ++ inorder r

  @[reducible] def IsBst (t : Tree) : Prop := (inorder t).Pairwise fun a b => a < b

  def isBst (t : Tree) : Bool := decide ((inorder t).Pairwise fun a b => a < b)

  def subtrees : Tree → List Tree
    | Tree.Null => [Tree.Null]
    | Tree.Node v l r => Tree.Node v l r :: (subtrees l ++ subtrees r)

  def LBST (t : Tree) : Nat :=
    (subtrees t).foldr (fun s acc => if isBst s then Nat.max (size s) acc else acc) 0

  inductive CompleteSubtree : Tree → Tree → Prop where
    | refl (t : Tree) : CompleteSubtree t t
    | left {s : Tree} {v : Std.I64} {l r : Tree} :
        CompleteSubtree s l → CompleteSubtree s (Tree.Node v l r)
    | right {s : Tree} {v : Std.I64} {l r : Tree} :
        CompleteSubtree s r → CompleteSubtree s (Tree.Node v l r)

  def Occurs (v : Std.I64) : Tree → Prop
    | Tree.Null => False
    | Tree.Node w l r => v = w ∨ Occurs v l ∨ Occurs v r

  inductive MapVals (f : Std.I64 → Std.I64) : Tree → Tree → Prop where
    | null : MapVals f Tree.Null Tree.Null
    | node {v : Std.I64} {l l' r r' : Tree}
        (hl : MapVals f l l') (hr : MapVals f r r') :
        MapVals f (Tree.Node v l r) (Tree.Node (f v) l' r')

  /-- The function returns a result r (it does not fail), and r = L(root), where L(Null)=0, and for non-Null t, L(t) is the maximum number of nodes in a complete subtree s of t that is a BST. A complete subtree of t is the whole tree rooted at some node u of t together with all descendants of u in t. A tree is a BST exactly when its in-order sequence of node values is strictly increasing; equivalently, for every node, all values in its left subtree are less than its value, all values in its right subtree are greater than its value, and both child subtrees are BSTs.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_1 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r : Std.I64,
        largest_bst_subtree root = ok r ∧
        r.val = (LBST root : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r : Std.I64,
          largest_bst_subtree root = ok r ∧
          r.val = (LBST root : Int)) := by
    sorry

  /-- The function returns a result r; it does not overflow, go out of bounds, or panic.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_2 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r : Std.I64, largest_bst_subtree root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r : Std.I64, largest_bst_subtree root = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n, where n is the number of nodes in root.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_3 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∀ r : Std.I64,
        largest_bst_subtree root = ok r →
        0 ≤ r.val ∧ r.val ≤ (size root : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000), ∀ r : Std.I64,
          largest_bst_subtree root = ok r →
          0 ≤ r.val ∧ r.val ≤ (size root : Int)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if root = Null.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_4 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r : Std.I64,
        largest_bst_subtree root = ok r ∧
        (r.val = 0 ↔ root = Tree.Null) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r : Std.I64,
          largest_bst_subtree root = ok r ∧
          (r.val = 0 ↔ root = Tree.Null)) := by
    sorry

  /-- If root = Node(v, Null, Null) for some i64 v, then the function returns 1.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_5 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
      (v : Std.I64) (hroot : root = Tree.Node v Tree.Null Tree.Null) :
      ∃ r : Std.I64, largest_bst_subtree root = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
        (v : Std.I64) (hroot : root = Tree.Node v Tree.Null Tree.Null), ∃ r : Std.I64, largest_bst_subtree root = ok r ∧ r.val = 1) := by
    sorry

  /-- If root is a BST, then the function returns n, the number of nodes in root. Here BST means the in-order sequence of node values is strictly increasing (Null is a BST).
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_6 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hbst : IsBst root) :
      ∃ r : Std.I64,
        largest_bst_subtree root = ok r ∧
        r.val = (size root : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hbst : IsBst root), ∃ r : Std.I64,
          largest_bst_subtree root = ok r ∧
          r.val = (size root : Int)) := by
    sorry

  /-- If root is not a BST, then the function returns a result r and r < n, where n is the number of nodes in root.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_7 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hbst : ¬ IsBst root) :
      ∃ r : Std.I64,
        largest_bst_subtree root = ok r ∧
        r.val < (size root : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hbst : ¬ IsBst root), ∃ r : Std.I64,
          largest_bst_subtree root = ok r ∧
          r.val < (size root : Int)) := by
    sorry

  /-- If root is not Null, then the function returns a result r and there exists a complete subtree s of root such that s is a BST and s has exactly r nodes. A complete subtree of root is the tree rooted at some node u of root together with all descendants of u; a BST is a tree whose in-order sequence of node values is strictly increasing.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_8 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hne : root ≠ Tree.Null) :
      ∃ r : Std.I64,
        largest_bst_subtree root = ok r ∧
        ∃ s : Tree, CompleteSubtree s root ∧ IsBst s ∧ (size s : Int) = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hne : root ≠ Tree.Null), ∃ r : Std.I64,
          largest_bst_subtree root = ok r ∧
          ∃ s : Tree, CompleteSubtree s root ∧ IsBst s ∧ (size s : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every complete subtree s of root, if s is a BST (its in-order sequence of node values is strictly increasing), then the number of nodes in s is at most r. A complete subtree is a node of root together with all its descendants in root.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_9 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∀ r : Std.I64,
        largest_bst_subtree root = ok r →
        ∀ s : Tree, CompleteSubtree s root → IsBst s → (size s : Int) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000), ∀ r : Std.I64,
          largest_bst_subtree root = ok r →
          ∀ s : Tree, CompleteSubtree s root → IsBst s → (size s : Int) ≤ r.val) := by
    sorry

  /-- If root = Node(v, L, R) and root is not a BST, then the function returns a result r and r = max(LBST(L), LBST(R)), where for any tree t, LBST(t) is the largest number of nodes in a complete subtree of t whose in-order sequence is strictly increasing, with LBST(Null)=0; a complete subtree of t is a node of t together with all its descendants in t.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_10 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
      (v : Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R)
      (hbst : ¬ IsBst root) :
      ∃ r : Std.I64,
        largest_bst_subtree root = ok r ∧
        r.val = (Nat.max (LBST L) (LBST R) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
        (v : Std.I64) (L R : Tree) (hroot : root = Tree.Node v L R)
        (hbst : ¬ IsBst root), ∃ r : Std.I64,
          largest_bst_subtree root = ok r ∧
          r.val = (Nat.max (LBST L) (LBST R) : Int)) := by
    sorry

  /-- If root has exactly two nodes and is not a BST, that is, either root = Node(v, Node(u, Null, Null), Null) with u >= v or root = Node(v, Null, Node(u, Null, Null)) with u <= v, then the function returns 1.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_11 (root : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
      (v u : Std.I64)
      (hroot :
        (root = Tree.Node v (Tree.Node u Tree.Null Tree.Null) Tree.Null ∧ v.val ≤ u.val) ∨
        (root = Tree.Node v Tree.Null (Tree.Node u Tree.Null Tree.Null) ∧ u.val ≤ v.val)) :
      ∃ r : Std.I64, largest_bst_subtree root = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
        (v u : Std.I64)
        (hroot :
          (root = Tree.Node v (Tree.Node u Tree.Null Tree.Null) Tree.Null ∧ v.val ≤ u.val) ∨
          (root = Tree.Node v Tree.Null (Tree.Node u Tree.Null Tree.Null) ∧ u.val ≤ v.val)), ∃ r : Std.I64, largest_bst_subtree root = ok r ∧ r.val = 1) := by
    sorry

  /-- Let f be any strictly increasing function from i64 to i64, and let root' be the tree obtained from root by replacing every node value v with f(v). If every node value in root' also satisfies -10000 <= value <= 10000, then both largest_bst_subtree(root) and largest_bst_subtree(root') return results, and these two results are equal.
    Preconditions: Let n be the number of nodes in root. Assume 0 <= n <= 10000 and every Node value v in root satisfies -10000 <= v <= 10000. -/
  theorem spec_12 (root root' : Tree)
      (hn : size root ≤ 10000)
      (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
      (f : Std.I64 → Std.I64) (hf : ∀ a b : Std.I64, a.val < b.val → (f a).val < (f b).val)
      (hmap : MapVals f root root')
      (hv' : ∀ v : Std.I64, Occurs v root' → -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r r' : Std.I64,
        largest_bst_subtree root = ok r ∧
        largest_bst_subtree root' = ok r' ∧ r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root root' : Tree)
        (hn : size root ≤ 10000)
        (hv : ∀ v : Std.I64, Occurs v root → -10000 ≤ v.val ∧ v.val ≤ 10000)
        (f : Std.I64 → Std.I64) (hf : ∀ a b : Std.I64, a.val < b.val → (f a).val < (f b).val)
        (hmap : MapVals f root root')
        (hv' : ∀ v : Std.I64, Occurs v root' → -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r r' : Std.I64,
          largest_bst_subtree root = ok r ∧
          largest_bst_subtree root' = ok r' ∧ r = r') := by
    sorry

  end AegisSpec.LargestBstSubtree
