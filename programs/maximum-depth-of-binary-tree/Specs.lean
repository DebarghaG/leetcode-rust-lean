import Aegis.MaxDepth.Code.Funs

/-!
# Specifications of `Aegis.MaxDepth.max_depth`

LeetCode problem `maximum-depth-of-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxDepth

  open Aegis.MaxDepth

  def nodes : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodes l + nodes r

  def labels : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (labels l ++ labels r)

  def labelsInRange (t : Tree) : Prop := ∀ v ∈ labels t, -100 ≤ v ∧ v ≤ 100

  def pre (t : Tree) : Prop := nodes t ≤ 10000 ∧ labelsInRange t

  def IsLeaf (t : Tree) : Prop := ∃ v : Std.I64, t = Tree.Node v Tree.Null Tree.Null

  def IsChild (c p : Tree) : Prop :=
    (∃ v r, p = Tree.Node v c r) ∨ (∃ v l, p = Tree.Node v l c)

  def WalkFrom (t : Tree) : List Tree → Prop
    | [] => True
    | c :: rest => IsChild c t ∧ WalkFrom c rest

  def IsRootToLeafPath (root : Tree) (p : List Tree) : Prop :=
    (∃ tail, p = root :: tail ∧ WalkFrom root tail) ∧
      ∃ L, p.getLast? = some L ∧ IsLeaf L

  def AtDistance (root : Tree) : Nat → Tree → Prop
    | 0, t => t = root
    | d + 1, t =>
      ∃ v l r, root = Tree.Node v l r ∧ (AtDistance l d t ∨ AtDistance r d t)

  def MaxDepth : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (MaxDepth l) (MaxDepth r)

  def sameShape : Tree → Tree → Bool
    | Tree.Null, Tree.Null => true
    | Tree.Node _ l1 r1, Tree.Node _ l2 r2 => sameShape l1 l2 && sameShape r1 r2
    | _, _ => false

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  /-- Define a leaf as a node Node(v, Null, Null), and define a root-to-leaf path in root as a sequence of nodes T0,...,Tk such that T0 = root, each T_{i+1} is the left or right child of T_i, and T_k is a leaf; its length is k+1, the number of nodes. If root = Null, there is no root-to-leaf path and define MaxDepth(root) = 0. If root is non-null, define MaxDepth(root) as the maximum length of any root-to-leaf path in root (such a path always exists). Then max_depth(root) returns a result r and r = MaxDepth(root).
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_1 (root : Tree) (h : pre root) :
      ∃ r : Std.I64, max_depth root = ok r ∧ r.val = (MaxDepth root : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (h : pre root), ∃ r : Std.I64, max_depth root = ok r ∧ r.val = (MaxDepth root : Int)) := by
    sorry

  /-- For every root satisfying the preconditions, the call max_depth(root) returns a result r; it does not fail, overflow, or panic.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_2 (root : Tree) (h : pre root) :
      ∃ r : Std.I64, max_depth root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (h : pre root), ∃ r : Std.I64, max_depth root = ok r) := by
    sorry

  /-- For every root satisfying the preconditions, max_depth(root) returns a result r and 0 <= r <= nodes(root), where nodes(root) is the number of Node constructors in root.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_3 (root : Tree) (h : pre root) :
      ∃ r : Std.I64, max_depth root = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (nodes root : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (h : pre root), ∃ r : Std.I64, max_depth root = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (nodes root : Int)) := by
    sorry

  /-- For every root satisfying the preconditions with root = Node(v,l,r), if max_depth(l) returns dl and max_depth(r) returns dr, then max_depth(root) returns d and d = 1 + max(dl, dr). Here max is the usual maximum of two i64 values, and max_depth(Null) is 0 by the empty-tree case.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_4 (v : Std.I64) (l r : Tree) (h : pre (Tree.Node v l r))
      (dl dr : Std.I64) (hl : max_depth l = ok dl) (hr : max_depth r = ok dr) :
      ∃ d : Std.I64,
        max_depth (Tree.Node v l r) = ok d ∧ d.val = 1 + max dl.val dr.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (v : Std.I64) (l r : Tree) (h : pre (Tree.Node v l r))
        (dl dr : Std.I64) (hl : max_depth l = ok dl) (hr : max_depth r = ok dr), ∃ d : Std.I64,
          max_depth (Tree.Node v l r) = ok d ∧ d.val = 1 + max dl.val dr.val) := by
    sorry

  /-- max_depth(root) returns a result r and there exists a leaf L of root such that the distance from root to L, the number of edges on the unique path from root down to L, is r - 1.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100, and root is non-null. -/
  theorem spec_5 (root : Tree) (h : pre root) (hne : root ≠ Tree.Null) :
      ∃ r : Std.I64,
        max_depth root = ok r ∧
          ∃ (L : Tree) (d : Nat), AtDistance root d L ∧ IsLeaf L ∧ r.val = (d : Int) + 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (h : pre root) (hne : root ≠ Tree.Null), ∃ r : Std.I64,
          max_depth root = ok r ∧
            ∃ (L : Tree) (d : Nat), AtDistance root d L ∧ IsLeaf L ∧ r.val = (d : Int) + 1) := by
    sorry

  /-- max_depth(root) returns a result r and for every root-to-leaf path P in root, the length of P, defined as the number of nodes in P, is at most r. If root = Null, there are no root-to-leaf paths and the condition is vacuous.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_6 (root : Tree) (h : pre root) :
      ∃ r : Std.I64,
        max_depth root = ok r ∧
          ∀ p : List Tree, IsRootToLeafPath root p → (p.length : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (h : pre root), ∃ r : Std.I64,
          max_depth root = ok r ∧
            ∀ p : List Tree, IsRootToLeafPath root p → (p.length : Int) ≤ r.val) := by
    sorry

  /-- max_depth(root) returns a result r and for every node u of root, if u is at distance d from root, meaning the number of edges on the unique path from root down to u, with d = 0 for the root itself, then d + 1 <= r.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_7 (root : Tree) (h : pre root) :
      ∃ r : Std.I64,
        max_depth root = ok r ∧
          ∀ (u : Tree) (d : Nat), u ≠ Tree.Null → AtDistance root d u → (d : Int) + 1 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (h : pre root), ∃ r : Std.I64,
          max_depth root = ok r ∧
            ∀ (u : Tree) (d : Nat), u ≠ Tree.Null → AtDistance root d u → (d : Int) + 1 ≤ r.val) := by
    sorry

  /-- max_depth(root) returns a result r. For every tree T such that either T = root or T is the subtree rooted at some node of root (including a Null child of a leaf), if max_depth(T) returns d, then d <= r.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_8 (root : Tree) (h : pre root) :
      ∃ r : Std.I64,
        max_depth root = ok r ∧
          ∀ T : Tree, (∃ d : Nat, AtDistance root d T) →
            ∀ d' : Std.I64, max_depth T = ok d' → d'.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (h : pre root), ∃ r : Std.I64,
          max_depth root = ok r ∧
            ∀ T : Tree, (∃ d : Nat, AtDistance root d T) →
              ∀ d' : Std.I64, max_depth T = ok d' → d'.val ≤ r.val) := by
    sorry

  /-- Define same_shape recursively by: same_shape(Null, Null) = true; same_shape(Node(_, l1, r1), Node(_, l2, r2)) = (same_shape(l1, l2) and same_shape(r1, r2)); same_shape(T1, T2) = false in all other cases. For every two trees root1 and root2, if same_shape(root1, root2) holds, and if max_depth(root1) returns r1 and max_depth(root2) returns r2, then r1 = r2.
    Preconditions: For two trees root1 and root2, each satisfies nodes(.) <= 10000, and every label v in any Node(v,_,_) of either tree satisfies -100 <= v <= 100. -/
  theorem spec_9 (root1 root2 : Tree) (h1 : pre root1) (h2 : pre root2)
      (hs : sameShape root1 root2 = true) (r1 r2 : Std.I64)
      (h1' : max_depth root1 = ok r1) (h2' : max_depth root2 = ok r2) : r1 = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root1 root2 : Tree) (h1 : pre root1) (h2 : pre root2)
        (hs : sameShape root1 root2 = true) (r1 r2 : Std.I64)
        (h1' : max_depth root1 = ok r1) (h2' : max_depth root2 = ok r2), r1 = r2) := by
    sorry

  /-- Define mirror(Null) = Null and mirror(Node(v,l,r)) = Node(v, mirror(r), mirror(l)). For every root satisfying the preconditions, if max_depth(root) returns r and max_depth(mirror(root)) returns r', then r = r'.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_10 (root : Tree) (h : pre root) (r r' : Std.I64)
      (h1 : max_depth root = ok r) (h2 : max_depth (mirror root) = ok r') : r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (h : pre root) (r r' : Std.I64)
        (h1 : max_depth root = ok r) (h2 : max_depth (mirror root) = ok r'), r = r') := by
    sorry

  /-- For every root satisfying the preconditions, max_depth(root) returns a result r and r = 0 if and only if root = Null; equivalently, r > 0 exactly when root is non-null.
    Preconditions: Let nodes(T) be the number of Node constructors in T. The input root satisfies nodes(root) <= 10000, and every label v in any Node(v,_,_) of root satisfies -100 <= v <= 100. -/
  theorem spec_11 (root : Tree) (h : pre root) :
      ∃ r : Std.I64, max_depth root = ok r ∧ (r.val = 0 ↔ root = Tree.Null) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (h : pre root), ∃ r : Std.I64, max_depth root = ok r ∧ (r.val = 0 ↔ root = Tree.Null)) := by
    sorry

  end AegisSpec.MaxDepth
