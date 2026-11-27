import Aegis.TrimBst.Code.Funs

/-!
# Specifications of `Aegis.TrimBst.trim_bst`

LeetCode problem `trim-a-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.TrimBst

open Aegis.TrimBst

def nodeCount : Tree → Nat
  | .Null => 0
  | .Node _ l r => nodeCount l + nodeCount r + 1

def values : Tree → List Int
  | .Null => []
  | .Node v l r => v.val :: (values l ++ values r)

def Occurs : Tree → Int → Prop
  | .Null, _ => False
  | .Node u l r, v => u.val = v ∨ Occurs l v ∨ Occurs r v

def countVal : Tree → Int → Nat
  | .Null, _ => 0
  | .Node u l r, v => (if u.val = v then 1 else 0) + countVal l v + countVal r v

def countInRange : Tree → Int → Int → Nat
  | .Null, _, _ => 0
  | .Node u l r, lo, hi =>
      (if lo ≤ u.val ∧ u.val ≤ hi then 1 else 0) + countInRange l lo hi + countInRange r lo hi

def inorder : Tree → List Int
  | .Null => []
  | .Node v l r => inorder l ++ [v.val] ++ inorder r

def AllLt : Tree → Int → Prop
  | .Null, _ => True
  | .Node u l r, v => u.val < v ∧ AllLt l v ∧ AllLt r v

def AllGt : Tree → Int → Prop
  | .Null, _ => True
  | .Node u l r, v => v < u.val ∧ AllGt l v ∧ AllGt r v

def IsStrictBst : Tree → Prop
  | .Null => True
  | .Node v l r => IsStrictBst l ∧ IsStrictBst r ∧ AllLt l v.val ∧ AllGt r v.val

def AllInRange : Tree → Int → Int → Prop
  | .Null, _, _ => True
  | .Node u l r, lo, hi => lo ≤ u.val ∧ u.val ≤ hi ∧ AllInRange l lo hi ∧ AllInRange r lo hi

def IsProperAncestorVal : Tree → Int → Int → Prop
  | .Null, _, _ => False
  | .Node u l r, v, w =>
      (u.val = v ∧ (Occurs l w ∨ Occurs r w)) ∨ IsProperAncestorVal l v w ∨ IsProperAncestorVal r v w

def rootVal : Tree → Option Int
  | .Null => none
  | .Node v _ _ => some v.val

def IsParentVal : Tree → Int → Int → Prop
  | .Null, _, _ => False
  | .Node u l r, c, p =>
      (u.val = p ∧ (rootVal l = some c ∨ rootVal r = some c))
      ∨ IsParentVal l c p ∨ IsParentVal r c p

def IsLeftSubtreeOfVal : Tree → Int → Tree → Prop
  | .Null, _, _ => False
  | .Node u l r, v, s => (u.val = v ∧ s = l) ∨ IsLeftSubtreeOfVal l v s ∨ IsLeftSubtreeOfVal r v s

def IsRightSubtreeOfVal : Tree → Int → Tree → Prop
  | .Null, _, _ => False
  | .Node u l r, v, s => (u.val = v ∧ s = r) ∨ IsRightSubtreeOfVal l v s ∨ IsRightSubtreeOfVal r v s

def IsNearestAncestorInRange (t : Tree) (lo hi v p : Int) : Prop :=
  lo ≤ p ∧ p ≤ hi ∧ IsProperAncestorVal t p v ∧
    ∀ w, lo ≤ w → w ≤ hi → IsProperAncestorVal t w v → ¬ IsProperAncestorVal t p w

def SameVals : Tree → Tree → Prop
  | .Null, .Null => True
  | .Node v l r, .Node w l' r' => v.val = w.val ∧ SameVals l l' ∧ SameVals r r'
  | _, _ => False

def TrimContent (root : Tree) (lo hi : Int) (t : Tree) : Prop :=
  (∀ v : Int, Occurs root v → lo ≤ v → v ≤ hi → countVal t v = 1) ∧
  (∀ v : Int, ¬ (Occurs root v ∧ lo ≤ v ∧ v ≤ hi) → countVal t v = 0)

def TrimAncestry (root : Tree) (lo hi : Int) (t : Tree) : Prop :=
  ∀ v w : Int, v ≠ w →
    lo ≤ v → v ≤ hi → lo ≤ w → w ≤ hi →
    Occurs root v → Occurs root w →
    (IsProperAncestorVal t v w ↔ IsProperAncestorVal root v w)

/-- Whenever the preconditions hold, the function returns a result t, and t is the unique tree satisfying: (i) for every integer v, t contains exactly one node with value v if root contains a node with value v and low <= v <= high, and t contains no node with value v otherwise; (ii) for every two distinct integers v and w with low <= v <= high, low <= w <= high, and both occurring in root, the unique node of t with value v is a proper ancestor of the unique node of t with value w if and only if the node of root with value v is a proper ancestor of the node of root with value w, where a node a is a proper ancestor of b when b lies in the left or right subtree of a; (iii) t is a valid strict binary search tree: for every node of t with value v, every value in its left subtree is < v and every value in its right subtree is > v. This completely characterises the trimmed tree; the root of t may differ from the root of root.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_1 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∃ t : Tree, trim_bst root low high = ok t ∧
      TrimContent root low.val high.val t ∧
      TrimAncestry root low.val high.val t ∧
      IsStrictBst t ∧

      (∀ t' : Tree, TrimContent root low.val high.val t' →
        TrimAncestry root low.val high.val t' → IsStrictBst t' → SameVals t' t) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∃ t : Tree, trim_bst root low high = ok t ∧
      TrimContent root low.val high.val t ∧
      TrimAncestry root low.val high.val t ∧
      IsStrictBst t ∧

      (∀ t' : Tree, TrimContent root low.val high.val t' →
        TrimAncestry root low.val high.val t' → IsStrictBst t' → SameVals t' t)) := by
  sorry

/-- Whenever the preconditions hold, the function returns a result t; it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_2 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∃ t : Tree, trim_bst root low high = ok t := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∃ t : Tree, trim_bst root low high = ok t) := by
  sorry

/-- Whenever the function returns a result t, every node value in t lies in [low, high]. If t is Null this condition is vacuous.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_3 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t → AllInRange t low.val high.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t → AllInRange t low.val high.val) := by
  sorry

/-- Whenever the function returns a result t, for every integer v, if some node of root has value v and low <= v <= high, then some node of t has value v.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_4 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v : Int, Occurs root v → low.val ≤ v → v ≤ high.val → Occurs t v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v : Int, Occurs root v → low.val ≤ v → v ≤ high.val → Occurs t v) := by
  sorry

/-- Whenever the function returns a result t, for every integer v, if some node of t has value v, then some node of root has value v.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_5 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t → ∀ v : Int, Occurs t v → Occurs root v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t → ∀ v : Int, Occurs t v → Occurs root v) := by
  sorry

/-- Whenever the function returns a result t, if t is not Null then t is a valid strict binary search tree: for every node of t with value v, every value in its left subtree is < v and every value in its right subtree is > v.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_6 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t → t ≠ Tree.Null → IsStrictBst t := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t → t ≠ Tree.Null → IsStrictBst t) := by
  sorry

/-- Whenever the function returns a result t, the inorder traversal of t is exactly the inorder traversal of root with every value outside [low, high] deleted; equivalently, it is the sequence of those values occurring in root that lie in [low, high], in their original inorder order.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_7 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t →
      inorder t = (inorder root).filter (fun v : Int => decide (low.val ≤ v ∧ v ≤ high.val)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t →
      inorder t = (inorder root).filter (fun v : Int => decide (low.val ≤ v ∧ v ≤ high.val))) := by
  sorry

/-- Whenever the function returns a result t, for every two distinct integers v and w occurring in t, the node with value v is a proper ancestor of the node with value w in t if and only if the node with value v is a proper ancestor of the node with value w in root. Here a proper ancestor means lying strictly on the path above the node.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_8 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v w : Int, v ≠ w → Occurs t v → Occurs t w →
        (IsProperAncestorVal t v w ↔ IsProperAncestorVal root v w) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v w : Int, v ≠ w → Occurs t v → Occurs t w →
        (IsProperAncestorVal t v w ↔ IsProperAncestorVal root v w)) := by
  sorry

/-- Whenever the function returns a result t, for every value v occurring in t that is not the value at the root of t, let u be the node of root with value v. Let p be the value of the nearest proper ancestor of u in root whose value lies in [low, high] (such a p exists). Then the parent in t of the node with value v is the node with value p.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_9 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v : Int, Occurs t v → rootVal t ≠ some v →
        ∃ p : Int, IsNearestAncestorInRange root low.val high.val v p ∧ IsParentVal t v p := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v : Int, Occurs t v → rootVal t ≠ some v →
        ∃ p : Int, IsNearestAncestorInRange root low.val high.val v p ∧ IsParentVal t v p) := by
  sorry

/-- Whenever the function returns a result t, for every value v occurring in t, let u be the node of root with value v. The set of values in the left subtree of the node with value v in t is exactly { w | some node of the left subtree of u in root has value w and low <= w <= high }; and the set of values in the right subtree of the node with value v in t is exactly { w | some node of the right subtree of u in root has value w and low <= w <= high }.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_10 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v : Int, Occurs t v →
        (∀ s : Tree, IsLeftSubtreeOfVal t v s →
          ∀ w : Int,
            (Occurs s w ↔
              (∃ sr : Tree, IsLeftSubtreeOfVal root v sr ∧ Occurs sr w) ∧
                low.val ≤ w ∧ w ≤ high.val)) ∧
        (∀ s : Tree, IsRightSubtreeOfVal t v s →
          ∀ w : Int,
            (Occurs s w ↔
              (∃ sr : Tree, IsRightSubtreeOfVal root v sr ∧ Occurs sr w) ∧
                low.val ≤ w ∧ w ≤ high.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t →
      ∀ v : Int, Occurs t v →
        (∀ s : Tree, IsLeftSubtreeOfVal t v s →
          ∀ w : Int,
            (Occurs s w ↔
              (∃ sr : Tree, IsLeftSubtreeOfVal root v sr ∧ Occurs sr w) ∧
                low.val ≤ w ∧ w ≤ high.val)) ∧
        (∀ s : Tree, IsRightSubtreeOfVal t v s →
          ∀ w : Int,
            (Occurs s w ↔
              (∃ sr : Tree, IsRightSubtreeOfVal root v sr ∧ Occurs sr w) ∧
                low.val ≤ w ∧ w ≤ high.val))) := by
  sorry

/-- Whenever the function returns a result t, the number of nodes in t equals the number of nodes of root whose value lies in [low, high].
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_11 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t → nodeCount t = countInRange root low.val high.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t → nodeCount t = countInRange root low.val high.val) := by
  sorry

/-- Whenever the function returns a result t, t is not Null and the value at the root of t is v, the original root value.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. Additionally, root is Node(v, left, right) and low <= v <= high. -/
theorem spec_12 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000)
    (v : Std.I64) (left right : Tree) (hroot : root = Tree.Node v left right)
    (hvlow : low.val ≤ v.val) (hvhigh : v.val ≤ high.val) :
    ∀ t : Tree, trim_bst root low high = ok t → t ≠ Tree.Null ∧ rootVal t = some v.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000)
    (v : Std.I64) (left right : Tree) (hroot : root = Tree.Node v left right)
    (hvlow : low.val ≤ v.val) (hvhigh : v.val ≤ high.val), ∀ t : Tree, trim_bst root low high = ok t → t ≠ Tree.Null ∧ rootVal t = some v.val) := by
  sorry

/-- Whenever the function returns a result t, t is structurally identical to root: it has the same Null/Node shape and the same value at every corresponding node.
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. Additionally, every value occurring in root satisfies low <= value <= high. -/
theorem spec_13 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000)
    (hinrange : ∀ v : Int, Occurs root v → low.val ≤ v ∧ v ≤ high.val) :
    ∀ t : Tree, trim_bst root low high = ok t → SameVals t root := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000)
    (hinrange : ∀ v : Int, Occurs root v → low.val ≤ v ∧ v ≤ high.val), ∀ t : Tree, trim_bst root low high = ok t → SameVals t root) := by
  sorry

/-- Whenever the function returns a result t, t is Null if and only if there is no value v such that some node of root has value v and low <= v <= high. Equivalently, t is non-Null exactly when root contains at least one value in [low, high].
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. -/
theorem spec_14 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000) :
    ∀ t : Tree, trim_bst root low high = ok t →
      (t = Tree.Null ↔ ¬ ∃ v : Int, Occurs root v ∧ low.val ≤ v ∧ v ≤ high.val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000), ∀ t : Tree, trim_bst root low high = ok t →
      (t = Tree.Null ↔ ¬ ∃ v : Int, Occurs root v ∧ low.val ≤ v ∧ v ≤ high.val)) := by
  sorry

/-- Whenever the function returns a result t, if no node of root has value low then t is Null; if some node of root has value low then t is exactly Node(low, Null, Null).
  Preconditions: root is a nonempty binary tree with between 1 and 10^4 nodes; every node value is in [0, 10^4] and all node values are distinct; root is a valid strict binary search tree (for every node with value v, every value in its left subtree is < v and every value in its right subtree is > v); and 0 <= low <= high <= 10^4. Additionally, low = high. -/
theorem spec_15 (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000)
    (hloweq : low = high) :
    ∀ t : Tree, trim_bst root low high = ok t →
      (¬ Occurs root low.val → t = Tree.Null) ∧
      (Occurs root low.val → t = Tree.Node low Tree.Null Tree.Null) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (root : Tree) (low high : Std.I64)
    (hne : root ≠ Tree.Null)
    (hnodes1 : 1 ≤ nodeCount root) (hnodes2 : nodeCount root ≤ 10000)
    (hvals : AllInRange root 0 10000)
    (hdistinct : (values root).Nodup)
    (hbst : IsStrictBst root)
    (hlow0 : 0 ≤ low.val) (hlowhigh : low.val ≤ high.val) (hhigh10k : high.val ≤ 10000)
    (hloweq : low = high), ∀ t : Tree, trim_bst root low high = ok t →
      (¬ Occurs root low.val → t = Tree.Null) ∧
      (Occurs root low.val → t = Tree.Node low Tree.Null Tree.Null)) := by
  sorry

end AegisSpec.TrimBst
