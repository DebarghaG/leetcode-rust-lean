import Aegis.SubtreeWithAllDeepest.Code.Funs

/-!
# Specifications of `Aegis.SubtreeWithAllDeepest.subtree_with_all_deepest`

LeetCode problem `smallest-subtree-with-all-the-deepest-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubtreeWithAllDeepest

open Aegis.SubtreeWithAllDeepest

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => nodeCount l + nodeCount r + 1

def values : Tree → List ℤ
  | Tree.Null => []
  | Tree.Node x l r => x.val :: (values l ++ values r)

def height : Tree → ℤ
  | Tree.Null => -1
  | Tree.Node _ l r => 1 + max (height l) (height r)

def maxNodeDepth (t : Tree) : Nat := (height t).toNat

def nodeAt : Tree → List Bool → Option Tree
  | t, [] => some t
  | Tree.Null, _ :: _ => none
  | Tree.Node _ l _, true :: ps => nodeAt l ps
  | Tree.Node _ _ r, false :: ps => nodeAt r ps

def paths : Tree → List (List Bool)
  | Tree.Null => []
  | Tree.Node _ l r =>
    [] :: ((paths l).map (fun p => true :: p) ++ (paths r).map (fun p => false :: p))

def IsDeepestPath (t : Tree) (p : List Bool) : Prop :=
  p ∈ paths t ∧ p.length = maxNodeDepth t

def IsAncestorOfDeepest (t : Tree) (p : List Bool) : Prop :=
  p ∈ paths t ∧ ∀ q, IsDeepestPath t q → p <+: q

def IsLCAOfDeepest (t : Tree) (p : List Bool) : Prop :=
  IsAncestorOfDeepest t p ∧ ∀ p', IsAncestorOfDeepest t p' → p' <+: p

def IsSubtreeOf (out root : Tree) : Prop :=
  ∃ p, nodeAt root p = some out

def IsSubtreeAtLCAOfDeepest (t out : Tree) : Prop :=
  ∃ p, IsLCAOfDeepest t p ∧ nodeAt t p = some out

def valuesInRange (t : Tree) : Prop :=
  ∀ v ∈ values t, 0 ≤ v ∧ v ≤ 500

def valuesDistinct (t : Tree) : Prop :=
  (values t).Nodup

/-- The function returns a result out (Result.ok out) and there is a node v of root such that: (1) every deepest node of root is v or a descendant of v; (2) no immediate child of v has the property that every deepest node of root is that child or a descendant of that child; and (3) out is exactly the subtree of root rooted at v, i.e. the tree consisting of v and all descendants of v, with the same left and right child relationships as in root. The depth of a node is its distance from the root (the root has depth 0), and a deepest node of root is a node whose depth equals the maximum depth over all nodes of root.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_1 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∃ (out : Tree) (p : List Bool),
      subtree_with_all_deepest root = ok out ∧
        nodeAt root p = some out ∧
          IsAncestorOfDeepest root p ∧ ∀ b : Bool, ¬ IsAncestorOfDeepest root (p ++ [b]) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∃ (out : Tree) (p : List Bool),
      subtree_with_all_deepest root = ok out ∧
        nodeAt root p = some out ∧
          IsAncestorOfDeepest root p ∧ ∀ b : Bool, ¬ IsAncestorOfDeepest root (p ++ [b])) := by
  sorry

/-- The function returns a result out (Result.ok out); in particular, it does not fail, panic, access out of bounds, or overflow.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_2 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∃ out : Tree, subtree_with_all_deepest root = ok out := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∃ out : Tree, subtree_with_all_deepest root = ok out) := by
  sorry

/-- Whenever the function returns a result out, out ≠ Tree.Null.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_3 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∀ out : Tree, subtree_with_all_deepest root = ok out → out ≠ Tree.Null := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∀ out : Tree, subtree_with_all_deepest root = ok out → out ≠ Tree.Null) := by
  sorry

/-- Whenever the function returns a result out, out is a subtree of root: there exists a node v of root such that out is obtained from root by keeping exactly v and all descendants of v, with their original left and right child relationships, and deleting every other node.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_4 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∀ out : Tree, subtree_with_all_deepest root = ok out → IsSubtreeOf out root := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∀ out : Tree, subtree_with_all_deepest root = ok out → IsSubtreeOf out root) := by
  sorry

/-- Whenever the function returns a result out, every deepest node of root occurs as a node of out, using the inclusion of out as a subtree of root.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_5 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool, nodeAt root p = some out ∧ ∀ q, IsDeepestPath root q → p <+: q := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool, nodeAt root p = some out ∧ ∀ q, IsDeepestPath root q → p <+: q) := by
  sorry

/-- Whenever the function returns a result out and v is the root node of out, for every node w of root such that every deepest node of root is w or a descendant of w, the node v is a descendant-or-equal of w. Equivalently, for every node w of root whose subtree contains all deepest nodes of root, the subtree out is contained in the subtree of root rooted at w.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_6 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool,
          nodeAt root p = some out ∧ ∀ p', IsAncestorOfDeepest root p' → p' <+: p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool,
          nodeAt root p = some out ∧ ∀ p', IsAncestorOfDeepest root p' → p' <+: p) := by
  sorry

/-- Whenever the function returns a result out (Result.ok out) and v is the root node of out (so out is the subtree of root rooted at v), v is the lowest common ancestor of all deepest nodes of root: (i) every deepest node of root is v or a descendant of v; and (ii) for every node w of root that is an ancestor-or-equal of every deepest node, w is an ancestor-or-equal of v (equivalently, v is w or a descendant of v).
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_7 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool, nodeAt root p = some out ∧ IsLCAOfDeepest root p := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool, nodeAt root p = some out ∧ IsLCAOfDeepest root p) := by
  sorry

/-- Whenever the function returns a result out, if out is viewed as the subtree of root rooted at its root node v, then the set of nodes of out whose depth measured from v is maximum within out is exactly the set of deepest nodes of root, viewed as nodes of root and hence of out.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_8 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool,
          nodeAt root p = some out ∧
            ∀ q : List Bool, (IsDeepestPath out q ↔ IsDeepestPath root (p ++ q)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∃ p : List Bool,
          nodeAt root p = some out ∧
            ∀ q : List Bool, (IsDeepestPath out q ↔ IsDeepestPath root (p ++ q))) := by
  sorry

/-- Whenever the function returns a result out, out = Tree.Node(value(d), Tree.Null, Tree.Null), i.e. the one-node tree whose only value is the value of d.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; all node values in root are pairwise distinct; and root has exactly one node d at maximum depth. -/
theorem spec_9 (root : Tree) (d : Std.I64) (l r : Tree) (p : List Bool)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hdeep : IsDeepestPath root p)
    (hnode : nodeAt root p = some (Tree.Node d l r))
    (huniq : ∀ q : List Bool, IsDeepestPath root q → q = p) :
    ∀ out : Tree,
      subtree_with_all_deepest root = ok out → out = Tree.Node d Tree.Null Tree.Null := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (d : Std.I64) (l r : Tree) (p : List Bool)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hdeep : IsDeepestPath root p)
    (hnode : nodeAt root p = some (Tree.Node d l r))
    (huniq : ∀ q : List Bool, IsDeepestPath root q → q = p), ∀ out : Tree,
      subtree_with_all_deepest root = ok out → out = Tree.Node d Tree.Null Tree.Null) := by
  sorry

/-- Whenever the function returns a result out, out = root.
  Preconditions: root = Tree.Node(x, left, right) with left ≠ Tree.Null and right ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; all node values in root are pairwise distinct; and height(left) = height(right), where height(Tree.Null) = -1 and height(Tree.Node(_, a, b)) = 1 + max(height(a), height(b)). -/
theorem spec_10 (root : Tree) (x : Std.I64) (left right : Tree)
    (hroot : root = Tree.Node x left right)
    (hleft : left ≠ Tree.Null)
    (hright : right ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hheight : height left = height right) :
    ∀ out : Tree, subtree_with_all_deepest root = ok out → out = root := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (x : Std.I64) (left right : Tree)
    (hroot : root = Tree.Node x left right)
    (hleft : left ≠ Tree.Null)
    (hright : right ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hheight : height left = height right), ∀ out : Tree, subtree_with_all_deepest root = ok out → out = root) := by
  sorry

/-- Whenever the function returns a result out, out is exactly the subtree of left rooted at the lowest common ancestor, within left, of all deepest nodes of left.
  Preconditions: root = Tree.Node(x, left, right) with left ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; all node values in root are pairwise distinct; and height(left) > height(right), where height(Tree.Null) = -1 and height(Tree.Node(_, a, b)) = 1 + max(height(a), height(b)). -/
theorem spec_11 (root : Tree) (x : Std.I64) (left right : Tree)
    (hroot : root = Tree.Node x left right)
    (hleft : left ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hheight : height left > height right) :
    ∀ out : Tree, subtree_with_all_deepest root = ok out → IsSubtreeAtLCAOfDeepest left out := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (x : Std.I64) (left right : Tree)
    (hroot : root = Tree.Node x left right)
    (hleft : left ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hheight : height left > height right), ∀ out : Tree, subtree_with_all_deepest root = ok out → IsSubtreeAtLCAOfDeepest left out) := by
  sorry

/-- Whenever the function returns a result out, out is exactly the subtree of right rooted at the lowest common ancestor, within right, of all deepest nodes of right.
  Preconditions: root = Tree.Node(x, left, right) with right ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; all node values in root are pairwise distinct; and height(right) > height(left), where height(Tree.Null) = -1 and height(Tree.Node(_, a, b)) = 1 + max(height(a), height(b)). -/
theorem spec_12 (root : Tree) (x : Std.I64) (left right : Tree)
    (hroot : root = Tree.Node x left right)
    (hright : right ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hheight : height right > height left) :
    ∀ out : Tree, subtree_with_all_deepest root = ok out → IsSubtreeAtLCAOfDeepest right out := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (x : Std.I64) (left right : Tree)
    (hroot : root = Tree.Node x left right)
    (hright : right ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root)
    (hheight : height right > height left), ∀ out : Tree, subtree_with_all_deepest root = ok out → IsSubtreeAtLCAOfDeepest right out) := by
  sorry

/-- Whenever the function returns a result out, every integer value occurring in out is an integer in [0,500] and occurs in root.
  Preconditions: root ≠ Tree.Null; root has at most 500 nodes; every node value is an integer in [0,500]; and all node values in root are pairwise distinct. -/
theorem spec_13 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root) :
    ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∀ v ∈ values out, 0 ≤ v ∧ v ≤ 500 ∧ v ∈ values root := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hcount : nodeCount root ≤ 500)
    (hrange : valuesInRange root)
    (hdistinct : valuesDistinct root), ∀ out : Tree,
      subtree_with_all_deepest root = ok out →
        ∀ v ∈ values out, 0 ≤ v ∧ v ≤ 500 ∧ v ∈ values root) := by
  sorry

end AegisSpec.SubtreeWithAllDeepest
