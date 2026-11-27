import Aegis.InvertTree.Code.Funs

/-!
# Specifications of `Aegis.InvertTree.invert_tree`

LeetCode problem `invert-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.InvertTree (Tree invert invert_tree)

namespace AegisSpec.InvertTree

def nodes : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodes l + nodes r

def height : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + max (height l) (height r)

def leaves : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ Tree.Null Tree.Null => 1
  | Tree.Node _ l r => leaves l + leaves r

def occurrences (x : Int) : Tree → Nat
  | Tree.Null => 0
  | Tree.Node v l r => (if v.val = x then 1 else 0) + occurrences x l + occurrences x r

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

def levelValues : Nat → Tree → List Int
  | _, Tree.Null => []
  | 0, Tree.Node v _ _ => [v.val]
  | d + 1, Tree.Node _ l r => levelValues d l ++ levelValues d r

inductive Dir where
  | L : Dir
  | R : Dir

def Dir.compl : Dir → Dir
  | Dir.L => Dir.R
  | Dir.R => Dir.L

def complPath : List Dir → List Dir :=
  List.map Dir.compl

def validPath : Tree → List Dir → Prop
  | Tree.Null, _ => False
  | Tree.Node _ _ _, [] => True
  | Tree.Node _ l _, Dir.L :: p => validPath l p
  | Tree.Node _ _ r, Dir.R :: p => validPath r p

def valueAt : Tree → List Dir → Option Int
  | Tree.Null, _ => none
  | Tree.Node v _ _, [] => some v.val
  | Tree.Node _ l _, Dir.L :: p => valueAt l p
  | Tree.Node _ _ r, Dir.R :: p => valueAt r p

def allValuesIn (lo hi : Int) (t : Tree) : Prop :=
  ∀ x : Int, 0 < occurrences x t → lo ≤ x ∧ x ≤ hi

/-- Whenever invert_tree root returns Result.ok r, r equals the mirror M(root), where M is defined recursively by M(Null)=Null and M(Node(v,L,R))=Node(v,M(R),M(L)). Equivalently, every node keeps its value, its left and right subtrees are exchanged, and this is done recursively throughout the tree.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_1 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    r = mirror root := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), r = mirror root) := by
  sorry

/-- For every root satisfying the preconditions, invert_tree root returns Result.ok r for some Tree r; it does not fail or raise an error.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_2 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root) :
    ∃ r : Tree, invert_tree root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root), ∃ r : Tree, invert_tree root = ok r) := by
  sorry

/-- Whenever invert_tree root returns Result.ok r, nodes(r)=nodes(root), where nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R).
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_3 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    nodes r = nodes root := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), nodes r = nodes root) := by
  sorry

/-- Whenever invert_tree root returns Result.ok r, for every integer x, occurrences(x,r)=occurrences(x,root), where occurrences(x,T) is the number of nodes in T whose value is x.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_4 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    ∀ x : Int, occurrences x r = occurrences x root := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), ∀ x : Int, occurrences x r = occurrences x root) := by
  sorry

/-- Whenever invert_tree root returns Result.ok r, height(r)=height(root), where height(Null)=0 and height(Node(v,L,R))=1+max(height(L),height(R)); this height counts nodes on a longest root-to-leaf path.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_5 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    height r = height root := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), height r = height root) := by
  sorry

/-- Whenever invert_tree root returns Result.ok r, for every depth d>=0, the list of values of nodes at depth d in r, read left-to-right, is the reverse of the list of values of nodes at depth d in root, read left-to-right. The root has depth 0 and absent children are omitted from the lists.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_6 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    ∀ d : Nat, levelValues d r = (levelValues d root).reverse := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), ∀ d : Nat, levelValues d r = (levelValues d root).reverse) := by
  sorry

/-- Whenever invert_tree root returns Result.ok r, for every finite path p of L/R moves that is valid in root, the path complement(p) is valid in r and value_at(r,complement(p))=value_at(root,p), where complement swaps L and R in every position. A path is valid when starting at the root and following its moves reaches an existing node; the empty path is valid exactly for a non-Null tree, and value_at gives the value of that reached node.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_7 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    ∀ p : List Dir, validPath root p →
      validPath r (complPath p) ∧ valueAt r (complPath p) = valueAt root p := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), ∀ p : List Dir, validPath root p →
      validPath r (complPath p) ∧ valueAt r (complPath p) = valueAt root p) := by
  sorry

/-- Whenever invert_tree root returns Result.ok r, for every finite path p of L/R moves, p is a valid path in r if and only if complement(p) is a valid path in root, where complement swaps L and R in every position. A path is valid when following it from the root reaches an existing node; the empty path is valid exactly for a non-Null tree.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_8 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    ∀ p : List Dir, validPath r p ↔ validPath root (complPath p) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), ∀ p : List Dir, validPath r p ↔ validPath root (complPath p)) := by
  sorry

/-- For every root satisfying the preconditions, whenever invert_tree root returns Result.ok r and invert_tree r returns Result.ok s, we have s=root.
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_9 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) (s : Tree) (hs : invert_tree r = ok s) :
    s = root := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) (s : Tree) (hs : invert_tree r = ok s), s = root) := by
  sorry

/-- Whenever invert_tree root returns Result.ok r, leaves(r)=leaves(root), where leaves(Null)=0, leaves(Node(v,Null,Null))=1, and for a node with at least one child leaves(Node(v,L,R))=leaves(L)+leaves(R).
  Preconditions: root is a finite Tree with at most 100 nodes, and every node value in root lies in [-100,100]. -/
theorem spec_10 (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r) :
    leaves r = leaves root := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (hsize : nodes root ≤ 100) (hvals : allValuesIn (-100) 100 root)
    (r : Tree) (hr : invert_tree root = ok r), leaves r = leaves root) := by
  sorry

end AegisSpec.InvertTree
