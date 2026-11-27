import Aegis.FlipMatchVoyage.Code.Funs

/-!
# Specifications of `Aegis.FlipMatchVoyage.flip_match_voyage`

LeetCode problem `flip-binary-tree-to-match-preorder-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FlipMatchVoyage

namespace AegisSpec.FlipMatchVoyage

def treeSize : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => treeSize l + treeSize r + 1

def treePre : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (treePre l ++ treePre r)

def OccursIn (x : Int) (t : Tree) : Prop := x ∈ treePre t

def flipTree (S : List Int) : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r =>
      if v.val ∈ S then Tree.Node v (flipTree S r) (flipTree S l)
      else Tree.Node v (flipTree S l) (flipTree S r)

def IsFlipSol (root : Tree) (voyage : List Int) (S : List Int) : Prop :=
  S.Nodup ∧ (∀ x ∈ S, OccursIn x root) ∧ treePre (flipTree S root) = voyage

def MinFlipSize (root : Tree) (voyage : List Int) (m : Nat) : Prop :=
  (∃ S : List Int, IsFlipSol root voyage S ∧ S.length = m) ∧
    ∀ S : List Int, IsFlipSol root voyage S → m ≤ S.length

def IsMinFlipSol (root : Tree) (voyage : List Int) (S : List Int) : Prop :=
  IsFlipSol root voyage S ∧ MinFlipSize root voyage S.length

def findNodeAt (x : Int) : Tree → Option Tree
  | Tree.Null => none
  | Tree.Node v l r =>
      if v.val = x then some (Tree.Node v l r)
      else
        match findNodeAt x l with
        | some t => some t
        | none => findNodeAt x r

def HasTwoNonemptyChildren (x : Int) (t : Tree) : Prop :=
  ∃ (v : I64) (l r : Tree),
    findNodeAt x t = some (Tree.Node v l r) ∧ v.val = x ∧ l ≠ Tree.Null ∧ r ≠ Tree.Null

def sliceVals (s : Slice I64) : List Int := s.val.map (fun e => e.val)

def vecVals (v : alloc.vec.Vec I64) : List Int := v.val.map (fun e => e.val)

/-- Define vals(T) as the set of node values of T. Define pre(T) as the preorder traversal of T: pre(Null) = [], and pre(Node(v,L,R)) = [v] followed by pre(L) followed by pre(R). For S subseteq vals(root), define flip(T,S) as the tree obtained from T by swapping the left and right children at exactly those nodes whose values belong to S. A swap at a node with fewer than two children does not change the preorder traversal. Whenever the function returns Ok r: (1) if there exists S subseteq vals(root) with pre(flip(root,S)) = voyage, let m = min { |S| : S subseteq vals(root) and pre(flip(root,S)) = voyage }; then r is a list whose entries are exactly the elements of some S_min subseteq vals(root) for which pre(flip(root,S_min)) = voyage and |S_min| = m, in any order, with no repeated entries; (2) if no such S exists, then r = [-1].
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_1 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r →
      ((∃ S : List Int, IsFlipSol root (sliceVals voyage) S) →
        ∃ S : List Int, IsMinFlipSol root (sliceVals voyage) S ∧
          (vecVals r).Nodup ∧ (vecVals r).Perm S) ∧
      ((¬ ∃ S : List Int, IsFlipSol root (sliceVals voyage) S) → vecVals r = [-1]) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r →
      ((∃ S : List Int, IsFlipSol root (sliceVals voyage) S) →
        ∃ S : List Int, IsMinFlipSol root (sliceVals voyage) S ∧
          (vecVals r).Nodup ∧ (vecVals r).Perm S) ∧
      ((¬ ∃ S : List Int, IsFlipSol root (sliceVals voyage) S) → vecVals r = [-1])) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_2 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup) :
    ∃ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup), ∃ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r) := by
  sorry

/-- Let pre(T) be the preorder traversal of T, and for a set S of node values let flip(root,S) be root after swapping left and right children at exactly the nodes whose values are in S. Whenever the function returns a result r, r = [-1] if and only if there is no set S of node values of root such that pre(flip(root,S)) = voyage.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_3 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r →
      (vecVals r = [-1] ↔ ¬ ∃ S : List Int, IsFlipSol root (sliceVals voyage) S) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r →
      (vecVals r = [-1] ↔ ¬ ∃ S : List Int, IsFlipSol root (sliceVals voyage) S)) := by
  sorry

/-- Let pre(T) be the preorder traversal of T, and for a set S of node values let flip(root,S) be root after swapping left and right children at exactly the nodes whose values are in S. Whenever the function returns a result r with r != [-1], every entry of r is the value of a node of root, and if S_r is the set of values occurring in r, then pre(flip(root,S_r)) = voyage.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_4 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      (∀ x ∈ vecVals r, OccursIn x root) ∧
        treePre (flipTree (vecVals r) root) = sliceVals voyage := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      (∀ x ∈ vecVals r, OccursIn x root) ∧
        treePre (flipTree (vecVals r) root) = sliceVals voyage) := by
  sorry

/-- Let pre(T) be the preorder traversal of T, and for a set S of node values let flip(root,S) be root after swapping left and right children at exactly the nodes whose values are in S. Suppose there exists a set S of node values of root with pre(flip(root,S)) = voyage. Whenever the function returns a result r with r != [-1], len(r) = min { |S| : S is a set of node values of root and pre(flip(root,S)) = voyage }.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_5 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup)
    (hexists : ∃ S : List Int, IsFlipSol root (sliceVals voyage) S) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      MinFlipSize root (sliceVals voyage) (vecVals r).length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup)
    (hexists : ∃ S : List Int, IsFlipSol root (sliceVals voyage) S), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      MinFlipSize root (sliceVals voyage) (vecVals r).length) := by
  sorry

/-- Let pre(T) be the preorder traversal of T. Whenever the function returns a result r, r = [] if and only if pre(root) = voyage.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_6 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r →
      (vecVals r = [] ↔ treePre root = sliceVals voyage) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r →
      (vecVals r = [] ↔ treePre root = sliceVals voyage)) := by
  sorry

/-- If root = Node(v,L,R) and the function returns a result r with r != [-1], then voyage[0] = v.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_7 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup)
    (v : I64) (L R : Tree) (hroot : root = Tree.Node v L R) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      ∃ tl : List Int, sliceVals voyage = v.val :: tl := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup)
    (v : I64) (L R : Tree) (hroot : root = Tree.Node v L R), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      ∃ tl : List Int, sliceVals voyage = v.val :: tl) := by
  sorry

/-- Let pre(T) be the preorder traversal of T, and for a set S of node values let flip(root,S) be root after swapping left and right children at exactly the nodes whose values are in S. Whenever the function returns a result r with r != [-1], let S_r be the set of values occurring in r. For every x in S_r, pre(flip(root, S_r without x)) != voyage.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_8 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      ∀ x ∈ vecVals r, treePre (flipTree ((vecVals r).erase x) root) ≠ sliceVals voyage := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      ∀ x ∈ vecVals r, treePre (flipTree ((vecVals r).erase x) root) ≠ sliceVals voyage) := by
  sorry

/-- Whenever the function returns a result r with r != [-1], for every value x occurring in r, the node of root whose value is x has two nonempty children.
  Preconditions: Let n = len(voyage). root has exactly n nodes, n >= 1 and n <= 100; every node value and every voyage entry lies in {1,...,n}; all node values are distinct; all voyage entries are distinct (hence voyage is a permutation of the node values). -/
theorem spec_9 (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup) :
    ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      ∀ x ∈ vecVals r, HasTwoNonemptyChildren x root := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (voyage : Slice I64)
    (hnodes : treeSize root = (sliceVals voyage).length)
    (hn_pos : 1 ≤ (sliceVals voyage).length)
    (hn_le : (sliceVals voyage).length ≤ 100)
    (hroot_bounds : ∀ x ∈ treePre root, 1 ≤ x ∧ x ≤ ((sliceVals voyage).length : Int))
    (hvoyage_bounds : ∀ e ∈ sliceVals voyage, 1 ≤ e ∧ e ≤ ((sliceVals voyage).length : Int))
    (hroot_nd : (treePre root).Nodup)
    (hvoyage_nd : (sliceVals voyage).Nodup), ∀ r : alloc.vec.Vec I64, flip_match_voyage root voyage = ok r → vecVals r ≠ [-1] →
      ∀ x ∈ vecVals r, HasTwoNonemptyChildren x root) := by
  sorry

end AegisSpec.FlipMatchVoyage
