import Aegis.LcaDeepestLeaves.Code.Funs

/-!
# Specifications of `Aegis.LcaDeepestLeaves.lca_deepest_leaves`

LeetCode problem `lowest-common-ancestor-of-deepest-leaves`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LcaDeepestLeaves

open Aegis.LcaDeepestLeaves

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

def nodeValues : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (nodeValues l ++ nodeValues r)

def ValuesInRange (t : Tree) (lo hi : Int) : Prop :=
  ∀ x ∈ nodeValues t, lo ≤ x ∧ x ≤ hi

def ValuesDistinct (t : Tree) : Prop :=
  (nodeValues t).Nodup

def subtreeAt (t : Tree) (p : List Bool) : Option Tree :=
  match p with
  | [] => some t
  | b :: rest =>
    match t with
    | Tree.Null => none
    | Tree.Node _ l r => subtreeAt (if b then r else l) rest

def IsNodeAt (t : Tree) (p : List Bool) : Prop :=
  ∃ (v : I64) (l r : Tree), subtreeAt t p = some (Tree.Node v l r)

def IsLeafAt (t : Tree) (p : List Bool) : Prop :=
  ∃ v, subtreeAt t p = some (Tree.Node v Tree.Null Tree.Null)

def IsMaxLeafDepth (t : Tree) (M : Nat) : Prop :=
  (∃ p, IsLeafAt t p ∧ p.length = M) ∧ ∀ p, IsLeafAt t p → p.length ≤ M

def IsDeepestLeafAt (t : Tree) (p : List Bool) : Prop :=
  IsLeafAt t p ∧ ∀ q, IsLeafAt t q → q.length ≤ p.length

def IsDeepestLcaAt (t : Tree) (p : List Bool) : Prop :=
  IsNodeAt t p ∧
    (∀ q, IsDeepestLeafAt t q → p <+: q) ∧
    (∀ p', IsNodeAt t p' → (∀ q, IsDeepestLeafAt t q → p' <+: q) → p'.length ≤ p.length) ∧
    (∀ p', IsNodeAt t p' → (∀ q, IsDeepestLeafAt t q → p' <+: q) → p'.length = p.length →
      p' = p)

def UniqueDeepestLeafAt (t : Tree) (p : List Bool) (v : I64) : Prop :=
  subtreeAt t p = some (Tree.Node v Tree.Null Tree.Null) ∧
    IsDeepestLeafAt t p ∧
    ∀ (q : List Bool) (w : I64), subtreeAt t q = some (Tree.Node w Tree.Null Tree.Null) →
      IsDeepestLeafAt t q → q = p

def HasExactlyOneDeepestLeaf (t : Tree) : Prop :=
  ∃ (p : List Bool) (v : I64), UniqueDeepestLeafAt t p v

def AllDeepestLeavesLeft (t : Tree) : Prop :=
  ∀ q, IsDeepestLeafAt t q → ∃ q', q = false :: q'

def AllDeepestLeavesRight (t : Tree) : Prop :=
  ∀ q, IsDeepestLeafAt t q → ∃ q', q = true :: q'

def SomeDeepestLeafLeft (t : Tree) : Prop :=
  ∃ q', IsDeepestLeafAt t (false :: q')

def SomeDeepestLeafRight (t : Tree) : Prop :=
  ∃ q', IsDeepestLeafAt t (true :: q')

/-- Let a leaf of root be a node occurrence Tree.Node(v, Tree.Null, Tree.Null); let the depth of a node be the number of edges from root to it; let M be the maximum depth of a leaf of root; let D be the set of leaf occurrences of root with depth M (D is nonempty because root is non-null); and let A be the unique node of root of maximum depth whose subtree contains every node of D (equivalently, the lowest common ancestor of D). Then lca_deepest_leaves root returns Result.ok r, where r is exactly the subtree of root rooted at A: r has the value of A at its root and contains precisely A and all descendants of A, preserving the same left/right child structure and node values.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct. -/
theorem spec_1 (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root) :
    ∃ (p : List Bool) (r : Tree),
      IsDeepestLcaAt root p ∧ subtreeAt root p = some r ∧
        lca_deepest_leaves root = Result.ok r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root), ∃ (p : List Bool) (r : Tree),
      IsDeepestLcaAt root p ∧ subtreeAt root p = some r ∧
        lca_deepest_leaves root = Result.ok r) := by
  sorry

/-- lca_deepest_leaves root does not fail: there exists a Tree r such that lca_deepest_leaves root = Result.ok r.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct. -/
theorem spec_2 (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root) :
    ∃ r : Tree, lca_deepest_leaves root = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root), ∃ r : Tree, lca_deepest_leaves root = Result.ok r) := by
  sorry

/-- Whenever lca_deepest_leaves root = Result.ok r, r is not Tree.Null; that is, the returned tree always has at least one node.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct. -/
theorem spec_3 (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root) :
    ∀ r : Tree, lca_deepest_leaves root = Result.ok r → r ≠ Tree.Null := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root), ∀ r : Tree, lca_deepest_leaves root = Result.ok r → r ≠ Tree.Null) := by
  sorry

/-- lca_deepest_leaves root returns Result.ok r with r = Tree.Node(v, Tree.Null, Tree.Null).
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct; and root has exactly one leaf at the maximum leaf depth. Let x be that leaf occurrence and let v be its value. -/
theorem spec_4 (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root) :
    ∃ (p : List Bool) (v : I64),
      UniqueDeepestLeafAt root p v ∧
        lca_deepest_leaves root = Result.ok (Tree.Node v Tree.Null Tree.Null) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root), ∃ (p : List Bool) (v : I64),
      UniqueDeepestLeafAt root p v ∧
        lca_deepest_leaves root = Result.ok (Tree.Node v Tree.Null Tree.Null)) := by
  sorry

/-- lca_deepest_leaves root returns Result.ok r with r = Tree.Node(v, L, R), which is exactly the input tree root.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct; root = Tree.Node(v, L, R); L and R are not Tree.Null; and among the deepest leaves of root there is at least one node in L and at least one node in R. -/
theorem spec_5 (root : Tree) (n : Nat) (v : I64) (L R : Tree)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_root : root = Tree.Node v L R) (hL : L ≠ Tree.Null) (hR : R ≠ Tree.Null)
    (h_left : SomeDeepestLeafLeft root) (h_right : SomeDeepestLeafRight root) :
    lca_deepest_leaves root = Result.ok (Tree.Node v L R) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (n : Nat) (v : I64) (L R : Tree)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_root : root = Tree.Node v L R) (hL : L ≠ Tree.Null) (hR : R ≠ Tree.Null)
    (h_left : SomeDeepestLeafLeft root) (h_right : SomeDeepestLeafRight root), lca_deepest_leaves root = Result.ok (Tree.Node v L R)) := by
  sorry

/-- lca_deepest_leaves root returns Result.ok r where r is exactly the subtree of L rooted at the lowest common ancestor, computed inside L, of the deepest leaves of L; equivalently r is the answer required by this same specification when the input is L.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct; root = Tree.Node(v, L, R); L is not Tree.Null; and every deepest leaf of root lies in L, so no deepest leaf of root lies in R. -/
theorem spec_6 (root : Tree) (n : Nat) (v : I64) (L R : Tree)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_root : root = Tree.Node v L R) (hL : L ≠ Tree.Null)
    (h_all_left : AllDeepestLeavesLeft root) :
    ∃ (p : List Bool) (r : Tree),
      IsDeepestLcaAt L p ∧ subtreeAt L p = some r ∧ lca_deepest_leaves root = Result.ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (n : Nat) (v : I64) (L R : Tree)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_root : root = Tree.Node v L R) (hL : L ≠ Tree.Null)
    (h_all_left : AllDeepestLeavesLeft root), ∃ (p : List Bool) (r : Tree),
      IsDeepestLcaAt L p ∧ subtreeAt L p = some r ∧ lca_deepest_leaves root = Result.ok r) := by
  sorry

/-- lca_deepest_leaves root returns Result.ok r where r is exactly the subtree of R rooted at the lowest common ancestor, computed inside R, of the deepest leaves of R; equivalently r is the answer required by this same specification when the input is R.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct; root = Tree.Node(v, L, R); R is not Tree.Null; and every deepest leaf of root lies in R, so no deepest leaf of root lies in L. -/
theorem spec_7 (root : Tree) (n : Nat) (v : I64) (L R : Tree)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_root : root = Tree.Node v L R) (hR : R ≠ Tree.Null)
    (h_all_right : AllDeepestLeavesRight root) :
    ∃ (p : List Bool) (r : Tree),
      IsDeepestLcaAt R p ∧ subtreeAt R p = some r ∧ lca_deepest_leaves root = Result.ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (n : Nat) (v : I64) (L R : Tree)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_root : root = Tree.Node v L R) (hR : R ≠ Tree.Null)
    (h_all_right : AllDeepestLeavesRight root), ∃ (p : List Bool) (r : Tree),
      IsDeepestLcaAt R p ∧ subtreeAt R p = some r ∧ lca_deepest_leaves root = Result.ok r) := by
  sorry

/-- Whenever lca_deepest_leaves root = Result.ok r, every deepest leaf of root occurs as a leaf node of r with the same value; here a deepest leaf is a leaf (node with two Tree.Null children) whose depth, the number of edges from root, is maximum among all leaves of root.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct. -/
theorem spec_8 (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root) :
    ∀ r : Tree, lca_deepest_leaves root = Result.ok r →
      ∀ q : List Bool, IsDeepestLeafAt root q →
        ∃ (q' : List Bool) (w : I64),
          subtreeAt root q = some (Tree.Node w Tree.Null Tree.Null) ∧
            subtreeAt r q' = some (Tree.Node w Tree.Null Tree.Null) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root), ∀ r : Tree, lca_deepest_leaves root = Result.ok r →
      ∀ q : List Bool, IsDeepestLeafAt root q →
        ∃ (q' : List Bool) (w : I64),
          subtreeAt root q = some (Tree.Node w Tree.Null Tree.Null) ∧
            subtreeAt r q' = some (Tree.Node w Tree.Null Tree.Null)) := by
  sorry

/-- Whenever lca_deepest_leaves root = Result.ok r and r = Tree.Node(a, Lr, Rr) is not a leaf, both Lr and Rr are not Tree.Null and each of Lr and Rr contains at least one deepest leaf of root; equivalently, no proper immediate child subtree of the root of r contains all deepest leaves of root.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct. -/
theorem spec_9 (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root) :
    ∀ (p : List Bool) (a : I64) (Lr Rr : Tree),
      lca_deepest_leaves root = Result.ok (Tree.Node a Lr Rr) →
        subtreeAt root p = some (Tree.Node a Lr Rr) →
          ¬ (Lr = Tree.Null ∧ Rr = Tree.Null) →
            Lr ≠ Tree.Null ∧ Rr ≠ Tree.Null ∧
              (∃ q, IsDeepestLeafAt root q ∧ (p ++ [false]) <+: q) ∧
              (∃ q, IsDeepestLeafAt root q ∧ (p ++ [true]) <+: q) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root), ∀ (p : List Bool) (a : I64) (Lr Rr : Tree),
      lca_deepest_leaves root = Result.ok (Tree.Node a Lr Rr) →
        subtreeAt root p = some (Tree.Node a Lr Rr) →
          ¬ (Lr = Tree.Null ∧ Rr = Tree.Null) →
            Lr ≠ Tree.Null ∧ Rr ≠ Tree.Null ∧
              (∃ q, IsDeepestLeafAt root q ∧ (p ++ [false]) <+: q) ∧
              (∃ q, IsDeepestLeafAt root q ∧ (p ++ [true]) <+: q)) := by
  sorry

/-- Whenever lca_deepest_leaves root = Result.ok r and r = Tree.Node(a, Lr, Rr), let A be the unique node of root with value a and let M be the maximum depth of a leaf of root. Then the depth of A is at most M; moreover the depth of A equals M if and only if root has exactly one deepest leaf, and in that case r = Tree.Node(a, Tree.Null, Tree.Null).
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct. -/
theorem spec_10 (root : Tree) (n : Nat) (M : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_M : IsMaxLeafDepth root M) :
    ∀ (a : I64) (Lr Rr : Tree),
      lca_deepest_leaves root = Result.ok (Tree.Node a Lr Rr) →
        ∃ p : List Bool,
          subtreeAt root p = some (Tree.Node a Lr Rr) ∧
            (∀ (p' : List Bool) (s1 s2 : Tree),
              subtreeAt root p' = some (Tree.Node a s1 s2) → p' = p) ∧
            p.length ≤ M ∧
            (p.length = M ↔ HasExactlyOneDeepestLeaf root) ∧
            (p.length = M → Lr = Tree.Null ∧ Rr = Tree.Null) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (n : Nat) (M : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root)
    (h_M : IsMaxLeafDepth root M), ∀ (a : I64) (Lr Rr : Tree),
      lca_deepest_leaves root = Result.ok (Tree.Node a Lr Rr) →
        ∃ p : List Bool,
          subtreeAt root p = some (Tree.Node a Lr Rr) ∧
            (∀ (p' : List Bool) (s1 s2 : Tree),
              subtreeAt root p' = some (Tree.Node a s1 s2) → p' = p) ∧
            p.length ≤ M ∧
            (p.length = M ↔ HasExactlyOneDeepestLeaf root) ∧
            (p.length = M → Lr = Tree.Null ∧ Rr = Tree.Null)) := by
  sorry

/-- Whenever lca_deepest_leaves root = Result.ok r = Tree.Node(a, Lr, Rr), the value a occurs at a unique node A of root, and r is exactly the subtree of root rooted at A: for every node of r there is a corresponding node of root in the subtree rooted at A (including A itself) with the same sequence of left/right moves from A and the same value; conversely, for every node in the subtree of root rooted at A there is a corresponding node of r with the same relative path and value. Thus r is literally a subtree of root, not a different tree with the same root value.
  Preconditions: root is a finite, non-null binary tree with n nodes, 1 <= n <= 1000; every node value is an integer in [0,1000]; all node values in root are pairwise distinct. -/
theorem spec_11 (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root) :
    ∀ (a : I64) (Lr Rr : Tree),
      lca_deepest_leaves root = Result.ok (Tree.Node a Lr Rr) →
        ∃ p : List Bool,
          subtreeAt root p = some (Tree.Node a Lr Rr) ∧
            (∀ (p' : List Bool) (s1 s2 : Tree),
              subtreeAt root p' = some (Tree.Node a s1 s2) → p' = p) ∧
            (∀ (q : List Bool) (s : Tree),
              subtreeAt (Tree.Node a Lr Rr) q = some s → subtreeAt root (p ++ q) = some s) ∧
            (∀ (q : List Bool) (s : Tree),
              subtreeAt root (p ++ q) = some s → subtreeAt (Tree.Node a Lr Rr) q = some s) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (h_size : nodeCount root = n) (h_pos : 1 ≤ n) (h_bound : n ≤ 1000)
    (h_range : ValuesInRange root 0 1000) (h_distinct : ValuesDistinct root), ∀ (a : I64) (Lr Rr : Tree),
      lca_deepest_leaves root = Result.ok (Tree.Node a Lr Rr) →
        ∃ p : List Bool,
          subtreeAt root p = some (Tree.Node a Lr Rr) ∧
            (∀ (p' : List Bool) (s1 s2 : Tree),
              subtreeAt root p' = some (Tree.Node a s1 s2) → p' = p) ∧
            (∀ (q : List Bool) (s : Tree),
              subtreeAt (Tree.Node a Lr Rr) q = some s → subtreeAt root (p ++ q) = some s) ∧
            (∀ (q : List Bool) (s : Tree),
              subtreeAt root (p ++ q) = some s → subtreeAt (Tree.Node a Lr Rr) q = some s)) := by
  sorry

end AegisSpec.LcaDeepestLeaves
