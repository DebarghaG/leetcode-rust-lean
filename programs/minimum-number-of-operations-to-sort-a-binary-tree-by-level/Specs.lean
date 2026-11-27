import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-number-of-operations-to-sort-a-binary-tree-by-level`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.MinimumOperations

namespace AegisSpec.MinimumOperations

def values : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (values l ++ values r)

def nodeCount (t : Tree) : Nat := (values t).length

def maxDepth : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + max (maxDepth l) (maxDepth r)

def height (t : Tree) : Nat := maxDepth t - 1

def level : Tree → Nat → List Int
  | Tree.Null, _ => []
  | Tree.Node v _ _, 0 => [v.val]
  | Tree.Node _ l r, d + 1 => level l d ++ level r d

def IsValidInput (t : Tree) : Prop :=
  t ≠ Tree.Null ∧ nodeCount t ≤ 100000 ∧
    (∀ v ∈ values t, 1 ≤ v ∧ v ≤ 100000) ∧ (values t).Nodup

def invCount : List Int → Nat
  | [] => 0
  | x :: xs => (xs.filter (fun y => y < x)).length + invCount xs

def rankMap (l : List Int) (i : Nat) : Nat := (l.filter (fun x => x < l.getD i 0)).length

def orbit (f : Nat → Nat) (n i : Nat) : List Nat := (List.range n).map (fun k => f^[k] i)

def OrbitMin (f : Nat → Nat) (n i : Nat) : Prop := ∀ j ∈ orbit f n i, i ≤ j

def cycleCount (f : Nat → Nat) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => (orbit f n i).all (fun j => decide (i ≤ j)))).length

def levelCycles (l : List Int) : Nat := cycleCount (rankMap l) l.length

def levelSwaps (l : List Int) : Nat := l.length - levelCycles l

def valueAt : Tree → List Bool → Option Std.I64
  | Tree.Null, _ => none
  | Tree.Node v _ _, [] => some v
  | Tree.Node _ l _, false :: p => valueAt l p
  | Tree.Node _ _ r, true :: p => valueAt r p

def replaceAt : Tree → List Bool → Std.I64 → Tree
  | Tree.Null, _, _ => Tree.Null
  | Tree.Node _ l r, [], w => Tree.Node w l r
  | Tree.Node v l r, false :: p, w => Tree.Node v (replaceAt l p w) r
  | Tree.Node v l r, true :: p, w => Tree.Node v l (replaceAt r p w)

def IsSwap (t t' : Tree) : Prop :=
  ∃ p q : List Bool, ∃ v w : Std.I64,
    p ≠ q ∧ p.length = q.length ∧ valueAt t p = some v ∧ valueAt t q = some w ∧
      t' = replaceAt (replaceAt t p w) q v

def SwapReach : Nat → Tree → Tree → Prop
  | 0, t, t' => t' = t
  | n + 1, t, t' => ∃ u : Tree, SwapReach n t u ∧ IsSwap u t'

def LevelsIncreasing (t : Tree) : Prop := ∀ d, (level t d).Pairwise (· < ·)

def SameLevelOrder (t1 t2 : Tree) : Prop :=
  ∀ d, (level t1 d).length = (level t2 d).length ∧
    ∀ i j : Nat, i < (level t1 d).length → j < (level t1 d).length →
      (((level t1 d)[i]! < (level t1 d)[j]!) ↔ ((level t2 d)[i]! < (level t2 d)[j]!))

/-- The function returns a result r (it does not fail). Let h be the maximum depth of a node of root, with the root at depth 0. For each d with 0 <= d <= h, let L_d be the list of values of the nodes at depth d in left-to-right order, let m_d = len(L_d), and let pi_d be the permutation of {0,...,m_d-1} sending i to the number of j with 0 <= j < m_d and L_d[j] < L_d[i]. Let c_d be the number of cycles of pi_d. Then r = sum_{d=0}^{h} (m_d - c_d). Equivalently, r is the minimum total number of same-level swaps needed so that, at every depth d, the values in left-to-right order are strictly increasing.
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_1 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val = ∑ d ∈ Finset.range (height root + 1), (levelSwaps (level root d) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val = ∑ d ∈ Finset.range (height root + 1), (levelSwaps (level root d) : Int)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or run out of bounds on this input.
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_2 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64, minimum_operations root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64, minimum_operations root = ok r) := by
  sorry

/-- The function returns a result r, and r >= 0.
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_3 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64, minimum_operations root = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64, minimum_operations root = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r. Let N be the number of Node constructors in root and let h be the maximum depth of a node of root, with the root at depth 0. Then r <= N - (h + 1).
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_4 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val ≤ (nodeCount root : Int) - ((height root : Int) + 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val ≤ (nodeCount root : Int) - ((height root : Int) + 1)) := by
  sorry

/-- The function returns a result r. Let h be the maximum depth of a node of root, and for each d with 0 <= d <= h let L_d be the list of values of nodes at depth d in left-to-right order. Then r = 0 if and only if for every d with 0 <= d <= h and every i with 0 <= i < len(L_d) - 1, L_d[i] < L_d[i + 1].
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_5 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        (r.val = 0 ↔
          ∀ d, d ≤ height root → ∀ i : Nat, i + 1 < (level root d).length →
            (level root d)[i]! < (level root d)[i + 1]!) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        (r.val = 0 ↔
          ∀ d, d ≤ height root → ∀ i : Nat, i + 1 < (level root d).length →
            (level root d)[i]! < (level root d)[i + 1]!)) := by
  sorry

/-- The function returns a result r, and there exists a sequence of exactly r same-level swaps (each swap exchanges the values of two distinct nodes at the same depth) after which every level list of the resulting tree, in left-to-right order, is strictly increasing.
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_6 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        ∃ n : Nat, r.val = (n : Int) ∧
          ∃ t' : Tree, SwapReach n root t' ∧ LevelsIncreasing t' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        ∃ n : Nat, r.val = (n : Int) ∧
          ∃ t' : Tree, SwapReach n root t' ∧ LevelsIncreasing t') := by
  sorry

/-- The function returns a result r, and for every k with 0 <= k < r there is no sequence of k same-level swaps (each exchanging the values of two distinct nodes at the same depth) after which every level list of the resulting tree is strictly increasing.
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_7 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        ∀ k : Nat, (k : Int) < r.val →
          ∀ t' : Tree, ¬ (SwapReach k root t' ∧ LevelsIncreasing t') := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        ∀ k : Nat, (k : Int) < r.val →
          ∀ t' : Tree, ¬ (SwapReach k root t' ∧ LevelsIncreasing t')) := by
  sorry

/-- The function returns a result r. Let h be the maximum depth of a node of root, and for each d with 0 <= d <= h let L_d be the list of values of nodes at depth d in left-to-right order. For a list a let inv(a) be the number of pairs (i,j) with 0 <= i < j < len(a) and a[i] > a[j]. Then r mod 2 = (sum_{d=0}^{h} inv(L_d)) mod 2.
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_8 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val % 2 = (∑ d ∈ Finset.range (height root + 1), (invCount (level root d) : Int)) % 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val % 2 = (∑ d ∈ Finset.range (height root + 1), (invCount (level root d) : Int)) % 2) := by
  sorry

/-- The function returns results r1 for root1 and r2 for root2. For a tree t and each d >= 0, let L_d(t) be the list of values of nodes at depth d in left-to-right order. If for every d >= 0 the lists L_d(root1) and L_d(root2) have the same length and, for all i,j with 0 <= i,j < that common length, L_d(root1)[i] < L_d(root1)[j] if and only if L_d(root2)[i] < L_d(root2)[j], then r1 = r2.
  Preconditions: root1 and root2 are both non-null finite Trees with at most 100000 nodes; every Node value in each tree is an integer v with 1 <= v <= 100000; all node values within root1 are pairwise distinct, and all node values within root2 are pairwise distinct. -/
theorem spec_9 (root1 root2 : Tree) (hvalid1 : IsValidInput root1)
    (hvalid2 : IsValidInput root2) :
    ∃ r1 r2 : Std.I64,
      minimum_operations root1 = ok r1 ∧ minimum_operations root2 = ok r2 ∧
        (SameLevelOrder root1 root2 → r1 = r2) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root1 root2 : Tree) (hvalid1 : IsValidInput root1)
    (hvalid2 : IsValidInput root2), ∃ r1 r2 : Std.I64,
      minimum_operations root1 = ok r1 ∧ minimum_operations root2 = ok r2 ∧
        (SameLevelOrder root1 root2 → r1 = r2)) := by
  sorry

/-- The function returns a result r. Let h be the maximum depth of a node of root. Then r is the number of depths d with 0 <= d <= h such that len(L_d(root)) = 2 and L_d(root)[0] > L_d(root)[1].
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct; and for every d >= 0, len(L_d(root)) <= 2, where L_d(root) is the list of values of nodes at depth d in left-to-right order. -/
theorem spec_10 (root : Tree) (hvalid : IsValidInput root)
    (hshape : ∀ d, (level root d).length ≤ 2) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val = (((List.range (height root + 1)).filter
              (fun d => (level root d).length = 2 ∧ (level root d)[0]! > (level root d)[1]!)).length :
            Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root)
    (hshape : ∀ d, (level root d).length ≤ 2), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val = (((List.range (height root + 1)).filter
              (fun d => (level root d).length = 2 ∧ (level root d)[0]! > (level root d)[1]!)).length :
            Int)) := by
  sorry

/-- The function returns a result r. Let h be the maximum depth of a node of root, and for each d with 0 <= d <= h let L_d be the list of values of nodes at depth d in left-to-right order. For a list a let inv(a) be the number of pairs (i,j) with 0 <= i < j < len(a) and a[i] > a[j]. Then r <= sum_{d=0}^{h} inv(L_d).
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_11 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val ≤ ∑ d ∈ Finset.range (height root + 1), (invCount (level root d) : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        r.val ≤ ∑ d ∈ Finset.range (height root + 1), (invCount (level root d) : Int)) := by
  sorry

/-- The function returns a result r. Let h be the maximum depth of a node of root. For each d with 0 <= d <= h, let L_d be the list of values of nodes at depth d in left-to-right order, let m_d = len(L_d), and let c_d be the number of cycles of the permutation of {0,...,m_d-1} sending i to the number of j with 0 <= j < m_d and L_d[j] < L_d[i]. Then r >= m_d - c_d for every such d.
  Preconditions: root is a non-null finite Tree with at most 100000 nodes; every Node value is an integer v with 1 <= v <= 100000; all node values in root are pairwise distinct. -/
theorem spec_12 (root : Tree) (hvalid : IsValidInput root) :
    ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        ∀ d, d ≤ height root →
          ((level root d).length : Int) - (levelCycles (level root d) : Int) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (hvalid : IsValidInput root), ∃ r : Std.I64,
      minimum_operations root = ok r ∧
        ∀ d, d ≤ height root →
          ((level root d).length : Int) - (levelCycles (level root d) : Int) ≤ r.val) := by
  sorry

end AegisSpec.MinimumOperations
