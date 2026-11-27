import Aegis.CountSubIslands.Code.Funs

/-!
# Specifications of `Aegis.CountSubIslands.count_sub_islands`

LeetCode problem `count-sub-islands`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountSubIslands

namespace AegisSpec.CountSubIslands

def cell (g : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match g.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def rowWidth (g : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  (g.val.getD i default).val.length

structure GridShape (g : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop where

  len : g.val.length = m

  row : ∀ i, i < m → rowWidth g i = n

  bin : ∀ i, i < m → ∀ j, j < n → cell g i j = 0 ∨ cell g i j = 1

structure GridPre (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop where

  len1 : grid1.val.length = m

  len2 : grid2.val.length = m

  m_pos : 1 ≤ m

  m_le : m ≤ 500

  n_pos : 1 ≤ n

  n_le : n ≤ 500

  row1 : ∀ i, i < m → rowWidth grid1 i = n

  row2 : ∀ i, i < m → rowWidth grid2 i = n

  bin1 : ∀ i, i < m → ∀ j, j < n → cell grid1 i j = 0 ∨ cell grid1 i j = 1

  bin2 : ∀ i, i < m → ∀ j, j < n → cell grid2 i j = 0 ∨ cell grid2 i j = 1

def InRect (m n : Nat) (p : Nat × Nat) : Prop :=
  p.1 < m ∧ p.2 < n

def Adjacent (p q : Nat × Nat) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
    (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

def Step (m n : Nat) (c : Nat → Nat → Int) (p q : Nat × Nat) : Prop :=
  InRect m n p ∧ InRect m n q ∧ c p.1 p.2 = 1 ∧ c q.1 q.2 = 1 ∧ Adjacent p q

def Reach (m n : Nat) (c : Nat → Nat → Int) : Nat × Nat → Nat × Nat → Prop :=
  Relation.ReflTransGen (Step m n c)

def CellLt (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

def IsIslandRoot (m n : Nat) (c : Nat → Nat → Int) (p : Nat × Nat) : Prop :=
  InRect m n p ∧ c p.1 p.2 = 1 ∧ ∀ q, Reach m n c p q → ¬ CellLt q p

def IsSubIslandRoot (m n : Nat) (c1 c2 : Nat → Nat → Int) (p : Nat × Nat) : Prop :=
  IsIslandRoot m n c2 p ∧ ∀ q, Reach m n c2 p q → c1 q.1 q.2 = 1

noncomputable def numIslands (m n : Nat) (c : Nat → Nat → Int) : Nat := by
  classical
  exact (((Finset.range m).product (Finset.range n)).filter (fun p => IsIslandRoot m n c p)).card

noncomputable def numSubIslands (m n : Nat) (c1 c2 : Nat → Nat → Int) : Nat := by
  classical
  exact (((Finset.range m).product (Finset.range n)).filter
    (fun p => IsSubIslandRoot m n c1 c2 p)).card

def EveryIslandHasZero (m n : Nat) (c1 c2 : Nat → Nat → Int) : Prop :=
  ∀ p, IsIslandRoot m n c2 p → ∃ q, Reach m n c2 p q ∧ c1 q.1 q.2 = 0

/-- Consider the graph G2 whose vertices are the pairs (i,j) with 0 <= i < m, 0 <= j < n and grid2[i][j] = 1, and whose edges join (i,j) and (i',j') exactly when |i - i'| + |j - j'| = 1. An island of grid2 is the set of vertices of one connected component of G2. An island C of grid2 is a sub-island if for every (i,j) in C, grid1[i][j] = 1. The function returns a result r and r is exactly the number of sub-islands of grid2.
  Preconditions: Let m = len(grid1) and n = len(grid1[0]). Assume 1 <= m <= 500, 1 <= n <= 500, len(grid2) = m, and for every i with 0 <= i < m, len(grid1[i]) = n and len(grid2[i]) = n. Also assume that for every i,j with 0 <= i < m and 0 <= j < n, grid1[i][j] ∈ {0,1} and grid2[i][j] ∈ {0,1}. -/
theorem spec_1 (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) :
    ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧
        r.val = ((numSubIslands m n (cell grid1) (cell grid2) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n), ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧
        r.val = ((numSubIslands m n (cell grid1) (cell grid2) : Nat) : Int)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let m = len(grid1) and n = len(grid1[0]). Assume 1 <= m <= 500, 1 <= n <= 500, len(grid2) = m, and for every i with 0 <= i < m, len(grid1[i]) = n and len(grid2[i]) = n. Also assume that for every i,j with 0 <= i < m and 0 <= j < n, grid1[i][j] ∈ {0,1} and grid2[i][j] ∈ {0,1}. -/
theorem spec_2 (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) :
    ∃ r : Std.I64, count_sub_islands grid1 grid2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n), ∃ r : Std.I64, count_sub_islands grid1 grid2 = ok r) := by
  sorry

/-- Let I2 be the number of islands of grid2, where an island is a maximal 4-connected set of cells (i,j) with grid2[i][j] = 1. The function returns a result r and r <= I2.
  Preconditions: Let m = len(grid1) and n = len(grid1[0]). Assume 1 <= m <= 500, 1 <= n <= 500, len(grid2) = m, and for every i with 0 <= i < m, len(grid1[i]) = n and len(grid2[i]) = n. Also assume that for every i,j with 0 <= i < m and 0 <= j < n, grid1[i][j] ∈ {0,1} and grid2[i][j] ∈ {0,1}. -/
theorem spec_3 (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) :
    ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧
        r.val ≤ ((numIslands m n (cell grid2) : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n), ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧
        r.val ≤ ((numIslands m n (cell grid2) : Nat) : Int)) := by
  sorry

/-- Let grid1' be any matrix of the same shape m x n with entries in {0,1} such that grid1'[i][j] = grid1[i][j] whenever grid2[i][j] = 1. Then the function returns a result r for (grid1, grid2) and the same result r for (grid1', grid2); in other words, count_sub_islands(grid1, grid2) = count_sub_islands(grid1', grid2).
  Preconditions: Let m = len(grid1) and n = len(grid1[0]). Assume 1 <= m <= 500, 1 <= n <= 500, len(grid2) = m, and for every i with 0 <= i < m, len(grid1[i]) = n and len(grid2[i]) = n. Also assume that for every i,j with 0 <= i < m and 0 <= j < n, grid1[i][j] ∈ {0,1} and grid2[i][j] ∈ {0,1}. -/
theorem spec_4 (grid1 grid2 grid1' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) (h' : GridShape grid1' m n)
    (hagree : ∀ i j, i < m → j < n → cell grid2 i j = 1 → cell grid1' i j = cell grid1 i j) :
    ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧ count_sub_islands grid1' grid2 = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid1 grid2 grid1' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) (h' : GridShape grid1' m n)
    (hagree : ∀ i j, i < m → j < n → cell grid2 i j = 1 → cell grid1' i j = cell grid1 i j), ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧ count_sub_islands grid1' grid2 = ok r) := by
  sorry

/-- Let grid1' be any matrix of the same shape m x n with entries in {0,1} such that grid1'[i][j] >= grid1[i][j] for every i,j. Let r = count_sub_islands(grid1, grid2) and r' = count_sub_islands(grid1', grid2). Then both calls return results and r' >= r.
  Preconditions: Let m = len(grid1) and n = len(grid1[0]). Assume 1 <= m <= 500, 1 <= n <= 500, len(grid2) = m, and for every i with 0 <= i < m, len(grid1[i]) = n and len(grid2[i]) = n. Also assume that for every i,j with 0 <= i < m and 0 <= j < n, grid1[i][j] ∈ {0,1} and grid2[i][j] ∈ {0,1}. -/
theorem spec_5 (grid1 grid2 grid1' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) (h' : GridShape grid1' m n)
    (hge : ∀ i j, i < m → j < n → cell grid1 i j ≤ cell grid1' i j) :
    ∃ r r' : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧ count_sub_islands grid1' grid2 = ok r' ∧
        r.val ≤ r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid1 grid2 grid1' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) (h' : GridShape grid1' m n)
    (hge : ∀ i j, i < m → j < n → cell grid1 i j ≤ cell grid1' i j), ∃ r r' : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧ count_sub_islands grid1' grid2 = ok r' ∧
        r.val ≤ r'.val) := by
  sorry

/-- Let grid1^T and grid2^T be the transposes of grid1 and grid2, so grid1^T[j][i] = grid1[i][j] and grid2^T[j][i] = grid2[i][j] for all i,j. Then the function returns a result r for (grid1, grid2) and also returns r for (grid1^T, grid2^T).
  Preconditions: Let m = len(grid1) and n = len(grid1[0]). Assume 1 <= m <= 500, 1 <= n <= 500, len(grid2) = m, and for every i with 0 <= i < m, len(grid1[i]) = n and len(grid2[i]) = n. Also assume that for every i,j with 0 <= i < m and 0 <= j < n, grid1[i][j] ∈ {0,1} and grid2[i][j] ∈ {0,1}. -/
theorem spec_6 (grid1 grid2 grid1T grid2T : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) (hT1 : GridShape grid1T n m) (hT2 : GridShape grid2T n m)
    (hcell1 : ∀ i j, i < m → j < n → cell grid1T j i = cell grid1 i j)
    (hcell2 : ∀ i j, i < m → j < n → cell grid2T j i = cell grid2 i j) :
    ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧ count_sub_islands grid1T grid2T = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid1 grid2 grid1T grid2T : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) (hT1 : GridShape grid1T n m) (hT2 : GridShape grid2T n m)
    (hcell1 : ∀ i j, i < m → j < n → cell grid1T j i = cell grid1 i j)
    (hcell2 : ∀ i j, i < m → j < n → cell grid2T j i = cell grid2 i j), ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧ count_sub_islands grid1T grid2T = ok r) := by
  sorry

/-- The function returns a result r and r = 0 if and only if every island of grid2 contains at least one cell (i,j) with grid1[i][j] = 0. If grid2 has no islands, this condition is vacuously true.
  Preconditions: Let m = len(grid1) and n = len(grid1[0]). Assume 1 <= m <= 500, 1 <= n <= 500, len(grid2) = m, and for every i with 0 <= i < m, len(grid1[i]) = n and len(grid2[i]) = n. Also assume that for every i,j with 0 <= i < m and 0 <= j < n, grid1[i][j] ∈ {0,1} and grid2[i][j] ∈ {0,1}. -/
theorem spec_7 (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n) :
    ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧
        (r.val = 0 ↔ EveryIslandHasZero m n (cell grid1) (cell grid2)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid1 grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : GridPre grid1 grid2 m n), ∃ r : Std.I64,
      count_sub_islands grid1 grid2 = ok r ∧
        (r.val = 0 ↔ EveryIslandHasZero m n (cell grid1) (cell grid2))) := by
  sorry

end AegisSpec.CountSubIslands
