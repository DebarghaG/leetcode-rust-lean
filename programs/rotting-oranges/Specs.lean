import Aegis.OrangesRotting.Code.Funs

/-!
# Specifications of `Aegis.OrangesRotting.oranges_rotting`

LeetCode problem `rotting-oranges`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.OrangesRotting

namespace AegisSpec.OrangesRotting

abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

def cellVal (grid : Grid) (i j : Nat) : Option Int :=
  match grid.val[i]? with
  | none => none
  | some row => (row.val[j]?).map (fun v => v.val)

def rowLen (grid : Grid) (i : Nat) : Option Nat :=
  (grid.val[i]?).map (fun row => row.val.length)

def GridValid (grid : Grid) (m n : Nat) : Prop :=
  1 ≤ m ∧ m ≤ 10 ∧ 1 ≤ n ∧ n ≤ 10 ∧
    grid.val.length = m ∧
    (∀ i : Nat, i < m → rowLen grid i = some n) ∧
    (∀ i j : Nat, i < m → j < n →
      ∃ v : Int, cellVal grid i j = some v ∧ (v = 0 ∨ v = 1 ∨ v = 2))

def manhattan (p q : Nat × Nat) : Nat :=
  ((p.1 : Int) - (q.1 : Int)).natAbs + ((p.2 : Int) - (q.2 : Int)).natAbs

def R (grid : Grid) (m n : Nat) : Nat → Set (Nat × Nat)
  | 0 => {p | p.1 < m ∧ p.2 < n ∧ cellVal grid p.1 p.2 = some 2}
  | t + 1 =>
      R grid m n t ∪
        {p | p.1 < m ∧ p.2 < n ∧ cellVal grid p.1 p.2 = some 1 ∧
          ∃ q : Nat × Nat, q ∈ R grid m n t ∧ manhattan q p = 1}

def Fresh (grid : Grid) (m n : Nat) : Set (Nat × Nat) :=
  {p | p.1 < m ∧ p.2 < n ∧ cellVal grid p.1 p.2 = some 1}

def freshCount (grid : Grid) (m n : Nat) : Nat :=
  ((List.range m).map (fun i => (List.range n).countP (fun j => decide (cellVal grid i j = some 1)))).sum

def PathTo (grid : Grid) (m n : Nat) (k : Nat) (c : Nat × Nat) : Prop :=
  ∃ p : Nat → Nat × Nat,
    (p 0).1 < m ∧ (p 0).2 < n ∧ cellVal grid (p 0).1 (p 0).2 = some 2 ∧
      p k = c ∧
      (∀ l : Nat, l ≤ k → (p l).1 < m ∧ (p l).2 < n ∧
        (cellVal grid (p l).1 (p l).2 = some 1 ∨ cellVal grid (p l).1 (p l).2 = some 2)) ∧
      (∀ l : Nat, l < k → manhattan (p l) (p (l + 1)) = 1)

def IsRotTime (grid : Grid) (m n : Nat) (i j k : Nat) : Prop :=
  PathTo grid m n k (i, j) ∧ ∀ k' : Nat, k' < k → ¬ PathTo grid m n k' (i, j)

/-- Let m = len(grid) and let n be the common row length from the preconditions. For every integer t >= 0 define R_t by: R_0 = { (i,j) | 0 <= i < m and 0 <= j < n and grid[i][j] = 2 }, and R_{t+1} = R_t union { (i,j) | 0 <= i < m and 0 <= j < n and grid[i][j] = 1 and there exists (a,b) in R_t with |i-a| + |j-b| = 1 }. Let F = { (i,j) | 0 <= i < m and 0 <= j < n and grid[i][j] = 1 }. The function returns a result r (it does not fail) such that: if the set { t | t >= 0 and F is a subset of R_t } is nonempty, then r is its least element; otherwise r = -1.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) :
    ∃ r : Std.I64,
      oranges_rotting grid = ok r ∧
        ((∃ t : Nat, Fresh grid m n ⊆ R grid m n t) →
          (0 ≤ r.val ∧ Fresh grid m n ⊆ R grid m n r.val.toNat ∧
            ∀ t : Nat, Fresh grid m n ⊆ R grid m n t → r.val ≤ (t : Int))) ∧
        ((¬∃ t : Nat, Fresh grid m n ⊆ R grid m n t) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n), ∃ r : Std.I64,
      oranges_rotting grid = ok r ∧
        ((∃ t : Nat, Fresh grid m n ⊆ R grid m n t) →
          (0 ≤ r.val ∧ Fresh grid m n ⊆ R grid m n r.val.toNat ∧
            ∀ t : Nat, Fresh grid m n ⊆ R grid m n t → r.val ≤ (t : Int))) ∧
        ((¬∃ t : Nat, Fresh grid m n ⊆ R grid m n t) → r.val = -1)) := by
  sorry

/-- For every grid satisfying the preconditions, the function returns a result r (that is, a Result.ok value); it does not panic, perform an out-of-bounds access, or overflow during the computation.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) :
    ∃ r : Std.I64, oranges_rotting grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n), ∃ r : Std.I64, oranges_rotting grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or (0 <= r and r <= fresh_count), where fresh_count is the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (freshCount grid m n : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (freshCount grid m n : Int))) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no pair (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) :
    r.val = 0 ↔ ¬∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r), r.val = 0 ↔ ¬∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there exists a fresh cell c = (i,j) with grid[i][j] = 1 for which there is no path p_0, p_1, ..., p_k (k >= 0) such that p_0 is initially rotten (grid[p_0] = 2), p_k = c, every p_l is a cell of the grid, consecutive positions are 4-directionally adjacent (Manhattan distance 1), and every p_l has original value 1 or 2.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) :
    r.val = -1 ↔
      ∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1 ∧
        ¬∃ k : Nat, PathTo grid m n k (i, j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r), r.val = -1 ↔
      ∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1 ∧
        ¬∃ k : Nat, PathTo grid m n k (i, j)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, every initially fresh cell (i,j), meaning grid[i][j] = 1, belongs to R_r, where R_t is the rotting process defined in spec_1.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) (hr : 0 ≤ r.val) :
    ∀ i j : Nat, i < m → j < n → cellVal grid i j = some 1 → (i, j) ∈ R grid m n r.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) (hr : 0 ≤ r.val), ∀ i j : Nat, i < m → j < n → cellVal grid i j = some 1 → (i, j) ∈ R grid m n r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists an initially fresh cell (i,j) with grid[i][j] = 1 that does not belong to R_{r-1}, where R_t is the rotting process defined in spec_1.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) (hr : 0 < r.val) :
    ∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1 ∧
      (i, j) ∉ R grid m n (r.val - 1).toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) (hr : 0 < r.val), ∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1 ∧
      (i, j) ∉ R grid m n (r.val - 1).toNat) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for each initially fresh cell c define d(c) to be the least k >= 0 for which there is a path p_0, ..., p_k with p_0 initially rotten, p_k = c, consecutive positions 4-directionally adjacent, and every p_l having original value 1 or 2. Then every fresh cell has a finite d(c), and r = max { d(c) | c is an initially fresh cell }, with the convention that the maximum over an empty set is 0.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) (hr : 0 ≤ r.val) :
    (∀ i j : Nat, i < m → j < n → cellVal grid i j = some 1 →
        ∃ k : Nat, IsRotTime grid m n i j k) ∧
      (∀ i j : Nat, i < m → j < n → cellVal grid i j = some 1 →
        ∀ k : Nat, IsRotTime grid m n i j k → (k : Int) ≤ r.val) ∧
      ((∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1 ∧
          IsRotTime grid m n i j r.val.toNat) ∨
        ((¬∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1) ∧ r.val = 0)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : GridValid grid m n) (r : Std.I64)
    (h : oranges_rotting grid = ok r) (hr : 0 ≤ r.val), (∀ i j : Nat, i < m → j < n → cellVal grid i j = some 1 →
        ∃ k : Nat, IsRotTime grid m n i j k) ∧
      (∀ i j : Nat, i < m → j < n → cellVal grid i j = some 1 →
        ∀ k : Nat, IsRotTime grid m n i j k → (k : Int) ≤ r.val) ∧
      ((∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1 ∧
          IsRotTime grid m n i j r.val.toNat) ∨
        ((¬∃ i j : Nat, i < m ∧ j < n ∧ cellVal grid i j = some 1) ∧ r.val = 0))) := by
  sorry

/-- Let grid' be the m x n grid defined by grid'[i][j] = grid[i][n-1-j] for all 0 <= i < m and 0 <= j < n. Whenever oranges_rotting(grid) returns r and oranges_rotting(grid') returns r', we have r = r'.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hgrid' : GridValid grid' m n)
    (hflip : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid i (n - 1 - j))
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hgrid' : GridValid grid' m n)
    (hflip : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid i (n - 1 - j))
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r'), r = r') := by
  sorry

/-- Let grid' be the m x n grid defined by grid'[i][j] = grid[m-1-i][j] for all 0 <= i < m and 0 <= j < n. Whenever oranges_rotting(grid) returns r and oranges_rotting(grid') returns r', we have r = r'.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hgrid' : GridValid grid' m n)
    (hflip : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid (m - 1 - i) j)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hgrid' : GridValid grid' m n)
    (hflip : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid (m - 1 - i) j)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r'), r = r') := by
  sorry

/-- Let grid' be the n x m grid defined by grid'[j][i] = grid[i][j] for all 0 <= i < m and 0 <= j < n. Whenever oranges_rotting(grid) returns r and oranges_rotting(grid') returns r', we have r = r'.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hgrid' : GridValid grid' n m)
    (htranspose : ∀ i j : Nat, i < m → j < n → cellVal grid' j i = cellVal grid i j)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hgrid' : GridValid grid' n m)
    (htranspose : ∀ i j : Nat, i < m → j < n → cellVal grid' j i = cellVal grid i j)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r'), r = r') := by
  sorry

/-- Let grid' be the (m+1) x n grid obtained by appending one row of zeros after the last row of grid: grid'[i][j] = grid[i][j] for 0 <= i < m and 0 <= j < n, and grid'[m][j] = 0 for 0 <= j < n. Whenever oranges_rotting(grid) returns r and oranges_rotting(grid') returns r', we have r = r'.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. Additionally, m + 1 <= 10. -/
theorem spec_12 (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hm : m + 1 ≤ 10) (hgrid' : GridValid grid' (m + 1) n)
    (hkeep : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid i j)
    (hzero : ∀ j : Nat, j < n → cellVal grid' m j = some 0)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hm : m + 1 ≤ 10) (hgrid' : GridValid grid' (m + 1) n)
    (hkeep : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid i j)
    (hzero : ∀ j : Nat, j < n → cellVal grid' m j = some 0)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r'), r = r') := by
  sorry

/-- Let grid' be the m x (n+1) grid obtained by appending one column of zeros after the last column of grid: grid'[i][j] = grid[i][j] for 0 <= i < m and 0 <= j < n, and grid'[i][n] = 0 for 0 <= i < m. Whenever oranges_rotting(grid) returns r and oranges_rotting(grid') returns r', we have r = r'.
  Preconditions: Let m = len(grid). There exists an integer n such that 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is the I64 encoding of 0, 1, or 2 for every 0 <= i < m and 0 <= j < n. Additionally, n + 1 <= 10. -/
theorem spec_13 (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hn : n + 1 ≤ 10) (hgrid' : GridValid grid' m (n + 1))
    (hkeep : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid i j)
    (hzero : ∀ i : Nat, i < m → cellVal grid' i n = some 0)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r') :
    r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid grid' : Grid) (m n : Nat) (hgrid : GridValid grid m n)
    (hn : n + 1 ≤ 10) (hgrid' : GridValid grid' m (n + 1))
    (hkeep : ∀ i j : Nat, i < m → j < n → cellVal grid' i j = cellVal grid i j)
    (hzero : ∀ i : Nat, i < m → cellVal grid' i n = some 0)
    (r r' : Std.I64) (h : oranges_rotting grid = ok r) (h' : oranges_rotting grid' = ok r'), r = r') := by
  sorry

end AegisSpec.OrangesRotting
