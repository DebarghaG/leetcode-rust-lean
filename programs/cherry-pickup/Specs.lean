import Aegis.CherryPickup.Code.Funs

/-!
# Specifications of `Aegis.CherryPickup.cherry_pickup`

LeetCode problem `cherry-pickup`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CherryPickup

set_option maxHeartbeats 1000000

namespace AegisSpec.CherryPickup

abbrev Grid : Type := Slice (alloc.vec.Vec I64)

def cell (grid : Grid) (i j : ℕ) : ℤ :=
  match grid.val[i]? with
  | some row =>
    match row.val[j]? with
    | some x => x.val
    | none => 0
  | none => 0

def Step (a b : ℕ × ℕ) : Prop :=
  b = (a.1, a.2 + 1) ∨ b = (a.1 + 1, a.2)

def IsForwardPath (grid : Grid) (n : ℕ) (P : List (ℕ × ℕ)) : Prop :=
  P.head? = some (0, 0) ∧
  P.getLast? = some (n - 1, n - 1) ∧
  (∀ (k : ℕ), k + 1 < P.length → Step P[k]! P[k + 1]!) ∧
  (∀ (p : ℕ × ℕ), p ∈ P → p.1 < n ∧ p.2 < n ∧
    (cell grid p.1 p.2 = 0 ∨ cell grid p.1 p.2 = 1))

def pathScore (grid : Grid) (P : List (ℕ × ℕ)) : ℕ :=
  (P.filter (fun p => decide (cell grid p.1 p.2 = 1))).length

def unionScore (grid : Grid) (P Q : List (ℕ × ℕ)) : ℕ :=
  ((P ++ Q).dedup.filter (fun p => decide (cell grid p.1 p.2 = 1))).length

def countOnes (grid : Grid) (n : ℕ) : ℕ :=
  ((((List.range n).flatMap (fun i => (List.range n).map (fun j => (i, j)))).filter
      (fun p => decide (cell grid p.1 p.2 = 1)))).length

def IsTranspose (A B : Grid) (n : ℕ) : Prop :=
  B.val.length = n ∧
  (∀ (row : alloc.vec.Vec I64), row ∈ B.val → row.val.length = n) ∧
  (∀ (i j : ℕ), i < n → j < n → cell B i j = cell A j i)

def OnesTurnedToZero (A B : Grid) (n : ℕ) : Prop :=
  ∀ (i j : ℕ), i < n → j < n →
    (cell A i j = 1 ∧ cell B i j = 0) ∨ cell B i j = cell A i j

def MinusOnesTurnedToZero (A B : Grid) (n : ℕ) : Prop :=
  ∀ (i j : ℕ), i < n → j < n →
    (cell A i j = -1 ∧ cell B i j = 0) ∨ cell B i j = cell A i j

/-- A forward monotone path is a sequence of cells from (0,0) to (n-1,n-1) in which each step is either right or down and every cell has grid value 0 or 1. For any two such paths P and Q, let score(P,Q) be the number of distinct cells (i,j) that belong to P or Q and satisfy grid[i][j] = 1. The function returns a result r and r = max score(P,Q) over all ordered pairs (P,Q) of forward monotone paths when at least one forward monotone path exists; if no forward monotone path exists, r = 0.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. -/
theorem spec_1 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1) :
    ∃ r : I64, cherry_pickup grid = ok r ∧
      ((∃ P : List (ℕ × ℕ), IsForwardPath grid n P) →
        (∃ P Q : List (ℕ × ℕ),
          IsForwardPath grid n P ∧ IsForwardPath grid n Q ∧
          r.val = (unionScore grid P Q : ℤ) ∧
          ∀ (P' Q' : List (ℕ × ℕ)), IsForwardPath grid n P' → IsForwardPath grid n Q' →
            (unionScore grid P' Q' : ℤ) ≤ r.val)) ∧
      ((¬ ∃ P : List (ℕ × ℕ), IsForwardPath grid n P) → r.val = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1), ∃ r : I64, cherry_pickup grid = ok r ∧
      ((∃ P : List (ℕ × ℕ), IsForwardPath grid n P) →
        (∃ P Q : List (ℕ × ℕ),
          IsForwardPath grid n P ∧ IsForwardPath grid n Q ∧
          r.val = (unionScore grid P Q : ℤ) ∧
          ∀ (P' Q' : List (ℕ × ℕ)), IsForwardPath grid n P' → IsForwardPath grid n Q' →
            (unionScore grid P' Q' : ℤ) ≤ r.val)) ∧
      ((¬ ∃ P : List (ℕ × ℕ), IsForwardPath grid n P) → r.val = 0)) := by
  sorry

/-- For every grid satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access an out-of-bounds index.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. -/
theorem spec_2 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1) :
    ∃ r : I64, cherry_pickup grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1), ∃ r : I64, cherry_pickup grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= min(C, 4n - 4), where C is the number of cells (i,j) with 0 <= i,j < n and grid[i][j] = 1.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1; additionally n >= 2. -/
theorem spec_3 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hn2 : 2 ≤ n) :
    ∀ r : I64, cherry_pickup grid = ok r →
      0 ≤ r.val ∧ r.val ≤ ((min (countOnes grid n) (4 * n - 4) : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hn2 : 2 ≤ n), ∀ r : I64, cherry_pickup grid = ok r →
      0 ≤ r.val ∧ r.val ≤ ((min (countOnes grid n) (4 * n - 4) : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = grid[0][0].
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1; additionally n = 1. -/
theorem spec_4 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hn1 : n = 1) :
    ∀ r : I64, cherry_pickup grid = ok r → r.val = cell grid 0 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hn1 : n = 1), ∀ r : I64, cherry_pickup grid = ok r → r.val = cell grid 0 0) := by
  sorry

/-- Whenever the function returns a result r, for every forward monotone path P from (0,0) to (n-1,n-1), r >= c(P), where c(P) is the number of cells of P with grid[i][j] = 1. A forward monotone path uses only right or down steps and only cells with grid value 0 or 1.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. -/
theorem spec_5 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1) :
    ∀ r : I64, cherry_pickup grid = ok r →
      ∀ P : List (ℕ × ℕ), IsForwardPath grid n P → (pathScore grid P : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1), ∀ r : I64, cherry_pickup grid = ok r →
      ∀ P : List (ℕ × ℕ), IsForwardPath grid n P → (pathScore grid P : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every ordered pair (P,Q) of forward monotone paths from (0,0) to (n-1,n-1), the number of distinct cells (i,j) that belong to P or Q and satisfy grid[i][j] = 1 is at most r.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. -/
theorem spec_6 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1) :
    ∀ r : I64, cherry_pickup grid = ok r →
      ∀ P Q : List (ℕ × ℕ), IsForwardPath grid n P → IsForwardPath grid n Q →
        (unionScore grid P Q : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1), ∀ r : I64, cherry_pickup grid = ok r →
      ∀ P Q : List (ℕ × ℕ), IsForwardPath grid n P → IsForwardPath grid n Q →
        (unionScore grid P Q : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist forward monotone paths P and Q from (0,0) to (n-1,n-1) such that the number of distinct cells (i,j) that belong to P or Q and satisfy grid[i][j] = 1 equals r.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1; additionally there exists at least one forward monotone path from (0,0) to (n-1,n-1). -/
theorem spec_7 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hex : ∃ P : List (ℕ × ℕ), IsForwardPath grid n P) :
    ∀ r : I64, cherry_pickup grid = ok r →
      ∃ P Q : List (ℕ × ℕ),
        IsForwardPath grid n P ∧ IsForwardPath grid n Q ∧
        (unionScore grid P Q : ℤ) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hex : ∃ P : List (ℕ × ℕ), IsForwardPath grid n P), ∀ r : I64, cherry_pickup grid = ok r →
      ∃ P Q : List (ℕ × ℕ),
        IsForwardPath grid n P ∧ IsForwardPath grid n Q ∧
        (unionScore grid P Q : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r, if there is no forward monotone path from (0,0) to (n-1,n-1), then r = 0.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. -/
theorem spec_8 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1) :
    ∀ r : I64, cherry_pickup grid = ok r →
      (¬ ∃ P : List (ℕ × ℕ), IsForwardPath grid n P) → r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1), ∀ r : I64, cherry_pickup grid = ok r →
      (¬ ∃ P : List (ℕ × ℕ), IsForwardPath grid n P) → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if grid[i][j] != 1 for every 0 <= i,j < n, then r = 0.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. -/
theorem spec_9 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1) :
    ∀ r : I64, cherry_pickup grid = ok r →
      (∀ (i j : ℕ), i < n → j < n → cell grid i j ≠ 1) → r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1), ∀ r : I64, cherry_pickup grid = ok r →
      (∀ (i j : ℕ), i < n → j < n → cell grid i j ≠ 1) → r.val = 0) := by
  sorry

/-- Let gridT be the n x n grid defined by gridT[i][j] = grid[j][i] for 0 <= i,j < n. For every grid satisfying the preconditions, if r is the result returned by the function on grid and rT is the result returned by the function on gridT, then r = rT.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. -/
theorem spec_10 (grid gridT : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hnT_len : gridT.val.length = n)
    (hrowsT : ∀ (row : alloc.vec.Vec I64), row ∈ gridT.val → row.val.length = n)
    (hvalsT : ∀ (i j : ℕ), i < n → j < n →
      cell gridT i j = -1 ∨ cell gridT i j = 0 ∨ cell gridT i j = 1)
    (h00T : cell gridT 0 0 ≠ -1)
    (hnnT : cell gridT (n - 1) (n - 1) ≠ -1)
    (hT : IsTranspose grid gridT n) :
    ∀ r rT : I64, cherry_pickup grid = ok r → cherry_pickup gridT = ok rT →
      r.val = rT.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridT : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hnT_len : gridT.val.length = n)
    (hrowsT : ∀ (row : alloc.vec.Vec I64), row ∈ gridT.val → row.val.length = n)
    (hvalsT : ∀ (i j : ℕ), i < n → j < n →
      cell gridT i j = -1 ∨ cell gridT i j = 0 ∨ cell gridT i j = 1)
    (h00T : cell gridT 0 0 ≠ -1)
    (hnnT : cell gridT (n - 1) (n - 1) ≠ -1)
    (hT : IsTranspose grid gridT n), ∀ r rT : I64, cherry_pickup grid = ok r → cherry_pickup gridT = ok rT →
      r.val = rT.val) := by
  sorry

/-- Whenever the function returns result rA on A and result rB on B, rB <= rA.
  Preconditions: Let A and B be two n x n grids with 1 <= n <= 50, every entry in {-1,0,1}, A[0][0] != -1, A[n-1][n-1] != -1, B[0][0] != -1, and B[n-1][n-1] != -1. Suppose B is obtained from A by changing zero or more cells with A[i][j] = 1 to B[i][j] = 0 and leaving every other cell unchanged. -/
theorem spec_11 (A B : Grid) (n : ℕ)
    (hnA_len : A.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrowsA : ∀ (row : alloc.vec.Vec I64), row ∈ A.val → row.val.length = n)
    (hvalsA : ∀ (i j : ℕ), i < n → j < n →
      cell A i j = -1 ∨ cell A i j = 0 ∨ cell A i j = 1)
    (h00A : cell A 0 0 ≠ -1)
    (hnnA : cell A (n - 1) (n - 1) ≠ -1)
    (hnB_len : B.val.length = n)
    (hrowsB : ∀ (row : alloc.vec.Vec I64), row ∈ B.val → row.val.length = n)
    (hvalsB : ∀ (i j : ℕ), i < n → j < n →
      cell B i j = -1 ∨ cell B i j = 0 ∨ cell B i j = 1)
    (h00B : cell B 0 0 ≠ -1)
    (hnnB : cell B (n - 1) (n - 1) ≠ -1)
    (hAB : OnesTurnedToZero A B n) :
    ∀ rA rB : I64, cherry_pickup A = ok rA → cherry_pickup B = ok rB →
      rB.val ≤ rA.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (A B : Grid) (n : ℕ)
    (hnA_len : A.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrowsA : ∀ (row : alloc.vec.Vec I64), row ∈ A.val → row.val.length = n)
    (hvalsA : ∀ (i j : ℕ), i < n → j < n →
      cell A i j = -1 ∨ cell A i j = 0 ∨ cell A i j = 1)
    (h00A : cell A 0 0 ≠ -1)
    (hnnA : cell A (n - 1) (n - 1) ≠ -1)
    (hnB_len : B.val.length = n)
    (hrowsB : ∀ (row : alloc.vec.Vec I64), row ∈ B.val → row.val.length = n)
    (hvalsB : ∀ (i j : ℕ), i < n → j < n →
      cell B i j = -1 ∨ cell B i j = 0 ∨ cell B i j = 1)
    (h00B : cell B 0 0 ≠ -1)
    (hnnB : cell B (n - 1) (n - 1) ≠ -1)
    (hAB : OnesTurnedToZero A B n), ∀ rA rB : I64, cherry_pickup A = ok rA → cherry_pickup B = ok rB →
      rB.val ≤ rA.val) := by
  sorry

/-- Whenever the function returns result rA on A and result rB on B, rA <= rB.
  Preconditions: Let A and B be two n x n grids with 1 <= n <= 50, every entry in {-1,0,1}, A[0][0] != -1, A[n-1][n-1] != -1, B[0][0] != -1, and B[n-1][n-1] != -1. Suppose B is obtained from A by changing zero or more cells with A[i][j] = -1 to B[i][j] = 0 and leaving every other cell unchanged. -/
theorem spec_12 (A B : Grid) (n : ℕ)
    (hnA_len : A.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrowsA : ∀ (row : alloc.vec.Vec I64), row ∈ A.val → row.val.length = n)
    (hvalsA : ∀ (i j : ℕ), i < n → j < n →
      cell A i j = -1 ∨ cell A i j = 0 ∨ cell A i j = 1)
    (h00A : cell A 0 0 ≠ -1)
    (hnnA : cell A (n - 1) (n - 1) ≠ -1)
    (hnB_len : B.val.length = n)
    (hrowsB : ∀ (row : alloc.vec.Vec I64), row ∈ B.val → row.val.length = n)
    (hvalsB : ∀ (i j : ℕ), i < n → j < n →
      cell B i j = -1 ∨ cell B i j = 0 ∨ cell B i j = 1)
    (h00B : cell B 0 0 ≠ -1)
    (hnnB : cell B (n - 1) (n - 1) ≠ -1)
    (hAB : MinusOnesTurnedToZero A B n) :
    ∀ rA rB : I64, cherry_pickup A = ok rA → cherry_pickup B = ok rB →
      rA.val ≤ rB.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (A B : Grid) (n : ℕ)
    (hnA_len : A.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrowsA : ∀ (row : alloc.vec.Vec I64), row ∈ A.val → row.val.length = n)
    (hvalsA : ∀ (i j : ℕ), i < n → j < n →
      cell A i j = -1 ∨ cell A i j = 0 ∨ cell A i j = 1)
    (h00A : cell A 0 0 ≠ -1)
    (hnnA : cell A (n - 1) (n - 1) ≠ -1)
    (hnB_len : B.val.length = n)
    (hrowsB : ∀ (row : alloc.vec.Vec I64), row ∈ B.val → row.val.length = n)
    (hvalsB : ∀ (i j : ℕ), i < n → j < n →
      cell B i j = -1 ∨ cell B i j = 0 ∨ cell B i j = 1)
    (h00B : cell B 0 0 ≠ -1)
    (hnnB : cell B (n - 1) (n - 1) ≠ -1)
    (hAB : MinusOnesTurnedToZero A B n), ∀ rA rB : I64, cherry_pickup A = ok rA → cherry_pickup B = ok rB →
      rA.val ≤ rB.val) := by
  sorry

/-- Whenever the function returns a result r, r = 4n - 4.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1; additionally n >= 2 and grid[i][j] = 1 for every 0 <= i,j < n. -/
theorem spec_13 (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hn2 : 2 ≤ n)
    (hones : ∀ (i j : ℕ), i < n → j < n → cell grid i j = 1) :
    ∀ r : I64, cherry_pickup grid = ok r → r.val = ((4 * n - 4 : ℕ) : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hn2 : 2 ≤ n)
    (hones : ∀ (i j : ℕ), i < n → j < n → cell grid i j = 1), ∀ r : I64, cherry_pickup grid = ok r → r.val = ((4 * n - 4 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = c(P), where c(P) is the number of cells of P with grid[i][j] = 1.
  Preconditions: Let n = len(grid). The input is an n x n grid (so every row has length n) with 1 <= n <= 50, every entry in {-1,0,1}, grid[0][0] != -1, and grid[n-1][n-1] != -1. Additionally, there is exactly one forward monotone path P from (0,0) to (n-1,n-1), where a forward monotone path uses only right or down steps and only cells with grid value 0 or 1. -/
theorem spec_14 (grid : Grid) (n : ℕ) (P : List (ℕ × ℕ))
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hpath : IsForwardPath grid n P)
    (huniq : ∀ Q : List (ℕ × ℕ), IsForwardPath grid n Q → Q = P) :
    ∀ r : I64, cherry_pickup grid = ok r → r.val = (pathScore grid P : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Grid) (n : ℕ) (P : List (ℕ × ℕ))
    (hn_len : grid.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50)
    (hrows : ∀ (row : alloc.vec.Vec I64), row ∈ grid.val → row.val.length = n)
    (hvals : ∀ (i j : ℕ), i < n → j < n →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1)
    (h00 : cell grid 0 0 ≠ -1)
    (hnn : cell grid (n - 1) (n - 1) ≠ -1)
    (hpath : IsForwardPath grid n P)
    (huniq : ∀ Q : List (ℕ × ℕ), IsForwardPath grid n Q → Q = P), ∀ r : I64, cherry_pickup grid = ok r → r.val = (pathScore grid P : ℤ)) := by
  sorry

end AegisSpec.CherryPickup
