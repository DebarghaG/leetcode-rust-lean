import Aegis.MinTotalDistance.Code.Funs

/-!
# Specifications of `Aegis.MinTotalDistance.min_total_distance`

LeetCode problem `best-meeting-point`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinTotalDistance

open Aegis.MinTotalDistance

abbrev Grid : Type := Slice (alloc.vec.Vec I64)

def absZ (z : ℤ) : ℤ := if z < 0 then -z else z

def cell (grid : Grid) (i j : ℕ) : Option ℤ :=
  (grid.val[i]?).bind fun row => (row.slice.val[j]?).map fun v => v.val

def SameDims (grid : Grid) (m n : ℕ) : Prop :=
  grid.val.length = m ∧ ∀ row ∈ grid.val, row.slice.val.length = n

def IsBinary (grid : Grid) (m n : ℕ) : Prop :=
  SameDims grid m n ∧
    ∀ i j, i < m → j < n → (cell grid i j = some 0 ∨ cell grid i j = some 1)

def ones (grid : Grid) (m n : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun i =>
    (List.range n).filterMap fun j => if cell grid i j = some 1 then some (i, j) else none

def kCount (grid : Grid) (m n : ℕ) : ℕ := (ones grid m n).length

def IsBinaryGrid (grid : Grid) (m n : ℕ) : Prop :=
  IsBinary grid m n ∧ 1 ≤ m ∧ m ≤ 200 ∧ 1 ≤ n ∧ n ≤ 200 ∧ 2 ≤ kCount grid m n

def D (grid : Grid) (m n : ℕ) (x y : ℤ) : ℤ :=
  ((ones grid m n).map fun p => absZ ((p.1 : ℤ) - x) + absZ ((p.2 : ℤ) - y)).sum

def R (grid : Grid) (m n : ℕ) (x : ℤ) : ℤ :=
  ((ones grid m n).map fun p => absZ ((p.1 : ℤ) - x)).sum

def C (grid : Grid) (m n : ℕ) (y : ℤ) : ℤ :=
  ((ones grid m n).map fun p => absZ ((p.2 : ℤ) - y)).sum

def inRect (m n : ℕ) (x y : ℤ) : Prop := 0 ≤ x ∧ x < (m : ℤ) ∧ 0 ≤ y ∧ y < (n : ℤ)

def IsMinOnRange (f : ℤ → ℤ) (k : ℕ) (v : ℤ) : Prop :=
  (∃ x, 0 ≤ x ∧ x < (k : ℤ) ∧ f x = v) ∧ ∀ x, 0 ≤ x → x < (k : ℤ) → v ≤ f x

def IsGridMin (grid : Grid) (m n : ℕ) (r : ℤ) : Prop :=
  (∃ x y, inRect m n x y ∧ D grid m n x y = r) ∧
    ∀ x y, inRect m n x y → r ≤ D grid m n x y

def countLtI (grid : Grid) (m n : ℕ) (x : ℤ) : ℕ :=
  ((ones grid m n).filter fun p => (p.1 : ℤ) < x).length

def countGtI (grid : Grid) (m n : ℕ) (x : ℤ) : ℕ :=
  ((ones grid m n).filter fun p => x < (p.1 : ℤ)).length

def countLtJ (grid : Grid) (m n : ℕ) (y : ℤ) : ℕ :=
  ((ones grid m n).filter fun p => (p.2 : ℤ) < y).length

def countGtJ (grid : Grid) (m n : ℕ) (y : ℤ) : ℕ :=
  ((ones grid m n).filter fun p => y < (p.2 : ℤ)).length

/-- Whenever min_total_distance(grid) returns a result r, r = min { D(x,y) | x,y are integers, 0 <= x < m, 0 <= y < n }, where D(x,y) = sum_{(i,j) in P} (|i - x| + |j - y|).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let P = { (i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1 }. -/
theorem spec_1 (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n) :
    ∀ r : I64, min_total_distance grid = ok r → IsGridMin grid m n r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n), ∀ r : I64, min_total_distance grid = ok r → IsGridMin grid m n r.val) := by
  sorry

/-- min_total_distance(grid) returns a result (it does not fail).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. -/
theorem spec_2 (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n) :
    ∃ r : I64, min_total_distance grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n), ∃ r : I64, min_total_distance grid = ok r) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r, for every (i1,j1) in P and every (i2,j2) in P with (i1,j1) != (i2,j2), r >= |i1 - i2| + |j1 - j2|.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let P = { (i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1 }. -/
theorem spec_3 (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n) :
    ∀ r : I64, min_total_distance grid = ok r →
      ∀ i1 j1 i2 j2 : ℕ, i1 < m → j1 < n → i2 < m → j2 < n →
        cell grid i1 j1 = some 1 → cell grid i2 j2 = some 1 → (i1, j1) ≠ (i2, j2) →
        absZ ((i1 : ℤ) - (i2 : ℤ)) + absZ ((j1 : ℤ) - (j2 : ℤ)) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n), ∀ r : I64, min_total_distance grid = ok r →
      ∀ i1 j1 i2 j2 : ℕ, i1 < m → j1 < n → i2 < m → j2 < n →
        cell grid i1 j1 = some 1 → cell grid i2 j2 = some 1 → (i1, j1) ≠ (i2, j2) →
        absZ ((i1 : ℤ) - (i2 : ℤ)) + absZ ((j1 : ℤ) - (j2 : ℤ)) ≤ r.val) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r, for every integer x,y with 0 <= x < m and 0 <= y < n, r <= D(x,y), where D(x,y) = sum_{(i,j) in P} (|i - x| + |j - y|).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let P = { (i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1 }. -/
theorem spec_4 (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n) :
    ∀ r : I64, min_total_distance grid = ok r →
      ∀ x y : ℤ, inRect m n x y → r.val ≤ D grid m n x y := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n), ∀ r : I64, min_total_distance grid = ok r →
      ∀ x y : ℤ, inRect m n x y → r.val ≤ D grid m n x y) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r, r = (min { R(x) | x integer, 0 <= x < m }) + (min { C(y) | y integer, 0 <= y < n }), where R(x) = sum_{(i,j) in P} |i - x| and C(y) = sum_{(i,j) in P} |j - y|.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let P = { (i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1 }. -/
theorem spec_5 (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n) :
    ∀ r : I64, min_total_distance grid = ok r →
      ∃ rx rc : ℤ,
        IsMinOnRange (R grid m n) m rx ∧ IsMinOnRange (C grid m n) n rc ∧ r.val = rx + rc := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n), ∀ r : I64, min_total_distance grid = ok r →
      ∃ rx rc : ℤ,
        IsMinOnRange (R grid m n) m rx ∧ IsMinOnRange (C grid m n) n rc ∧ r.val = rx + rc) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r, there exist integers x,y with 0 <= x < m and 0 <= y < n such that: (a) 2 * #{ (i,j) in P | i < x } <= k and 2 * #{ (i,j) in P | i > x } <= k; (b) 2 * #{ (i,j) in P | j < y } <= k and 2 * #{ (i,j) in P | j > y } <= k; and (c) r = D(x,y), where D(x,y) = sum_{(i,j) in P} (|i - x| + |j - y|).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let P = { (i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1 } and let k = number of elements of P. -/
theorem spec_6 (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n) :
    ∀ r : I64, min_total_distance grid = ok r →
      ∃ x y : ℤ,
        inRect m n x y ∧
          2 * countLtI grid m n x ≤ kCount grid m n ∧
          2 * countGtI grid m n x ≤ kCount grid m n ∧
          2 * countLtJ grid m n y ≤ kCount grid m n ∧
          2 * countGtJ grid m n y ≤ kCount grid m n ∧
          r.val = D grid m n x y := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n), ∀ r : I64, min_total_distance grid = ok r →
      ∃ x y : ℤ,
        inRect m n x y ∧
          2 * countLtI grid m n x ≤ kCount grid m n ∧
          2 * countGtI grid m n x ≤ kCount grid m n ∧
          2 * countLtJ grid m n y ≤ kCount grid m n ∧
          2 * countGtJ grid m n y ≤ kCount grid m n ∧
          r.val = D grid m n x y) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r and min_total_distance(grid') returns a result r', r <= r'.
  Preconditions: Both grid and grid' are binary grids of the same dimensions m,n, with 1 <= m <= 200, 1 <= n <= 200, every row of length n, entries 0 or 1, and at least two 1s. Let P = { (i,j) | grid[i][j] = 1 } and P' = { (i,j) | grid'[i][j] = 1 }. Assume P is a subset of P'. -/
theorem spec_7 (grid grid' : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid' : IsBinaryGrid grid' m n)
    (hsub : ∀ p ∈ ones grid m n, p ∈ ones grid' m n) :
    ∀ r r' : I64, min_total_distance grid = ok r → min_total_distance grid' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid grid' : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid' : IsBinaryGrid grid' m n)
    (hsub : ∀ p ∈ ones grid m n, p ∈ ones grid' m n), ∀ r r' : I64, min_total_distance grid = ok r → min_total_distance grid' = ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r and min_total_distance(grid_v) returns a result r_v, r = r_v.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Define grid_v by grid_v[i][j] = grid[m-1-i][j] for 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid grid_v : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid_v : IsBinary grid_v m n)
    (hv : ∀ i j, i < m → j < n → cell grid_v i j = cell grid (m - 1 - i) j) :
    ∀ r r_v : I64, min_total_distance grid = ok r → min_total_distance grid_v = ok r_v →
      r.val = r_v.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid grid_v : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid_v : IsBinary grid_v m n)
    (hv : ∀ i j, i < m → j < n → cell grid_v i j = cell grid (m - 1 - i) j), ∀ r r_v : I64, min_total_distance grid = ok r → min_total_distance grid_v = ok r_v →
      r.val = r_v.val) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r and min_total_distance(grid_h) returns a result r_h, r = r_h.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Define grid_h by grid_h[i][j] = grid[i][n-1-j] for 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid grid_h : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid_h : IsBinary grid_h m n)
    (hh : ∀ i j, i < m → j < n → cell grid_h i j = cell grid i (n - 1 - j)) :
    ∀ r r_h : I64, min_total_distance grid = ok r → min_total_distance grid_h = ok r_h →
      r.val = r_h.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid_h : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid_h : IsBinary grid_h m n)
    (hh : ∀ i j, i < m → j < n → cell grid_h i j = cell grid i (n - 1 - j)), ∀ r r_h : I64, min_total_distance grid = ok r → min_total_distance grid_h = ok r_h →
      r.val = r_h.val) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r and min_total_distance(grid_T) returns a result r_T, r = r_T.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Define grid_T of dimensions n x m by grid_T[i][j] = grid[j][i] for 0 <= i < n and 0 <= j < m. -/
theorem spec_10 (grid grid_T : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid_T : IsBinary grid_T n m)
    (hT : ∀ i j, i < n → j < m → cell grid_T i j = cell grid j i) :
    ∀ r r_T : I64, min_total_distance grid = ok r → min_total_distance grid_T = ok r_T →
      r.val = r_T.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid_T : Grid) (m n : ℕ)
    (hgrid : IsBinaryGrid grid m n) (hgrid_T : IsBinary grid_T n m)
    (hT : ∀ i j, i < n → j < m → cell grid_T i j = cell grid j i), ∀ r r_T : I64, min_total_distance grid = ok r → min_total_distance grid_T = ok r_T →
      r.val = r_T.val) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r and min_total_distance(grid_shift) returns a result r_shift, r = r_shift.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let P = { (i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1 }. Let a,b be integers such that for every (i,j) in P, 0 <= i+a < m and 0 <= j+b < n. Define P_shift = { (i+a,j+b) | (i,j) in P } and let grid_shift be the m x n binary grid with grid_shift[u][v] = 1 iff (u,v) in P_shift. -/
theorem spec_11 (grid grid_shift : Grid) (m n : ℕ) (a b : ℤ)
    (hgrid : IsBinaryGrid grid m n)
    (hdom : ∀ i j, i < m → j < n → cell grid i j = some 1 →
      0 ≤ (i : ℤ) + a ∧ (i : ℤ) + a < (m : ℤ) ∧ 0 ≤ (j : ℤ) + b ∧ (j : ℤ) + b < (n : ℤ))
    (hgrid_shift : IsBinary grid_shift m n)
    (hshift : ∀ u v, u < m → v < n →
      (cell grid_shift u v = some 1 ↔
        ∃ i j, i < m ∧ j < n ∧ cell grid i j = some 1 ∧
          (i : ℤ) + a = (u : ℤ) ∧ (j : ℤ) + b = (v : ℤ))) :
    ∀ r r_shift : I64,
      min_total_distance grid = ok r → min_total_distance grid_shift = ok r_shift →
      r.val = r_shift.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid grid_shift : Grid) (m n : ℕ) (a b : ℤ)
    (hgrid : IsBinaryGrid grid m n)
    (hdom : ∀ i j, i < m → j < n → cell grid i j = some 1 →
      0 ≤ (i : ℤ) + a ∧ (i : ℤ) + a < (m : ℤ) ∧ 0 ≤ (j : ℤ) + b ∧ (j : ℤ) + b < (n : ℤ))
    (hgrid_shift : IsBinary grid_shift m n)
    (hshift : ∀ u v, u < m → v < n →
      (cell grid_shift u v = some 1 ↔
        ∃ i j, i < m ∧ j < n ∧ cell grid i j = some 1 ∧
          (i : ℤ) + a = (u : ℤ) ∧ (j : ℤ) + b = (v : ℤ))), ∀ r r_shift : I64,
      min_total_distance grid = ok r → min_total_distance grid_shift = ok r_shift →
      r.val = r_shift.val) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r and min_total_distance(grid_pad) returns a result r_pad, r = r_pad.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let M,N be integers with m <= M <= 200 and n <= N <= 200. Define grid_pad as an M x N binary grid with grid_pad[i][j] = grid[i][j] for 0 <= i < m and 0 <= j < n, and grid_pad[i][j] = 0 otherwise. -/
theorem spec_12 (grid grid_pad : Grid) (m n M N : ℕ)
    (hgrid : IsBinaryGrid grid m n)
    (hM1 : m ≤ M) (hM2 : M ≤ 200) (hN1 : n ≤ N) (hN2 : N ≤ 200)
    (hgrid_pad : IsBinary grid_pad M N)
    (hpad : ∀ i j, i < M → j < N →
      cell grid_pad i j = if i < m ∧ j < n then cell grid i j else some 0) :
    ∀ r r_pad : I64,
      min_total_distance grid = ok r → min_total_distance grid_pad = ok r_pad →
      r.val = r_pad.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid grid_pad : Grid) (m n M N : ℕ)
    (hgrid : IsBinaryGrid grid m n)
    (hM1 : m ≤ M) (hM2 : M ≤ 200) (hN1 : n ≤ N) (hN2 : N ≤ 200)
    (hgrid_pad : IsBinary grid_pad M N)
    (hpad : ∀ i j, i < M → j < N →
      cell grid_pad i j = if i < m ∧ j < n then cell grid i j else some 0), ∀ r r_pad : I64,
      min_total_distance grid = ok r → min_total_distance grid_pad = ok r_pad →
      r.val = r_pad.val) := by
  sorry

/-- Whenever min_total_distance(grid) returns a result r, r <= (m - 1 + n - 1) * k. In particular, r <= 15920000.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 1 <= m <= 200; 1 <= n <= 200; every row grid[i] has length n; for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and at least two pairs (i,j) have grid[i][j] = 1. Let P = { (i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1 } and let k be the number of elements of P. -/
theorem spec_13 (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n) :
    ∀ r : I64, min_total_distance grid = ok r →
      r.val ≤ ((m : ℤ) - 1 + ((n : ℤ) - 1)) * (kCount grid m n : ℤ) ∧ r.val ≤ 15920000 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : IsBinaryGrid grid m n), ∀ r : I64, min_total_distance grid = ok r →
      r.val ≤ ((m : ℤ) - 1 + ((n : ℤ) - 1)) * (kCount grid m n : ℤ) ∧ r.val ≤ 15920000) := by
  sorry

end AegisSpec.MinTotalDistance
