import Aegis.RemoveOnes.Code.Funs

/-!
# Specifications of `Aegis.RemoveOnes.remove_ones`

LeetCode problem `remove-all-ones-with-row-and-column-flips`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.RemoveOnes

namespace AegisSpec.RemoveOnes

abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

def rowVal (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

def gridVal (grid : Grid) : List (List Int) := grid.val.map rowVal

def entry (grid : Grid) (i j : ℕ) : Int := ((gridVal grid).getD i []).getD j 0

def HasShape (grid : Grid) (m n : ℕ) : Prop :=
  grid.val.length = m ∧ 1 ≤ m ∧ m ≤ 300 ∧ 1 ≤ n ∧ n ≤ 300 ∧
    ∀ i, i < m → ((gridVal grid).getD i []).length = n

def EntriesAreBits (grid : Grid) (m n : ℕ) : Prop :=
  ∀ i, i < m → ∀ j, j < n → entry grid i j = 0 ∨ entry grid i j = 1

def IsBitGrid (grid : Grid) (m n : ℕ) : Prop :=
  HasShape grid m n ∧ EntriesAreBits grid m n

def RowsAgree (grid : Grid) (n i k : ℕ) : Prop :=
  ∀ j, j < n → entry grid i j = entry grid k j

def RowsCompl (grid : Grid) (n i k : ℕ) : Prop :=
  ∀ j, j < n → entry grid i j = 1 - entry grid k j

def ColsAgree (grid : Grid) (m j l : ℕ) : Prop :=
  ∀ i, i < m → entry grid i j = entry grid i l

def ColsCompl (grid : Grid) (m j l : ℕ) : Prop :=
  ∀ i, i < m → entry grid i j = 1 - entry grid i l

def permuteCols {n : ℕ} (σ : Equiv.Perm (Fin n)) (L : List (List Int)) : List (List Int) :=
  L.map fun r => List.ofFn fun j : Fin n => r.getD (σ j) 0

def permuteRows {m : ℕ} (π : Equiv.Perm (Fin m)) (L : List (List Int)) : List (List Int) :=
  List.ofFn fun i : Fin m => L.getD (π i) []

def flipRow (a : ℕ) (L : List (List Int)) : List (List Int) :=
  L.set a ((L.getD a []).map fun x => 1 - x)

def flipCol (b : ℕ) (L : List (List Int)) : List (List Int) :=
  L.map fun r => r.set b (1 - r.getD b 0)

def complementAll (L : List (List Int)) : List (List Int) :=
  L.map fun r => r.map fun x => 1 - x

/-- The function returns a result r and r = true if and only if there exist bits R_i in {0,1} for 0 <= i < m and C_j in {0,1} for 0 <= j < n such that for every 0 <= i < m and 0 <= j < n, (grid[i][j] + R_i + C_j) mod 2 = 0. Here R_i = 1 means row i is flipped an odd number of times and C_j = 1 means column j is flipped an odd number of times; all other rows and columns are flipped an even number of times.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n) :
    ∃ r, remove_ones grid = ok r ∧
      (r = true ↔ ∃ (R C : ℕ → Int),
        (∀ i, i < m → (R i = 0 ∨ R i = 1)) ∧
        (∀ j, j < n → (C j = 0 ∨ C j = 1)) ∧
        (∀ i, i < m → ∀ j, j < n → (entry grid i j + R i + C j) % 2 = 0)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n), ∃ r, remove_ones grid = ok r ∧
      (r = true ↔ ∃ (R C : ℕ → Int),
        (∀ i, i < m → (R i = 0 ∨ R i = 1)) ∧
        (∀ j, j < n → (C j = 0 ∨ C j = 1)) ∧
        (∀ i, i < m → ∀ j, j < n → (entry grid i j + R i + C j) % 2 = 0))) := by
  sorry

/-- The function returns a result r; in particular, for every valid input it does not fail, overflow, go out of bounds, or panic.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n) :
    ∃ r, remove_ones grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n), ∃ r, remove_ones grid = ok r) := by
  sorry

/-- If grid[i][j] = 0 for every 0 <= i < m and 0 <= j < n, then the function returns a result r with r = true.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hzero : ∀ i, i < m → ∀ j, j < n → entry grid i j = 0) :
    ∃ r, remove_ones grid = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hzero : ∀ i, i < m → ∀ j, j < n → entry grid i j = 0), ∃ r, remove_ones grid = ok r ∧ r = true) := by
  sorry

/-- If m = 1 or n = 1, then the function returns a result r with r = true.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hshape : m = 1 ∨ n = 1) :
    ∃ r, remove_ones grid = ok r ∧ r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hshape : m = 1 ∨ n = 1), ∃ r, remove_ones grid = ok r ∧ r = true) := by
  sorry

/-- If grid[i][j] = 1 for every 0 <= i < m and 0 <= j < n, then the function returns a result r with r = true.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hone : ∀ i, i < m → ∀ j, j < n → entry grid i j = 1) :
    ∃ r, remove_ones grid = ok r ∧ r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hone : ∀ i, i < m → ∀ j, j < n → entry grid i j = 1), ∃ r, remove_ones grid = ok r ∧ r = true) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every pair of row indices i and k with 0 <= i < k < m, either grid[i][j] = grid[k][j] for every 0 <= j < n, or grid[i][j] = 1 - grid[k][j] for every 0 <= j < n.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n) :
    ∀ r, remove_ones grid = ok r → r = true →
      ∀ i k, i < k → k < m → RowsAgree grid n i k ∨ RowsCompl grid n i k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n), ∀ r, remove_ones grid = ok r → r = true →
      ∀ i k, i < k → k < m → RowsAgree grid n i k ∨ RowsCompl grid n i k) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every pair of column indices j and l with 0 <= j < l < n, either grid[i][j] = grid[i][l] for every 0 <= i < m, or grid[i][j] = 1 - grid[i][l] for every 0 <= i < m.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n) :
    ∀ r, remove_ones grid = ok r → r = true →
      ∀ j l, j < l → l < n → ColsAgree grid m j l ∨ ColsCompl grid m j l := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n), ∀ r, remove_ones grid = ok r → r = true →
      ∀ j l, j < l → l < n → ColsAgree grid m j l ∨ ColsCompl grid m j l) := by
  sorry

/-- Whenever the function returns a result r with r = true, for all row indices i,k and column indices j,l with 0 <= i < k < m and 0 <= j < l < n, (grid[i][j] + grid[i][l] + grid[k][j] + grid[k][l]) mod 2 = 0.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n) :
    ∀ r, remove_ones grid = ok r → r = true →
      ∀ i k j l, i < k → k < m → j < l → l < n →
        (entry grid i j + entry grid i l + entry grid k j + entry grid k l) % 2 = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n), ∀ r, remove_ones grid = ok r → r = true →
      ∀ i k j l, i < k → k < m → j < l → l < n →
        (entry grid i j + entry grid i l + entry grid k j + entry grid k l) % 2 = 0) := by
  sorry

/-- Whenever the function returns a result r with r = false, there exist row indices i,k and column indices j,l with 0 <= i < k < m and 0 <= j < l < n such that (grid[i][j] + grid[i][l] + grid[k][j] + grid[k][l]) mod 2 = 1.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n) :
    ∀ r, remove_ones grid = ok r → r = false →
      ∃ i k j l, i < k ∧ k < m ∧ j < l ∧ l < n ∧
        (entry grid i j + entry grid i l + entry grid k j + entry grid k l) % 2 = 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n), ∀ r, remove_ones grid = ok r → r = false →
      ∃ i k j l, i < k ∧ k < m ∧ j < l ∧ l < n ∧
        (entry grid i j + entry grid i l + entry grid k j + entry grid k l) % 2 = 1) := by
  sorry

/-- If for every pair of row indices i and k with 0 <= i < k < m, either grid[i][j] = grid[k][j] for every 0 <= j < n or grid[i][j] = 1 - grid[k][j] for every 0 <= j < n, then the function returns a result r with r = true.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hrows : ∀ i k, i < k → k < m → RowsAgree grid n i k ∨ RowsCompl grid n i k) :
    ∃ r, remove_ones grid = ok r ∧ r = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hrows : ∀ i k, i < k → k < m → RowsAgree grid n i k ∨ RowsCompl grid n i k), ∃ r, remove_ones grid = ok r ∧ r = true) := by
  sorry

/-- For every permutation sigma of {0,...,n-1}, define gridsigma by len(gridsigma) = m, len(gridsigma[i]) = n, and gridsigma[i][j] = grid[i][sigma(j)] for all 0 <= i < m and 0 <= j < n. Then remove_ones(grid) and remove_ones(gridsigma) both return results r and rsigma, and r = rsigma.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (grid gridsigma : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (σ : Equiv.Perm (Fin n)) (hsigma : gridVal gridsigma = permuteCols σ (gridVal grid)) :
    ∃ r rsigma, remove_ones grid = ok r ∧ remove_ones gridsigma = ok rsigma ∧ r = rsigma := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid gridsigma : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (σ : Equiv.Perm (Fin n)) (hsigma : gridVal gridsigma = permuteCols σ (gridVal grid)), ∃ r rsigma, remove_ones grid = ok r ∧ remove_ones gridsigma = ok rsigma ∧ r = rsigma) := by
  sorry

/-- For every permutation pi of {0,...,m-1}, define gridpi by len(gridpi) = m, len(gridpi[i]) = n, and gridpi[i][j] = grid[pi(i)][j] for all 0 <= i < m and 0 <= j < n. Then remove_ones(grid) and remove_ones(gridpi) both return results r and rpi, and r = rpi.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (grid gridpi : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (π : Equiv.Perm (Fin m)) (hpi : gridVal gridpi = permuteRows π (gridVal grid)) :
    ∃ r rpi, remove_ones grid = ok r ∧ remove_ones gridpi = ok rpi ∧ r = rpi := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid gridpi : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (π : Equiv.Perm (Fin m)) (hpi : gridVal gridpi = permuteRows π (gridVal grid)), ∃ r rpi, remove_ones grid = ok r ∧ remove_ones gridpi = ok rpi ∧ r = rpi) := by
  sorry

/-- For every row index a with 0 <= a < m, define gridprime by gridprime[i][j] = 1 - grid[a][j] when i = a, and gridprime[i][j] = grid[i][j] otherwise. Then remove_ones(grid) and remove_ones(gridprime) both return results r and rprime, and r = rprime.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (grid gridprime : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (a : ℕ) (ha : a < m) (hprime : gridVal gridprime = flipRow a (gridVal grid)) :
    ∃ r rprime, remove_ones grid = ok r ∧ remove_ones gridprime = ok rprime ∧ r = rprime := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid gridprime : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (a : ℕ) (ha : a < m) (hprime : gridVal gridprime = flipRow a (gridVal grid)), ∃ r rprime, remove_ones grid = ok r ∧ remove_ones gridprime = ok rprime ∧ r = rprime) := by
  sorry

/-- For every column index b with 0 <= b < n, define gridprime by gridprime[i][j] = 1 - grid[i][b] when j = b, and gridprime[i][j] = grid[i][j] otherwise. Then remove_ones(grid) and remove_ones(gridprime) both return results r and rprime, and r = rprime.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_14 (grid gridprime : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (b : ℕ) (hb : b < n) (hprime : gridVal gridprime = flipCol b (gridVal grid)) :
    ∃ r rprime, remove_ones grid = ok r ∧ remove_ones gridprime = ok rprime ∧ r = rprime := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid gridprime : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (b : ℕ) (hb : b < n) (hprime : gridVal gridprime = flipCol b (gridVal grid)), ∃ r rprime, remove_ones grid = ok r ∧ remove_ones gridprime = ok rprime ∧ r = rprime) := by
  sorry

/-- Define gridprime by gridprime[i][j] = 1 - grid[i][j] for every 0 <= i < m and 0 <= j < n. Then remove_ones(grid) and remove_ones(gridprime) both return results r and rprime, and r = rprime.
  Preconditions: Let m = len(grid) and n be the common length of the rows. Assume 1 <= m <= 300, 1 <= n <= 300, every row grid[i] has length n, and grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_15 (grid gridprime : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hprime : gridVal gridprime = complementAll (gridVal grid)) :
    ∃ r rprime, remove_ones grid = ok r ∧ remove_ones gridprime = ok rprime ∧ r = rprime := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (grid gridprime : Grid) (m n : ℕ) (h : IsBitGrid grid m n)
    (hprime : gridVal gridprime = complementAll (gridVal grid)), ∃ r rprime, remove_ones grid = ok r ∧ remove_ones gridprime = ok rprime ∧ r = rprime) := by
  sorry

end AegisSpec.RemoveOnes
