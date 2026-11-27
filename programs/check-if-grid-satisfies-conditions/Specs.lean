import Aegis.SatisfiesConditions.Code.Funs

/-!
# Specifications of `Aegis.SatisfiesConditions.satisfies_conditions`

LeetCode problem `check-if-grid-satisfies-conditions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SatisfiesConditions

  open Aegis.SatisfiesConditions

  def gridInts (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map (fun v => v.val.map (fun x => x.val))

  def rowWidth (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    ((grid.val[0]?).map (fun v => v.val.length)).getD 0

  def cellAt (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((gridInts grid).getD i []).getD j 0

  def gridCells (grid : Slice (alloc.vec.Vec Std.I64)) : List Int :=
    (gridInts grid).flatten

  def OccursInGrid (grid : Slice (alloc.vec.Vec Std.I64)) (x : Int) : Prop :=
    x ∈ gridCells grid

  def InjectiveOnGridValues (grid : Slice (alloc.vec.Vec Std.I64)) (f : Int → Int) : Prop :=
    ∀ x, OccursInGrid grid x → ∀ y, OccursInGrid grid y → f x = f y → x = y

  def SatInput (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    Slice.len grid = m ∧
    1 ≤ m ∧ m ≤ 10 ∧
    n = rowWidth grid ∧
    1 ≤ n ∧ n ≤ 10 ∧
    (∀ r, r ∈ gridInts grid → r.length = n) ∧
    (∀ i j, i < m → j < n → 0 ≤ cellAt grid i j ∧ cellAt grid i j ≤ 9)

  def VerticallyConstant (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    ∀ i j, i < m - 1 → j < n → cellAt grid i j = cellAt grid (i + 1) j

  def HorizontallyDistinct (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    ∀ i j, i < m → j < n - 1 → cellAt grid i j ≠ cellAt grid i (j + 1)

  /-- The function returns a result r and r = true if and only if both (V) and (H) hold, where (V) says: for every i,j with 0 <= i < m-1 and 0 <= j < n, grid[i][j] = grid[i+1][j]; and (H) says: for every i,j with 0 <= i < m and 0 <= j < n-1, grid[i][j] != grid[i][j+1].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∃ r, satisfies_conditions grid = ok r ∧
        (r = true ↔ (VerticallyConstant grid m n ∧ HorizontallyDistinct grid m n)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∃ r, satisfies_conditions grid = ok r ∧
          (r = true ↔ (VerticallyConstant grid m n ∧ HorizontallyDistinct grid m n))) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∃ r, satisfies_conditions grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∃ r, satisfies_conditions grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every i,j with 0 <= i < m-1 and 0 <= j < n, grid[i][j] = grid[i+1][j].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∀ r, satisfies_conditions grid = ok r → r = true → VerticallyConstant grid m n := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∀ r, satisfies_conditions grid = ok r → r = true → VerticallyConstant grid m n) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every i,j with 0 <= i < m and 0 <= j < n-1, grid[i][j] != grid[i][j+1].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∀ r, satisfies_conditions grid = ok r → r = true → HorizontallyDistinct grid m n := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∀ r, satisfies_conditions grid = ok r → r = true → HorizontallyDistinct grid m n) := by
    sorry

  /-- Whenever the function returns a result r, if r = false then either there exist i,j with 0 <= i < m-1 and 0 <= j < n such that grid[i][j] != grid[i+1][j], or there exist i,j with 0 <= i < m and 0 <= j < n-1 such that grid[i][j] = grid[i][j+1].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∀ r, satisfies_conditions grid = ok r → r = false →
        (∃ i j, i < m - 1 ∧ j < n ∧ cellAt grid i j ≠ cellAt grid (i + 1) j) ∨
        (∃ i j, i < m ∧ j < n - 1 ∧ cellAt grid i j = cellAt grid i (j + 1)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∀ r, satisfies_conditions grid = ok r → r = false →
          (∃ i j, i < m - 1 ∧ j < n ∧ cellAt grid i j ≠ cellAt grid (i + 1) j) ∨
          (∃ i j, i < m ∧ j < n - 1 ∧ cellAt grid i j = cellAt grid i (j + 1))) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] = grid[0][j].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∀ r, satisfies_conditions grid = ok r → r = true →
        ∀ i j, i < m → j < n → cellAt grid i j = cellAt grid 0 j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∀ r, satisfies_conditions grid = ok r → r = true →
          ∀ i j, i < m → j < n → cellAt grid i j = cellAt grid 0 j) := by
    sorry

  /-- Whenever the function returns a result r, if there exist i,j with 0 <= i < m and 0 <= j < n-1 such that grid[i][j] = grid[i][j+1], then r = false.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∀ r, satisfies_conditions grid = ok r →
        (∃ i j, i < m ∧ j < n - 1 ∧ cellAt grid i j = cellAt grid i (j + 1)) → r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∀ r, satisfies_conditions grid = ok r →
          (∃ i j, i < m ∧ j < n - 1 ∧ cellAt grid i j = cellAt grid i (j + 1)) → r = false) := by
    sorry

  /-- Whenever the function returns a result r, if there exist i,j with 0 <= i < m-1 and 0 <= j < n such that grid[i][j] != grid[i+1][j], then r = false.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n) :
      ∀ r, satisfies_conditions grid = ok r →
        (∃ i j, i < m - 1 ∧ j < n ∧ cellAt grid i j ≠ cellAt grid (i + 1) j) → r = false := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hin : SatInput grid m n), ∀ r, satisfies_conditions grid = ok r →
          (∃ i j, i < m - 1 ∧ j < n ∧ cellAt grid i j ≠ cellAt grid (i + 1) j) → r = false) := by
    sorry

  /-- For every integer k and every grid H satisfying the same preconditions with the same m and n, if H[i][j] = grid[i][j] + k (as integers) for every i,j with 0 <= i < m and 0 <= j < n, then whenever the function returns r on grid and r' on H, r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_9 (grid H : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (k : Int)
      (hin : SatInput grid m n) (hinH : SatInput H m n)
      (hshift : ∀ i j, i < m → j < n → cellAt H i j = cellAt grid i j + k) :
      ∀ r r', satisfies_conditions grid = ok r → satisfies_conditions H = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid H : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (k : Int)
        (hin : SatInput grid m n) (hinH : SatInput H m n)
        (hshift : ∀ i j, i < m → j < n → cellAt H i j = cellAt grid i j + k), ∀ r r', satisfies_conditions grid = ok r → satisfies_conditions H = ok r' → r = r') := by
    sorry

  /-- For every grid H satisfying the same preconditions with the same m and n, and every function f from integers to integers that is injective on the set of values appearing in grid, if H[i][j] = f(grid[i][j]) for every i,j with 0 <= i < m and 0 <= j < n, then whenever the function returns r on grid and r' on H, r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 10, 1 <= n <= 10, len(grid[i]) = n for every i with 0 <= i < m, and 0 <= grid[i][j] <= 9 for every i with 0 <= i < m and j with 0 <= j < n. -/
  theorem spec_10 (grid H : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (f : Int → Int)
      (hin : SatInput grid m n) (hinH : SatInput H m n)
      (hinj : InjectiveOnGridValues grid f)
      (hmap : ∀ i j, i < m → j < n → cellAt H i j = f (cellAt grid i j)) :
      ∀ r r', satisfies_conditions grid = ok r → satisfies_conditions H = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid H : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (f : Int → Int)
        (hin : SatInput grid m n) (hinH : SatInput H m n)
        (hinj : InjectiveOnGridValues grid f)
        (hmap : ∀ i j, i < m → j < n → cellAt H i j = f (cellAt grid i j)), ∀ r r', satisfies_conditions grid = ok r → satisfies_conditions H = ok r' → r = r') := by
    sorry

  end AegisSpec.SatisfiesConditions
