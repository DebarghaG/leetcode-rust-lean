import Aegis.MaxTrailingZeros.Code.Funs

/-!
# Specifications of `Aegis.MaxTrailingZeros.max_trailing_zeros`

LeetCode problem `maximum-trailing-zeros-in-a-cornered-path`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.MaxTrailingZeros

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.MaxTrailingZeros

abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

def rowVals (grid : Grid) (i : Nat) : List Int :=
  match grid.val[i]? with
  | none => []
  | some row => row.val.map (fun x => x.val)

def rowLen (grid : Grid) (i : Nat) : Nat := (rowVals grid i).length

def cellVal (grid : Grid) (i j : Nat) : Int := (rowVals grid i).getD j (0 : Int)

def v2 (x : Int) : Nat := Nat.findGreatest (fun e : Nat => (2 : Int) ^ e ∣ x) x.natAbs

def v5 (x : Int) : Nat := Nat.findGreatest (fun e : Nat => (5 : Int) ^ e ∣ x) x.natAbs

def sumV2 (grid : Grid) (P : Finset (Nat × Nat)) : Int :=
  P.sum (fun c => (v2 (cellVal grid c.1 c.2) : Int))

def sumV5 (grid : Grid) (P : Finset (Nat × Nat)) : Int :=
  P.sum (fun c => (v5 (cellVal grid c.1 c.2) : Int))

def score (grid : Grid) (P : Finset (Nat × Nat)) : Int := min (sumV2 grid P) (sumV5 grid P)

def rowSeg (r0 c0 c1 : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc (min c0 c1) (max c0 c1)).image (fun k => (r0, k))

def colSeg (c0 r0 r1 : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc (min r0 r1) (max r0 r1)).image (fun i => (i, c0))

def IsCorneredPath (m n : Nat) (P : Finset (Nat × Nat)) : Prop :=
  ∃ r0 c0 r1 c1 : Nat, r0 < m ∧ r1 < m ∧ c0 < n ∧ c1 < n ∧
    P = rowSeg r0 c0 c1 ∪ colSeg c0 r0 r1

def ValidGrid (grid : Grid) (m n : Nat) : Prop :=
  grid.val.length = m ∧ 1 ≤ m ∧ 1 ≤ n ∧ m * n ≤ 100000 ∧
    (∀ i, i < m → rowLen grid i = n) ∧
    (∀ i j, i < m → j < n → 1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 1000)

def totalSum (f : Nat → Nat → Int) (m n : Nat) : Int :=
  (Finset.range m).sum (fun i => (Finset.range n).sum (fun j => f i j))

def totalV2 (grid : Grid) (m n : Nat) : Int :=
  totalSum (fun i j => (v2 (cellVal grid i j) : Int)) m n

def totalV5 (grid : Grid) (m n : Nat) : Int :=
  totalSum (fun i j => (v5 (cellVal grid i j) : Int)) m n

def segSum (f : Nat → Int) (l u : Nat) : Int := (Finset.Icc l u).sum f

def hSegScore (grid : Grid) (i l u : Nat) : Int :=
  min (segSum (fun k => (v2 (cellVal grid i k) : Int)) l u)
    (segSum (fun k => (v5 (cellVal grid i k) : Int)) l u)

def vSegScore (grid : Grid) (j l u : Nat) : Int :=
  min (segSum (fun k => (v2 (cellVal grid k j) : Int)) l u)
    (segSum (fun k => (v5 (cellVal grid k j) : Int)) l u)

/-- Whenever max_trailing_zeros(grid) returns a result r, r equals the maximum of score(P) over all cornered paths P in grid. For a positive integer x, v2(x) is the largest e >= 0 such that 2^e divides x, and v5(x) is the largest e >= 0 such that 5^e divides x. For a nonempty finite set P of cells, score(P) = min( sum_{(i,j) in P} v2(grid[i][j]), sum_{(i,j) in P} v5(grid[i][j]) ). A cornered path is a nonempty set P of cells for which there exist integers r0,c0,r1,c1 with 0 <= r0,r1 < m and 0 <= c0,c1 < n such that P = { (r0,k) : min(c0,c1) <= k <= max(c0,c1) } union { (i,c0) : min(r0,r1) <= i <= max(r0,r1) }. Indices are 0-based; the maximum is over all such P.
  Preconditions: Let m = len(grid). There exists an integer n >= 1 such that len(grid[i]) = n for every 0 <= i < m; moreover m >= 1, m*n <= 100000, and 1 <= grid[i][j] <= 1000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n) :
    ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      (∃ P : Finset (Nat × Nat), IsCorneredPath m n P ∧ r.val = score grid P) ∧
      (∀ P : Finset (Nat × Nat), IsCorneredPath m n P → score grid P ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n), ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      (∃ P : Finset (Nat × Nat), IsCorneredPath m n P ∧ r.val = score grid P) ∧
      (∀ P : Finset (Nat × Nat), IsCorneredPath m n P → score grid P ≤ r.val)) := by
  sorry

/-- For every valid grid, max_trailing_zeros(grid) does not fail: there exists an integer r such that max_trailing_zeros(grid) returns r.
  Preconditions: Let m = len(grid). There exists an integer n >= 1 such that len(grid[i]) = n for every 0 <= i < m; moreover m >= 1, m*n <= 100000, and 1 <= grid[i][j] <= 1000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n) :
    ∃ r : Std.I64, max_trailing_zeros grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n), ∃ r : Std.I64, max_trailing_zeros grid = ok r) := by
  sorry

/-- Whenever max_trailing_zeros(grid) returns a result r, 0 <= r <= min(T2,T5), where T2 = sum_{0 <= i < m} sum_{0 <= j < n} v2(grid[i][j]) and T5 = sum_{0 <= i < m} sum_{0 <= j < n} v5(grid[i][j]).
  Preconditions: Let m = len(grid). There exists an integer n >= 1 such that len(grid[i]) = n for every 0 <= i < m; moreover m >= 1, m*n <= 100000, and 1 <= grid[i][j] <= 1000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n) :
    ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      0 ≤ r.val ∧ r.val ≤ min (totalV2 grid m n) (totalV5 grid m n) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n), ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      0 ≤ r.val ∧ r.val ≤ min (totalV2 grid m n) (totalV5 grid m n)) := by
  sorry

/-- Whenever max_trailing_zeros(grid) returns a result r, there exists a cornered path P in grid such that score(P) = r. Here a cornered path is any set P of the form { (r0,k) : min(c0,c1) <= k <= max(c0,c1) } union { (i,c0) : min(r0,r1) <= i <= max(r0,r1) } for some 0 <= r0,r1 < m and 0 <= c0,c1 < n, and score(P) = min( sum_{(i,j) in P} v2(grid[i][j]), sum_{(i,j) in P} v5(grid[i][j]) ).
  Preconditions: Let m = len(grid). There exists an integer n >= 1 such that len(grid[i]) = n for every 0 <= i < m; moreover m >= 1, m*n <= 100000, and 1 <= grid[i][j] <= 1000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n) :
    ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      ∃ P : Finset (Nat × Nat), IsCorneredPath m n P ∧ score grid P = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n), ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      ∃ P : Finset (Nat × Nat), IsCorneredPath m n P ∧ score grid P = r.val) := by
  sorry

/-- Whenever max_trailing_zeros(grid) returns a result r, for every cornered path P in grid, score(P) <= r. Here a cornered path is any union of one contiguous row segment and one contiguous column segment that meet at one endpoint cell of each, including straight and one-cell paths, and score(P) is the minimum of the summed v2 counts and the summed v5 counts over the cells of P.
  Preconditions: Let m = len(grid). There exists an integer n >= 1 such that len(grid[i]) = n for every 0 <= i < m; moreover m >= 1, m*n <= 100000, and 1 <= grid[i][j] <= 1000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n) :
    ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      ∀ P : Finset (Nat × Nat), IsCorneredPath m n P → score grid P ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n), ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      ∀ P : Finset (Nat × Nat), IsCorneredPath m n P → score grid P ≤ r.val) := by
  sorry

/-- If max_trailing_zeros(G) returns r and max_trailing_zeros(H) returns s, then r = s.
  Preconditions: Let G and H be two valid grids with the same number of rows m and the same common row length n, where m >= 1, n >= 1, m*n <= 100000, and all entries of both grids are in 1..1000. For every 0 <= i < m and 0 <= j < n, v2(G[i][j]) = v2(H[i][j]) and v5(G[i][j]) = v5(H[i][j]). -/
theorem spec_6 (G H : Grid) (m n : Nat) (hG : ValidGrid G m n) (hH : ValidGrid H m n)
    (hinv : ∀ i j, i < m → j < n →
      v2 (cellVal G i j) = v2 (cellVal H i j) ∧ v5 (cellVal G i j) = v5 (cellVal H i j)) :
    ∀ r s : Std.I64, max_trailing_zeros G = ok r → max_trailing_zeros H = ok s →
      r.val = s.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (G H : Grid) (m n : Nat) (hG : ValidGrid G m n) (hH : ValidGrid H m n)
    (hinv : ∀ i j, i < m → j < n →
      v2 (cellVal G i j) = v2 (cellVal H i j) ∧ v5 (cellVal G i j) = v5 (cellVal H i j)), ∀ r s : Std.I64, max_trailing_zeros G = ok r → max_trailing_zeros H = ok s →
      r.val = s.val) := by
  sorry

/-- If max_trailing_zeros(G) returns r and max_trailing_zeros(H) returns s, then s >= r.
  Preconditions: Let G and H be two valid grids with the same number of rows m and the same common row length n, where m >= 1, n >= 1, m*n <= 100000, and all entries of both grids are in 1..1000. For every 0 <= i < m and 0 <= j < n, v2(H[i][j]) >= v2(G[i][j]) and v5(H[i][j]) >= v5(G[i][j]). -/
theorem spec_7 (G H : Grid) (m n : Nat) (hG : ValidGrid G m n) (hH : ValidGrid H m n)
    (hmono : ∀ i j, i < m → j < n →
      v2 (cellVal G i j) ≤ v2 (cellVal H i j) ∧ v5 (cellVal G i j) ≤ v5 (cellVal H i j)) :
    ∀ r s : Std.I64, max_trailing_zeros G = ok r → max_trailing_zeros H = ok s →
      r.val ≤ s.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (G H : Grid) (m n : Nat) (hG : ValidGrid G m n) (hH : ValidGrid H m n)
    (hmono : ∀ i j, i < m → j < n →
      v2 (cellVal G i j) ≤ v2 (cellVal H i j) ∧ v5 (cellVal G i j) ≤ v5 (cellVal H i j)), ∀ r s : Std.I64, max_trailing_zeros G = ok r → max_trailing_zeros H = ok s →
      r.val ≤ s.val) := by
  sorry

/-- Whenever max_trailing_zeros(grid) returns a result r, r is at least the maximum of the score of every nonempty contiguous horizontal segment and every nonempty contiguous vertical segment of grid. Explicitly, this lower bound is the maximum of min( sum_{k=l}^{u} v2(grid[i][k]), sum_{k=l}^{u} v5(grid[i][k]) ) over all 0 <= i < m and 0 <= l <= u < n, and of min( sum_{k=l}^{u} v2(grid[k][j]), sum_{k=l}^{u} v5(grid[k][j]) ) over all 0 <= j < n and 0 <= l <= u < m.
  Preconditions: Let m = len(grid). There exists an integer n >= 1 such that len(grid[i]) = n for every 0 <= i < m; moreover m >= 1, m*n <= 100000, and 1 <= grid[i][j] <= 1000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n) :
    ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      (∀ i l u : Nat, i < m → l ≤ u → u < n → hSegScore grid i l u ≤ r.val) ∧
      (∀ j l u : Nat, j < n → l ≤ u → u < m → vSegScore grid j l u ≤ r.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n), ∀ r : Std.I64, max_trailing_zeros grid = ok r →
      (∀ i l u : Nat, i < m → l ≤ u → u < n → hSegScore grid i l u ≤ r.val) ∧
      (∀ j l u : Nat, j < n → l ≤ u → u < m → vSegScore grid j l u ≤ r.val)) := by
  sorry

end AegisSpec.MaxTrailingZeros
