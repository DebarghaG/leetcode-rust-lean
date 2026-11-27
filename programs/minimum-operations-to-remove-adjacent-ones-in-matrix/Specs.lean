import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-operations-to-remove-adjacent-ones-in-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumOperations (minimum_operations)

namespace AegisSpec.MinimumOperations

abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

abbrev Cell : Type := ℕ × ℕ

abbrev Edge : Type := Cell × Cell

def mat (grid : Grid) : List (List ℤ) :=
  grid.val.map fun row => row.val.map fun x => x.val

def nrows (grid : Grid) : ℕ := (mat grid).length

def ncols (grid : Grid) : ℕ := ((mat grid).headD []).length

def cell (grid : Grid) (i j : ℕ) : Option ℤ :=
  ((mat grid)[i]?).bind fun row => row[j]?

def RectBinary (grid : Grid) : Prop :=
  1 ≤ nrows grid ∧ nrows grid ≤ 300 ∧
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 300 ∧
      (∀ row ∈ mat grid, row.length = n) ∧
      (∀ i j : ℕ, i < nrows grid → j < n → cell grid i j = some 0 ∨ cell grid i j = some 1)

def dist (u v : Cell) : ℤ := |(u.1 : ℤ) - (v.1 : ℤ)| + |(u.2 : ℤ) - (v.2 : ℤ)|

def Adj (u v : Cell) : Prop := dist u v = 1

def ltCell (u v : Cell) : Prop := u.1 < v.1 ∨ (u.1 = v.1 ∧ u.2 < v.2)

instance decidableAdj (u v : Cell) : Decidable (Adj u v) := by
  unfold Adj
  infer_instance

instance decidableLtCell (u v : Cell) : Decidable (ltCell u v) := by
  unfold ltCell
  infer_instance

def ones (M : List (List ℤ)) : Finset Cell :=
  ((List.range M.length).flatMap fun i =>
      (List.range ((M.getD i []).length)).filterMap fun j =>
        if (M.getD i []).getD j 0 = 1 then some (i, j) else none).toFinset

def oneCells (grid : Grid) : Finset Cell := ones (mat grid)

def setZeros (M : List (List ℤ)) (S : Finset Cell) : List (List ℤ) :=
  (List.range M.length).map fun i =>
    (List.range ((M.getD i []).length)).map fun j =>
      if (i, j) ∈ S then 0 else (M.getD i []).getD j 0

def Isolated (A : Finset Cell) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, u ≠ v → ¬ Adj u v

def flipCosts (grid : Grid) : Set ℤ :=
  {k : ℤ | ∃ S : Finset Cell,
    S ⊆ oneCells grid ∧ Isolated (ones (setZeros (mat grid) S)) ∧ (S.card : ℤ) = k}

def IsIndependent (A I : Finset Cell) : Prop :=
  I ⊆ A ∧ Isolated I

def IsCover (A C : Finset Cell) : Prop :=
  C ⊆ A ∧ ∀ u ∈ A, ∀ v ∈ A, u ≠ v → Adj u v → u ∈ C ∨ v ∈ C

def IsMatching (A : Finset Cell) (M : Finset Edge) : Prop :=
  (∀ e ∈ M, e.1 ∈ A ∧ e.2 ∈ A ∧ Adj e.1 e.2) ∧
    ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2

def adjPairCount (A : Finset Cell) : ℕ :=
  ((A.product A).filter (fun p : Edge => ltCell p.1 p.2 ∧ Adj p.1 p.2)).card

def runLengthsAux : List ℤ → ℕ → List ℕ → List ℕ
  | [], c, acc => if c = 0 then acc else c :: acc
  | x :: xs, c, acc =>
      if x = 1 then runLengthsAux xs (c + 1) acc
      else runLengthsAux xs 0 (if c = 0 then acc else c :: acc)

def runLengths (row : List ℤ) : List ℕ := (runLengthsAux row 0 []).reverse

/-- Let O = {(i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1}. For S subset of O, let flip(S) be the matrix obtained from grid by changing exactly the cells in S to 0 and changing no other cell. A matrix is well-isolated if no two distinct 1-cells (i,j),(i',j') in it satisfy |i-i'| + |j-j'| = 1. Let F = { |S| | S subset of O and flip(S) is well-isolated }. The function returns a result r and r = min F. (F is nonempty because S = O is valid.)
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_1 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧ IsLeast (flipCosts grid) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r ∧ IsLeast (flipCosts grid) r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_2 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r) := by
  sorry

/-- Let k be the number of cells (i,j) with grid[i][j] = 1. The function returns a result r and 0 <= r <= floor(k/2).
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_3 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (((oneCells grid).card / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (((oneCells grid).card / 2 : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0 if and only if grid is well-isolated, i.e., there do not exist distinct cells (i,j),(i',j') with grid[i][j] = 1, grid[i'][j'] = 1, and |i-i'| + |j-j'| = 1.
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_4 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      (r.val = 0 ↔ Isolated (oneCells grid)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      (r.val = 0 ↔ Isolated (oneCells grid))) := by
  sorry

/-- Let O = {(i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1}. Two distinct cells (i,j),(i',j') in O are adjacent when |i-i'| + |j-j'| = 1. The function returns a result r and r equals the maximum cardinality of a set M of unordered pairs {u,v} such that u and v are adjacent cells of O and no cell of O occurs in more than one pair of M.
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_5 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      ∃ M : Finset Edge, IsMatching (oneCells grid) M ∧
        (M.card : ℤ) = r.val ∧ ∀ M', IsMatching (oneCells grid) M' → M'.card ≤ M.card := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      ∃ M : Finset Edge, IsMatching (oneCells grid) M ∧
        (M.card : ℤ) = r.val ∧ ∀ M', IsMatching (oneCells grid) M' → M'.card ≤ M.card) := by
  sorry

/-- Let O = {(i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1}. The function returns a result r and r equals the minimum cardinality of a set C subset of O such that for every two distinct cells u=(i,j), v=(i',j') in O with |i-i'| + |j-j'| = 1, at least one of u and v belongs to C.
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_6 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      ∃ C : Finset Cell, IsCover (oneCells grid) C ∧
        (C.card : ℤ) = r.val ∧ ∀ C', IsCover (oneCells grid) C' → C.card ≤ C'.card := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      ∃ C : Finset Cell, IsCover (oneCells grid) C ∧
        (C.card : ℤ) = r.val ∧ ∀ C', IsCover (oneCells grid) C' → C.card ≤ C'.card) := by
  sorry

/-- Let O = {(i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1} and let k = |O|. Let alpha be the maximum cardinality of a set I subset of O such that no two distinct cells of I are 4-directionally adjacent (i.e., for any (i,j),(i',j') in I, |i-i'| + |j-j'| != 1). The function returns a result r and r = k - alpha.
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_7 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      ∃ I : Finset Cell, IsIndependent (oneCells grid) I ∧
        (∀ I', IsIndependent (oneCells grid) I' → I'.card ≤ I.card) ∧
        r.val = ((oneCells grid).card : ℤ) - (I.card : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      ∃ I : Finset Cell, IsIndependent (oneCells grid) I ∧
        (∀ I', IsIndependent (oneCells grid) I' → I'.card ≤ I.card) ∧
        r.val = ((oneCells grid).card : ℤ) - (I.card : ℤ)) := by
  sorry

/-- Let rA and rB be the results returned by the function on A and B respectively. Then rA <= rB.
  Preconditions: Let A and B be two inputs satisfying the same rectangular-binary preconditions, with the same dimensions m,n, and A[i][j] <= B[i][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (A B : Grid) (hA : RectBinary A) (hB : RectBinary B)
    (hm : nrows A = nrows B) (hn : ncols A = ncols B)
    (hle : ∀ i j : ℕ, i < nrows A → j < ncols A →
      ∃ a b : ℤ, cell A i j = some a ∧ cell B i j = some b ∧ a ≤ b) :
    ∃ rA rB : Std.I64, minimum_operations A = ok rA ∧ minimum_operations B = ok rB ∧
      rA.val ≤ rB.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (A B : Grid) (hA : RectBinary A) (hB : RectBinary B)
    (hm : nrows A = nrows B) (hn : ncols A = ncols B)
    (hle : ∀ i j : ℕ, i < nrows A → j < ncols A →
      ∃ a b : ℤ, cell A i j = some a ∧ cell B i j = some b ∧ a ≤ b), ∃ rA rB : Std.I64, minimum_operations A = ok rA ∧ minimum_operations B = ok rB ∧
      rA.val ≤ rB.val) := by
  sorry

/-- Let T be the n-by-m matrix defined by T[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Let r be the result returned by the function on grid and let rT be the result returned on T. Then r = rT.
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_9 (grid T : Grid) (h : RectBinary grid) (hT : mat T = (mat grid).transpose) :
    ∃ r rT : Std.I64, minimum_operations grid = ok r ∧ minimum_operations T = ok rT ∧
      r = rT := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid T : Grid) (h : RectBinary grid) (hT : mat T = (mat grid).transpose), ∃ r rT : Std.I64, minimum_operations grid = ok r ∧ minimum_operations T = ok rT ∧
      r = rT) := by
  sorry

/-- Let the maximal contiguous runs of 1s in the single row grid[0][0..n-1] have lengths L_1,...,L_q, where q >= 0 and each run is a maximal interval of columns whose entries are all 1. The function returns a result r and r = sum_{t=1..q} floor(L_t/2).
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1; and m = 1. -/
theorem spec_10 (grid : Grid) (h : RectBinary grid) (h1 : nrows grid = 1) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      r.val = (((runLengths ((mat grid).headD [])).map fun L => L / 2).sum : ℕ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid) (h1 : nrows grid = 1), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      r.val = (((runLengths ((mat grid).headD [])).map fun L => L / 2).sum : ℕ)) := by
  sorry

/-- Let R be the m-by-n matrix obtained by reversing the rows of grid: R[i][j] = grid[m-1-i][j] for 0 <= i < m and 0 <= j < n. Let r be the result returned by the function on grid and let rR be the result returned on R. Then r = rR.
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_11 (grid R : Grid) (h : RectBinary grid) (hR : mat R = (mat grid).reverse) :
    ∃ r rR : Std.I64, minimum_operations grid = ok r ∧ minimum_operations R = ok rR ∧
      r = rR := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid R : Grid) (h : RectBinary grid) (hR : mat R = (mat grid).reverse), ∃ r rR : Std.I64, minimum_operations grid = ok r ∧ minimum_operations R = ok rR ∧
      r = rR) := by
  sorry

/-- If grid[i][j] = 1 for every 0 <= i < m and 0 <= j < n, then the function returns a result r and r = floor(m*n/2).
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_12 (grid : Grid) (h : RectBinary grid)
    (hall : ∀ i j : ℕ, i < nrows grid → j < ncols grid → cell grid i j = some 1) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      r.val = (((nrows grid * ncols grid) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid)
    (hall : ∀ i j : ℕ, i < nrows grid → j < ncols grid → cell grid i j = some 1), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      r.val = (((nrows grid * ncols grid) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Let E be the number of unordered pairs { (i,j),(i',j') } of cells such that grid[i][j] = 1, grid[i'][j'] = 1, and |i-i'| + |j-j'| = 1. The function returns a result r and r <= E.
  Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 300; there exists n with 1 <= n <= 300 such that for every i with 0 <= i < m, len(grid[i]) = n; and for every i with 0 <= i < m and j with 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_13 (grid : Grid) (h : RectBinary grid) :
    ∃ r : Std.I64, minimum_operations grid = ok r ∧
      r.val ≤ ((adjPairCount (oneCells grid) : ℕ) : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Grid) (h : RectBinary grid), ∃ r : Std.I64, minimum_operations grid = ok r ∧
      r.val ≤ ((adjPairCount (oneCells grid) : ℕ) : ℤ)) := by
  sorry

end AegisSpec.MinimumOperations
