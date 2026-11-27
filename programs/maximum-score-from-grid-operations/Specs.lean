import Aegis.MaximumScore.Code.Funs

/-!
# Specifications of `Aegis.MaximumScore.maximum_score`

LeetCode problem `maximum-score-from-grid-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumScore

def entries (grid : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def cell (M : List (List ℤ)) (i j : Nat) : ℤ := (M.getD i []).getD j 0

def isBlack (h : Nat → ℤ) (i j : Nat) : Prop := 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ h j

instance (h : Nat → ℤ) (i j : Nat) : Decidable (isBlack h i j) :=
  inferInstanceAs (Decidable (0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ h j))

def score (M : List (List ℤ)) (n : Nat) (h : Nat → ℤ) : ℤ :=
  (Finset.range n).sum (fun i =>
    (Finset.range n).sum (fun j =>
      if ¬ isBlack h i j ∧
          ((0 < j ∧ isBlack h i (j - 1)) ∨ (j < n - 1 ∧ isBlack h i (j + 1)))
      then cell M i j else 0))

def ValidPlan (n : Nat) (h : Nat → ℤ) : Prop :=
  ∀ j, j < n → -1 ≤ h j ∧ h j ≤ (n : ℤ) - 1

def Achievable (M : List (List ℤ)) (n : Nat) (r : ℤ) : Prop :=
  ∃ h, ValidPlan n h ∧ score M n h = r

def IsMaxScore (M : List (List ℤ)) (n : Nat) (r : ℤ) : Prop :=
  Achievable M n r ∧ ∀ h, ValidPlan n h → score M n h ≤ r

def totalSum (M : List (List ℤ)) (n : Nat) : ℤ :=
  (Finset.range n).sum (fun i => (Finset.range n).sum (fun j => cell M i j))

def colSum (M : List (List ℤ)) (n j : Nat) : ℤ :=
  (Finset.range n).sum (fun i => cell M i j)

def minEntry (M : List (List ℤ)) (n : Nat) : ℤ :=
  match n with
  | 0 => 0
  | k + 1 =>
    (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).inf'
      ⟨(⟨0, Nat.succ_pos k⟩, ⟨0, Nat.succ_pos k⟩), Finset.mem_univ _⟩
      (fun p => cell M p.1.val p.2.val)

def opCount (n : Nat) (h : Nat → ℤ) : Nat :=
  ((Finset.range n).filter (fun j => 0 ≤ h j)).card

def isValidGrid (grid : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧ grid.val.length = n ∧
    (∀ i, i < n → ((entries grid).getD i []).length = n) ∧
    (∀ i j, i < n → j < n →
      0 ≤ cell (entries grid) i j ∧ cell (entries grid) i j ≤ 10 ^ 9)

/-- For every h = (h_0,...,h_{n-1}) in {-1,0,...,n-1}^n, let B_h(i,j) mean 0 <= i <= h_j, so h_j = -1 means column j has no black cells and h_j >= 0 means rows 0 through h_j of column j are black. Let W_h(i,j) mean not B_h(i,j). Define S(grid,h) = sum_{i=0}^{n-1} sum_{j=0}^{n-1} [ W_h(i,j) and ((j > 0 and B_h(i,j-1)) or (j < n-1 and B_h(i,j+1))) ] * grid[i][j], where [condition] is 1 if the condition holds and 0 otherwise. The function returns a result r, does not fail, and r = max { S(grid,h) : h in {-1,0,...,n-1}^n }.
  Preconditions: Let n = len(grid). The grid is an n by n matrix: 1 <= n <= 100, every row grid[i] has length n, and for every 0 <= i < n and 0 <= j < n, grid[i][j] is an integer with 0 <= grid[i][j] <= 10^9. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) :
    ∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r ∧
      IsMaxScore (entries grid) n r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n), ∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r ∧
      IsMaxScore (entries grid) n r.val) := by
  sorry

/-- The function returns a result r on every such input; it does not panic, go out of bounds, or overflow 64-bit signed arithmetic.
  Preconditions: Let n = len(grid). The grid is an n by n matrix: 1 <= n <= 100, every row grid[i] has length n, and for every 0 <= i < n and 0 <= j < n, grid[i][j] is an integer with 0 <= grid[i][j] <= 10^9. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) :
    ∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n), ∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= (sum_{i=0}^{n-1} sum_{j=0}^{n-1} grid[i][j]) - min{ grid[i][j] : 0 <= i < n and 0 <= j < n }.
  Preconditions: Let n = len(grid). The grid is an n by n matrix: 1 <= n <= 100, every row grid[i] has length n, and for every 0 <= i < n and 0 <= j < n, grid[i][j] is an integer with 0 <= grid[i][j] <= 10^9. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) :
    ∀ r : I64, Aegis.MaximumScore.maximum_score grid = ok r →
      0 ≤ r.val ∧
        r.val ≤ totalSum (entries grid) n - minEntry (entries grid) n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n), ∀ r : I64, Aegis.MaximumScore.maximum_score grid = ok r →
      0 ≤ r.val ∧
        r.val ≤ totalSum (entries grid) n - minEntry (entries grid) n) := by
  sorry

/-- Whenever the function returns a result r, r >= max{ sum_{i=0}^{n-1} grid[i][j] : 0 <= j < n }.
  Preconditions: Let n = len(grid). The grid is an n by n matrix with n >= 2, 1 <= n <= 100, every row grid[i] has length n, and for every 0 <= i < n and 0 <= j < n, grid[i][j] is an integer with 0 <= grid[i][j] <= 10^9. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) (hn : 2 ≤ n) :
    ∀ r : I64, Aegis.MaximumScore.maximum_score grid = ok r →
      ∀ j : Fin n, colSum (entries grid) n j.val ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) (hn : 2 ≤ n), ∀ r : I64, Aegis.MaximumScore.maximum_score grid = ok r →
      ∀ j : Fin n, colSum (entries grid) n j.val ≤ r.val) := by
  sorry

/-- Under these preconditions, the function returns 0 if and only if grid[i][j] = 0 for every 0 <= i < n and every 0 <= j < n.
  Preconditions: Let n = len(grid). The grid is an n by n matrix with n >= 2, 1 <= n <= 100, every row grid[i] has length n, and for every 0 <= i < n and 0 <= j < n, grid[i][j] is an integer with 0 <= grid[i][j] <= 10^9. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) (hn : 2 ≤ n) :
    (∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r ∧ r.val = 0) ↔
      (∀ i j, i < n → j < n → cell (entries grid) i j = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) (hn : 2 ≤ n), (∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r ∧ r.val = 0) ↔
      (∀ i j, i < n → j < n → cell (entries grid) i j = 0)) := by
  sorry

/-- If there exists a column index j0 with 0 <= j0 < n such that grid[i][j] = 0 for every 0 <= i < n and every j != j0, then the function returns sum_{i=0}^{n-1} grid[i][j0].
  Preconditions: Let n = len(grid). The grid is an n by n matrix with n >= 2, 1 <= n <= 100, every row grid[i] has length n, and for every 0 <= i < n and 0 <= j < n, grid[i][j] is an integer with 0 <= grid[i][j] <= 10^9. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) (hn : 2 ≤ n) :
    ∀ j0, j0 < n →
      (∀ i j, i < n → j < n → j ≠ j0 → cell (entries grid) i j = 0) →
      ∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r ∧
        r.val = colSum (entries grid) n j0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) (hn : 2 ≤ n), ∀ j0, j0 < n →
      (∀ i j, i < n → j < n → j ≠ j0 → cell (entries grid) i j = 0) →
      ∃ r : I64, Aegis.MaximumScore.maximum_score grid = ok r ∧
        r.val = colSum (entries grid) n j0) := by
  sorry

/-- If r_A is the result returned on A and r_B is the result returned on B, then r_A <= r_B.
  Preconditions: Let A and B be two valid n by n grids for the same n, with 1 <= n <= 100, all row lengths equal to n, and 0 <= A[i][j] <= B[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < n. -/
theorem spec_7 (A B : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hA : isValidGrid A n) (hB : isValidGrid B n)
    (hle : ∀ i j, i < n → j < n → cell (entries A) i j ≤ cell (entries B) i j) :
    ∀ rA rB : I64, Aegis.MaximumScore.maximum_score A = ok rA →
      Aegis.MaximumScore.maximum_score B = ok rB → rA.val ≤ rB.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hA : isValidGrid A n) (hB : isValidGrid B n)
    (hle : ∀ i j, i < n → j < n → cell (entries A) i j ≤ cell (entries B) i j), ∀ rA rB : I64, Aegis.MaximumScore.maximum_score A = ok rA →
      Aegis.MaximumScore.maximum_score B = ok rB → rA.val ≤ rB.val) := by
  sorry

/-- If r_A is the result returned on A and r_B is the result returned on B, then r_B = c * r_A.
  Preconditions: Let A be a valid n by n grid, 1 <= n <= 100, with 0 <= A[i][j] <= 10^9. Let c be an integer with c >= 0, and let B be the n by n grid B[i][j] = c * A[i][j], assuming 0 <= B[i][j] <= 10^9 for every i,j. -/
theorem spec_8 (A B : Slice (alloc.vec.Vec I64)) (n : Nat) (c : ℤ)
    (hA : isValidGrid A n) (hB : isValidGrid B n) (hc : 0 ≤ c)
    (hscale : ∀ i j, i < n → j < n →
      cell (entries B) i j = c * cell (entries A) i j) :
    ∀ rA rB : I64, Aegis.MaximumScore.maximum_score A = ok rA →
      Aegis.MaximumScore.maximum_score B = ok rB → rB.val = c * rA.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec I64)) (n : Nat) (c : ℤ)
    (hA : isValidGrid A n) (hB : isValidGrid B n) (hc : 0 ≤ c)
    (hscale : ∀ i j, i < n → j < n →
      cell (entries B) i j = c * cell (entries A) i j), ∀ rA rB : I64, Aegis.MaximumScore.maximum_score A = ok rA →
      Aegis.MaximumScore.maximum_score B = ok rB → rB.val = c * rA.val) := by
  sorry

/-- If r_A, r_B, and r_C are the results returned on A, B, and C respectively, then r_C <= r_A + r_B.
  Preconditions: Let A and B be valid n by n grids for the same n, 1 <= n <= 100, with 0 <= A[i][j] <= 10^9 and 0 <= B[i][j] <= 10^9. Let C be defined by C[i][j] = A[i][j] + B[i][j], and assume 0 <= C[i][j] <= 10^9 for every i,j. -/
theorem spec_9 (A B C : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hA : isValidGrid A n) (hB : isValidGrid B n) (hC : isValidGrid C n)
    (hadd : ∀ i j, i < n → j < n →
      cell (entries C) i j = cell (entries A) i j + cell (entries B) i j) :
    ∀ rA rB rC : I64, Aegis.MaximumScore.maximum_score A = ok rA →
      Aegis.MaximumScore.maximum_score B = ok rB →
      Aegis.MaximumScore.maximum_score C = ok rC →
      rC.val ≤ rA.val + rB.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (A B C : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hA : isValidGrid A n) (hB : isValidGrid B n) (hC : isValidGrid C n)
    (hadd : ∀ i j, i < n → j < n →
      cell (entries C) i j = cell (entries A) i j + cell (entries B) i j), ∀ rA rB rC : I64, Aegis.MaximumScore.maximum_score A = ok rA →
      Aegis.MaximumScore.maximum_score B = ok rB →
      Aegis.MaximumScore.maximum_score C = ok rC →
      rC.val ≤ rA.val + rB.val) := by
  sorry

/-- Whenever the function returns a result r, there exists h = (h_0,...,h_{n-1}) in {-1,0,...,n-1}^n such that the operation plan which, for each column j with h_j >= 0, colors rows 0 through h_j of column j black, and does nothing in columns with h_j = -1, has score exactly r. In particular, r is attainable using at most one operation per column, hence at most n operations.
  Preconditions: Let n = len(grid). The grid is an n by n matrix: 1 <= n <= 100, every row grid[i] has length n, and for every 0 <= i < n and 0 <= j < n, grid[i][j] is an integer with 0 <= grid[i][j] <= 10^9. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n) :
    ∀ r : I64, Aegis.MaximumScore.maximum_score grid = ok r →
      ∃ h : Nat → ℤ, ValidPlan n h ∧ score (entries grid) n h = r.val ∧
        opCount n h ≤ n := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat)
    (hvalid : isValidGrid grid n), ∀ r : I64, Aegis.MaximumScore.maximum_score grid = ok r →
      ∃ h : Nat → ℤ, ValidPlan n h ∧ score (entries grid) n h = r.val ∧
        opCount n h ≤ n) := by
  sorry

end AegisSpec.MaximumScore
