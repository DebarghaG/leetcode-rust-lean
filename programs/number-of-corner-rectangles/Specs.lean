import Aegis.CountCornerRectangles.Code.Funs

/-!
# Specifications of `Aegis.CountCornerRectangles.count_corner_rectangles`

LeetCode problem `number-of-corner-rectangles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountCornerRectangles

def toMatrix (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun v => v.val.map (fun x => x.val))

def nrows (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  grid.val.length

def row (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  (toMatrix grid).getD i []

def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (row grid i).getD j 0

def binom2 (a : Nat) : Nat := a * (a - 1) / 2

def onesCount (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
  ((List.range m).map (fun i =>
      ((List.range n).filter (fun j => decide (entry grid i j = 1))).length)).foldl
    (fun a b => a + b) 0

def rectCount (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
  ((((List.range m).product (List.range m)).product
        ((List.range n).product (List.range n))).filter
      (fun q =>
        decide (q.1.1 < q.1.2 ∧ q.2.1 < q.2.2 ∧
          entry grid q.1.1 q.2.1 = 1 ∧ entry grid q.1.1 q.2.2 = 1 ∧
          entry grid q.1.2 q.2.1 = 1 ∧ entry grid q.1.2 q.2.2 = 1))).length

def commonCols (grid : Slice (alloc.vec.Vec Std.I64)) (i k n : Nat) : Nat :=
  ((List.range n).filter (fun j => decide (entry grid i j = 1 ∧ entry grid k j = 1))).length

def commonRows (grid : Slice (alloc.vec.Vec Std.I64)) (j l m : Nat) : Nat :=
  ((List.range m).filter (fun i => decide (entry grid i j = 1 ∧ entry grid i l = 1))).length

def rowPairSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
  (((List.range m).product (List.range m)).map
      (fun p => if p.1 < p.2 then binom2 (commonCols grid p.1 p.2 n) else 0)).foldl
    (fun a b => a + b) 0

def colPairSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
  (((List.range n).product (List.range n)).map
      (fun p => if p.1 < p.2 then binom2 (commonRows grid p.1 p.2 m) else 0)).foldl
    (fun a b => a + b) 0

def IsTranspose (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  nrows gridT = n ∧ (∀ a, a < n → (row gridT a).length = m) ∧
    ∀ a b, a < n → b < m → entry gridT a b = entry grid b a

def IsDeleteRow (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n k : Nat) : Prop :=
  k < m ∧ nrows grid' = m - 1 ∧ (∀ i, i < m - 1 → (row grid' i).length = n) ∧
    ∀ i j, i < m - 1 → j < n →
      entry grid' i j = if i < k then entry grid i j else entry grid (i + 1) j

def IsDeleteCol (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n l : Nat) : Prop :=
  l < n ∧ nrows grid' = m ∧ (∀ i, i < m → (row grid' i).length = n - 1) ∧
    ∀ i j, i < m → j < n - 1 →
      entry grid' i j = if j < l then entry grid i j else entry grid i (j + 1)

/-- The function returns a result r, and r equals the number of pairs ((i,k),(j,l)) such that 0 <= i < k < m, 0 <= j < l < n, and grid[i][j] = 1, grid[i][l] = 1, grid[k][j] = 1, grid[k][l] = 1. Each such quadruple represents one corner rectangle; entries strictly inside the rectangle are unrestricted.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000) :
    ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r ∧
      r.val = ((rectCount grid m n : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000), ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r ∧
      r.val = ((rectCount grid m n : Nat) : Int)) := by
  sorry

/-- The function returns some integer r; that is, under these preconditions the call does not fail, panic, or overflow.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000) :
    ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000), ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r) := by
  sorry

/-- Let r be the returned integer. Then 0 <= r <= C(m,2)*C(n,2), where C(a,2) = a*(a-1)/2. Equivalently, r is at most the number of ways to choose two distinct rows and two distinct columns.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      0 ≤ r.val ∧ r.val ≤ (((binom2 m * binom2 n : Nat)) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      0 ≤ r.val ∧ r.val ≤ (((binom2 m * binom2 n : Nat)) : Int)) := by
  sorry

/-- The function returns r = 0.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. In addition, m < 2 or n < 2. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hedge : m < 2 ∨ n < 2) :
    ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hedge : m < 2 ∨ n < 2), ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r = C(m,2)*C(n,2) = (m*(m-1)/2)*(n*(n-1)/2).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1. In addition, grid[i][j] = 1 for every 0 <= i < m and 0 <= j < n, and the total number K = m*n of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hall : ∀ i j, i < m → j < n → entry grid i j = 1)
    (hK : 1 ≤ m * n ∧ m * n ≤ 6000) :
    ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r ∧
      r.val = (((binom2 m * binom2 n : Nat)) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hall : ∀ i j, i < m → j < n → entry grid i j = 1)
    (hK : 1 ≤ m * n ∧ m * n ≤ 6000), ∃ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r ∧
      r.val = (((binom2 m * binom2 n : Nat)) : Int)) := by
  sorry

/-- Let r be the returned integer. Then r > 0 if and only if there exist indices i,k,j,l with 0 <= i < k < m and 0 <= j < l < n such that grid[i][j]=1, grid[i][l]=1, grid[k][j]=1, and grid[k][l]=1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      (0 < r.val ↔ ∃ i k j l, i < k ∧ k < m ∧ j < l ∧ l < n ∧
        entry grid i j = 1 ∧ entry grid i l = 1 ∧
        entry grid k j = 1 ∧ entry grid k l = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      (0 < r.val ↔ ∃ i k j l, i < k ∧ k < m ∧ j < l ∧ l < n ∧
        entry grid i j = 1 ∧ entry grid i l = 1 ∧
        entry grid k j = 1 ∧ entry grid k l = 1)) := by
  sorry

/-- Let gridT be the n-by-m matrix defined by gridT[a][b] = grid[b][a] for 0 <= a < n and 0 <= b < m. The function returns results r for grid and rT for gridT, and r = rT.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_7 (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hT : IsTranspose grid gridT m n) :
    ∀ r rT, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles gridT = ok rT →
      r.val = rT.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hT : IsTranspose grid gridT m n), ∀ r rT, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles gridT = ok rT →
      r.val = rT.val) := by
  sorry

/-- For every bijection sigma from {0,...,m-1} to itself and every bijection tau from {0,...,n-1} to itself, define grid' by grid'[i][j] = grid[sigma(i)][tau(j)] for 0 <= i < m and 0 <= j < n. If r is the result for grid and r' is the result for grid', then r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_8 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hlen' : nrows grid' = m)
    (hrows' : ∀ i, i < m → (row grid' i).length = n)
    (sigma : Fin m → Fin m) (tau : Fin n → Fin n)
    (hsigma : Function.Bijective sigma) (htau : Function.Bijective tau)
    (hperm : ∀ (i : Nat) (hi : i < m) (j : Nat) (hj : j < n),
      entry grid' i j = entry grid (sigma ⟨i, hi⟩) (tau ⟨j, hj⟩)) :
    ∀ r r', Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles grid' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hlen' : nrows grid' = m)
    (hrows' : ∀ i, i < m → (row grid' i).length = n)
    (sigma : Fin m → Fin m) (tau : Fin n → Fin n)
    (hsigma : Function.Bijective sigma) (htau : Function.Bijective tau)
    (hperm : ∀ (i : Nat) (hi : i < m) (j : Nat) (hj : j < n),
      entry grid' i j = entry grid (sigma ⟨i, hi⟩) (tau ⟨j, hj⟩)), ∀ r r', Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles grid' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Let grid' be the (m-1)-by-n matrix obtained by deleting row k, so grid'[i][j] = grid[i][j] for 0 <= i < k and grid'[i][j] = grid[i+1][j] for k <= i < m-1. If r is the result for grid and r' is the result for grid', then r' = r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. In addition, m >= 2 and there exists an index k with 0 <= k < m such that grid[k][j] = 0 for every 0 <= j < n. -/
theorem spec_9 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hm2 : 2 ≤ m) (k : Nat) (hk : k < m) (hzero : ∀ j, j < n → entry grid k j = 0)
    (hdel : IsDeleteRow grid grid' m n k) :
    ∀ r r', Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles grid' = ok r' →
      r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hm2 : 2 ≤ m) (k : Nat) (hk : k < m) (hzero : ∀ j, j < n → entry grid k j = 0)
    (hdel : IsDeleteRow grid grid' m n k), ∀ r r', Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles grid' = ok r' →
      r'.val = r.val) := by
  sorry

/-- Let grid' be the m-by-(n-1) matrix obtained by deleting column l, so grid'[i][j] = grid[i][j] for 0 <= j < l and grid'[i][j] = grid[i][j+1] for l <= j < n-1. If r is the result for grid and r' is the result for grid', then r' = r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. In addition, n >= 2 and there exists an index l with 0 <= l < n such that grid[i][l] = 0 for every 0 <= i < m. -/
theorem spec_10 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hn2 : 2 ≤ n) (l : Nat) (hl : l < n) (hzero : ∀ i, i < m → entry grid i l = 0)
    (hdel : IsDeleteCol grid grid' m n l) :
    ∀ r r', Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles grid' = ok r' →
      r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hn2 : 2 ≤ n) (l : Nat) (hl : l < n) (hzero : ∀ i, i < m → entry grid i l = 0)
    (hdel : IsDeleteCol grid grid' m n l), ∀ r r', Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      Aegis.CountCornerRectangles.count_corner_rectangles grid' = ok r' →
      r'.val = r.val) := by
  sorry

/-- If rG is the result for G and rH is the result for H, then rG <= rH.
  Preconditions: Let m and n be positive integers with m <= 200 and n <= 200. Let G and H be two m-by-n matrices such that each of G and H has only 0 or 1 entries and has between 1 and 6000 entries equal to 1. Assume G[i][j] <= H[i][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (G H : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hGlen : nrows G = m) (hGrows : ∀ i, i < m → (row G i).length = n)
    (hHlen : nrows H = m) (hHrows : ∀ i, i < m → (row H i).length = n)
    (hGbin : ∀ i j, i < m → j < n → entry G i j = 0 ∨ entry G i j = 1)
    (hHbin : ∀ i j, i < m → j < n → entry H i j = 0 ∨ entry H i j = 1)
    (hGK : 1 ≤ onesCount G m n ∧ onesCount G m n ≤ 6000)
    (hHK : 1 ≤ onesCount H m n ∧ onesCount H m n ≤ 6000)
    (hle : ∀ i j, i < m → j < n → entry G i j ≤ entry H i j) :
    ∀ rG rH, Aegis.CountCornerRectangles.count_corner_rectangles G = ok rG →
      Aegis.CountCornerRectangles.count_corner_rectangles H = ok rH →
      rG.val ≤ rH.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (G H : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hGlen : nrows G = m) (hGrows : ∀ i, i < m → (row G i).length = n)
    (hHlen : nrows H = m) (hHrows : ∀ i, i < m → (row H i).length = n)
    (hGbin : ∀ i j, i < m → j < n → entry G i j = 0 ∨ entry G i j = 1)
    (hHbin : ∀ i j, i < m → j < n → entry H i j = 0 ∨ entry H i j = 1)
    (hGK : 1 ≤ onesCount G m n ∧ onesCount G m n ≤ 6000)
    (hHK : 1 ≤ onesCount H m n ∧ onesCount H m n ≤ 6000)
    (hle : ∀ i j, i < m → j < n → entry G i j ≤ entry H i j), ∀ rG rH, Aegis.CountCornerRectangles.count_corner_rectangles G = ok rG →
      Aegis.CountCornerRectangles.count_corner_rectangles H = ok rH →
      rG.val ≤ rH.val) := by
  sorry

/-- Define k as the number of columns c with 0 <= c < n such that grid[0][c] = 1 and grid[1][c] = 1. If r is the returned integer, then r = C(k,2) = k*(k-1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. In addition, m = 2. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hm2 : m = 2) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((binom2 (commonCols grid 0 1 n) : Nat) : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hm2 : m = 2), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((binom2 (commonCols grid 0 1 n) : Nat) : Int)) := by
  sorry

/-- Define k as the number of rows i with 0 <= i < m such that grid[i][0] = 1 and grid[i][1] = 1. If r is the returned integer, then r = C(k,2) = k*(k-1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. In addition, n = 2. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hn2 : n = 2) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((binom2 (commonRows grid 0 1 m) : Nat) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hn2 : n = 2), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((binom2 (commonRows grid 0 1 m) : Nat) : Int)) := by
  sorry

/-- Let r be the returned integer. Then r is either 0 or 1. Moreover, r = 1 if and only if there exist indices 0 <= i < k < m and 0 <= j < l < n such that the set of cells (a,b) with grid[a][b] = 1 is exactly {(i,j),(i,l),(k,j),(k,l)}.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. In addition, K = 4. -/
theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hK4 : onesCount grid m n = 4) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      (r.val = 0 ∨ r.val = 1) ∧
      (r.val = 1 ↔ ∃ i k j l, i < k ∧ k < m ∧ j < l ∧ l < n ∧
        ∀ a b, a < m → b < n →
          (entry grid a b = 1 ↔
            (a = i ∧ b = j) ∨ (a = i ∧ b = l) ∨ (a = k ∧ b = j) ∨ (a = k ∧ b = l))) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000)
    (hK4 : onesCount grid m n = 4), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      (r.val = 0 ∨ r.val = 1) ∧
      (r.val = 1 ↔ ∃ i k j l, i < k ∧ k < m ∧ j < l ∧ l < n ∧
        ∀ a b, a < m → b < n →
          (entry grid a b = 1 ↔
            (a = i ∧ b = j) ∨ (a = i ∧ b = l) ∨ (a = k ∧ b = j) ∨ (a = k ∧ b = l)))) := by
  sorry

/-- Let r be the returned integer. Then r <= C(K,2) = K*(K-1)/2, where K is the total number of 1-entries in grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_15 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val ≤ ((binom2 (onesCount grid m n) : Nat) : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val ≤ ((binom2 (onesCount grid m n) : Nat) : Int)) := by
  sorry

/-- For each pair of rows 0 <= i < k < m, let c(i,k) be the number of columns j with 0 <= j < n such that grid[i][j] = 1 and grid[k][j] = 1. Then the returned result r equals sum_{0 <= i < k < m} C(c(i,k),2) = sum_{0 <= i < k < m} c(i,k)*(c(i,k)-1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_16 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((rowPairSum grid m n : Nat) : Int) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((rowPairSum grid m n : Nat) : Int)) := by
  sorry

/-- For each pair of columns 0 <= j < l < n, let d(j,l) be the number of rows i with 0 <= i < m such that grid[i][j] = 1 and grid[i][l] = 1. Then the returned result r equals sum_{0 <= j < l < n} C(d(j,l),2) = sum_{0 <= j < l < n} d(j,l)*(d(j,l)-1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, every entry grid[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and the total number K of entries equal to 1 satisfies 1 <= K <= 6000. -/
theorem spec_17 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000) :
    ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((colPairSum grid m n : Nat) : Int) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
    (hlen : nrows grid = m)
    (hrows : ∀ i, i < m → (row grid i).length = n)
    (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
    (hK : 1 ≤ onesCount grid m n ∧ onesCount grid m n ≤ 6000), ∀ r, Aegis.CountCornerRectangles.count_corner_rectangles grid = ok r →
      r.val = ((colPairSum grid m n : Nat) : Int)) := by
  sorry

end AegisSpec.CountCornerRectangles
