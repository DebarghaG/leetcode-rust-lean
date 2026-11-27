import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `maximum-sum-with-at-most-k-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxSum

namespace AegisSpec.MaxSum

def rows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun r => r.val.map (fun v => v.val))

def nrows (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := (rows grid).length

def row (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int := (rows grid).getD i []

def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat := (row grid i).length

def ncols (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := rowLen grid 0

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int := (row grid i).getD j 0

def limitAt (limits : Slice Std.I64) (i : Nat) : Int := (limits.val.getD i 0#i64).val

def allCells (grid : Slice (alloc.vec.Vec Std.I64)) : List Int := (rows grid).flatten

def topList (l : List Int) (κ : Int) : List Int :=
  if κ ≤ 0 then [] else (l.mergeSort (fun a b => a ≥ b)).take κ.toNat

def topSumI (l : List Int) (κ : Int) : Int := (topList l κ).sum

def perRowTopList (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) : List Int :=
  ((List.range (nrows grid)).flatMap (fun i => topList (row grid i) (limitAt limits i)))

def perRowTopSum (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) : Int :=
  ((List.range (nrows grid)).map (fun i => topSumI (row grid i) (limitAt limits i))).sum

def eligibleCells (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) : List Int :=
  ((List.range (nrows grid)).filter (fun i => 1 ≤ limitAt limits i)).flatMap (fun i =>
    row grid i)

def maxEligible (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) : Int :=
  (eligibleCells grid limits).foldl (fun a b => if a ≤ b then b else a) 0

def weight (grid : Slice (alloc.vec.Vec Std.I64)) (S : Finset (Nat × Nat)) : Int :=
  S.sum (fun p => cell grid p.1 p.2)

def Feasible (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (κ : Int)
    (S : Finset (Nat × Nat)) : Prop :=
  (∀ p ∈ S, p.1 < nrows grid ∧ p.2 < rowLen grid p.1) ∧
    (∀ i, ((S.filter (fun p => p.1 = i)).card : Int) ≤ limitAt limits i) ∧
      (S.card : Int) ≤ κ

def IsMaxTotal (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (κ : Int)
    (v : Int) : Prop :=
  (∀ S, Feasible grid limits κ S → weight grid S ≤ v) ∧
    ∃ S, Feasible grid limits κ S ∧ weight grid S = v

def GridOk (grid : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ nrows grid ∧ nrows grid ≤ 500 ∧ 1 ≤ ncols grid ∧ ncols grid ≤ 500 ∧
    (∀ i, i < nrows grid → rowLen grid i = ncols grid) ∧
      (∀ i j, i < nrows grid → j < ncols grid → 0 ≤ cell grid i j ∧ cell grid i j ≤ 100000)

def LimitsOk (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) : Prop :=
  limits.val.length = nrows grid ∧
    (∀ i, i < nrows grid → 0 ≤ limitAt limits i ∧ limitAt limits i ≤ (ncols grid : Int))

def KOk (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64) : Prop :=
  0 ≤ k.val ∧ k.val ≤ ((nrows grid) * (ncols grid) : Int) ∧
    k.val ≤ ((List.range (nrows grid)).map (fun i => limitAt limits i)).sum

def Precondition (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64)
    (k : Std.I64) : Prop :=
  GridOk grid ∧ LimitsOk grid limits ∧ KOk grid limits k

/-- Whenever the function returns a result r, the integer represented by r equals the maximum of sum_{(i,j) in S} grid[i][j] over all finite sets S of pairs (i,j) with 0 <= i < n and 0 <= j < m such that, for every i, the number of j with (i,j) in S is at most limits[i], and the total number of pairs in S is at most k. The empty set S is allowed; the maximum is over a nonempty finite set of valid S.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). All numbers are mathematical integers represented by the I64 parameters. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    IsMaxTotal grid limits k.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), IsMaxTotal grid limits k.val r.val) := by
  sorry

/-- The function returns a result r (it does not fail by overflow, panic, or out-of-bounds) for every input satisfying the preconditions.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) :
    ∃ r : Std.I64, max_sum grid limits k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k), ∃ r : Std.I64, max_sum grid limits k = ok r) := by
  sorry

/-- Whenever the function returns a result r, let T be 0 if k = 0 and otherwise the sum of the k largest entries in the multiset { grid[i][j] : 0 <= i < n and 0 <= j < m } (ties among equal entries do not affect T). Then the integer represented by r is at most T.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    r.val ≤ topSumI (allCells grid) k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), r.val ≤ topSumI (allCells grid) k.val) := by
  sorry

/-- Whenever the function returns a result r, the integer represented by r is at least M, where M is the maximum of grid[i][j] over all pairs (i,j) with 0 <= i < n, 0 <= j < m and limits[i] >= 1.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]), and k > 0. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hk : 0 < k.val) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    maxEligible grid limits ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hk : 0 < k.val) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), maxEligible grid limits ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, the integer represented by r is 0.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]), and k = 0. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hk : k.val = 0) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hk : k.val = 0) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, the integer represented by r equals sum_{i=0}^{n-1} top_i, where top_i is the sum of the limits[i] largest entries of row i; top_i = 0 when limits[i] = 0, and top_i is the sum of the whole row when limits[i] = m.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]), and k = sum_{i=0}^{n-1} limits[i]. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k)
    (hk : k.val = ((List.range (nrows grid)).map (fun i => limitAt limits i)).sum)
    (r : Std.I64) (hr : max_sum grid limits k = ok r) :
    r.val = perRowTopSum grid limits := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k)
    (hk : k.val = ((List.range (nrows grid)).map (fun i => limitAt limits i)).sum)
    (r : Std.I64) (hr : max_sum grid limits k = ok r), r.val = perRowTopSum grid limits) := by
  sorry

/-- Whenever the function returns a result r, the integer represented by r equals M, where M is the maximum of grid[i][j] over all pairs (i,j) with 0 <= i < n, 0 <= j < m and limits[i] >= 1.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]), and k = 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hk : k.val = 1) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    r.val = maxEligible grid limits := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hk : k.val = 1) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), r.val = maxEligible grid limits) := by
  sorry

/-- Whenever the function returns a result r, the integer represented by r equals the sum of the k largest entries of the single row grid[0]; when k = 0 this sum is 0.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]), and n = 1. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hn : nrows grid = 1) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    r.val = topSumI (row grid 0) k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (hn : nrows grid = 1) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), r.val = topSumI (row grid 0) k.val) := by
  sorry

/-- Let pi be any permutation of {0,...,n-1}. Define grid' by grid'[t] = grid[pi(t)] and limits' by limits'[t] = limits[pi(t)] for 0 <= t < n. If r = max_sum(grid, limits, k) and r' = max_sum(grid', limits', k) are both returned results, then the integer represented by r equals the integer represented by r'.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_9 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (limits limits' : Slice Std.I64)
    (k : Std.I64) (hpre : Precondition grid limits k) (hpre' : Precondition grid' limits' k)
    (σ : Equiv.Perm (Fin (nrows grid))) (hn : nrows grid' = nrows grid)
    (hrow : ∀ t : Fin (nrows grid), row grid' t.val = row grid (σ t).val)
    (hlim : ∀ t : Fin (nrows grid), limitAt limits' t.val = limitAt limits (σ t).val)
    (r r' : Std.I64) (hr : max_sum grid limits k = ok r)
    (hr' : max_sum grid' limits' k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (limits limits' : Slice Std.I64)
    (k : Std.I64) (hpre : Precondition grid limits k) (hpre' : Precondition grid' limits' k)
    (σ : Equiv.Perm (Fin (nrows grid))) (hn : nrows grid' = nrows grid)
    (hrow : ∀ t : Fin (nrows grid), row grid' t.val = row grid (σ t).val)
    (hlim : ∀ t : Fin (nrows grid), limitAt limits' t.val = limitAt limits (σ t).val)
    (r r' : Std.I64) (hr : max_sum grid limits k = ok r)
    (hr' : max_sum grid' limits' k = ok r'), r.val = r'.val) := by
  sorry

/-- For each i with 0 <= i < n, let sigma_i be a permutation of {0,...,m-1}. Define grid' by grid'[i][j] = grid[i][sigma_i(j)] for all 0 <= i < n and 0 <= j < m, and keep limits' = limits. If r = max_sum(grid, limits, k) and r' = max_sum(grid', limits, k) are both returned results, then the integer represented by r equals the integer represented by r'.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_10 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64)
    (k : Std.I64) (hpre : Precondition grid limits k) (hpre' : Precondition grid' limits k)
    (hn : nrows grid' = nrows grid)
    (σ : (t : Fin (nrows grid)) → Equiv.Perm (Fin (rowLen grid t.val)))
    (hcell : ∀ (t : Fin (nrows grid)) (j : Fin (rowLen grid t.val)),
      cell grid' t.val j.val = cell grid t.val (σ t j).val)
    (r r' : Std.I64) (hr : max_sum grid limits k = ok r)
    (hr' : max_sum grid' limits k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64)
    (k : Std.I64) (hpre : Precondition grid limits k) (hpre' : Precondition grid' limits k)
    (hn : nrows grid' = nrows grid)
    (σ : (t : Fin (nrows grid)) → Equiv.Perm (Fin (rowLen grid t.val)))
    (hcell : ∀ (t : Fin (nrows grid)) (j : Fin (rowLen grid t.val)),
      cell grid' t.val j.val = cell grid t.val (σ t j).val)
    (r r' : Std.I64) (hr : max_sum grid limits k = ok r)
    (hr' : max_sum grid' limits k = ok r'), r.val = r'.val) := by
  sorry

/-- If r1 = max_sum(grid, limits, k1) and r2 = max_sum(grid, limits, k2) are both returned results, then the integer represented by r2 is at least the integer represented by r1.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k1 <= k2 <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64)
    (k1 k2 : Std.I64) (hpre1 : Precondition grid limits k1)
    (hpre2 : Precondition grid limits k2) (hk : k1.val ≤ k2.val) (r1 r2 : Std.I64)
    (hr1 : max_sum grid limits k1 = ok r1) (hr2 : max_sum grid limits k2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64)
    (k1 k2 : Std.I64) (hpre1 : Precondition grid limits k1)
    (hpre2 : Precondition grid limits k2) (hk : k1.val ≤ k2.val) (r1 r2 : Std.I64)
    (hr1 : max_sum grid limits k1 = ok r1) (hr2 : max_sum grid limits k2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If r1 = max_sum(grid, limits1, k) and r2 = max_sum(grid, limits2, k) are both returned results, then the integer represented by r2 is at least the integer represented by r1.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Let limits1 and limits2 be two arrays of length n. Preconditions: 1 <= n <= 500, 1 <= m <= 500, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, 0 <= limits1[i] <= limits2[i] <= m for every 0 <= i < n, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits1[i]). -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (limits1 limits2 : Slice Std.I64)
    (k : Std.I64) (hgrid : GridOk grid) (hlim1 : LimitsOk grid limits1)
    (hlim2 : LimitsOk grid limits2)
    (hmono : ∀ i, i < nrows grid → limitAt limits1 i ≤ limitAt limits2 i)
    (hk : KOk grid limits1 k) (r1 r2 : Std.I64)
    (hr1 : max_sum grid limits1 k = ok r1) (hr2 : max_sum grid limits2 k = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits1 limits2 : Slice Std.I64)
    (k : Std.I64) (hgrid : GridOk grid) (hlim1 : LimitsOk grid limits1)
    (hlim2 : LimitsOk grid limits2)
    (hmono : ∀ i, i < nrows grid → limitAt limits1 i ≤ limitAt limits2 i)
    (hk : KOk grid limits1 k) (r1 r2 : Std.I64)
    (hr1 : max_sum grid limits1 k = ok r1) (hr2 : max_sum grid limits2 k = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If rA = max_sum(gridA, limits, k) and rB = max_sum(gridB, limits, k) are both returned results, then the integer represented by rA is at most the integer represented by rB.
  Preconditions: Let gridA and gridB have the same dimensions n x m with 1 <= n <= 500 and 1 <= m <= 500. Let limits have length n. Preconditions: 0 <= gridA[i][j] <= gridB[i][j] <= 100000 for all 0 <= i < n and 0 <= j < m, 0 <= limits[i] <= m for all 0 <= i < n, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_13 (gridA gridB : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64)
    (k : Std.I64) (hA : GridOk gridA) (hB : GridOk gridB)
    (hn : nrows gridB = nrows gridA)
    (hm : ∀ i, i < nrows gridA → rowLen gridB i = rowLen gridA i)
    (hle : ∀ i j, i < nrows gridA → j < rowLen gridA i → cell gridA i j ≤ cell gridB i j)
    (hlim : LimitsOk gridA limits) (hk : KOk gridA limits k) (rA rB : Std.I64)
    (hrA : max_sum gridA limits k = ok rA) (hrB : max_sum gridB limits k = ok rB) :
    rA.val ≤ rB.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (gridA gridB : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64)
    (k : Std.I64) (hA : GridOk gridA) (hB : GridOk gridB)
    (hn : nrows gridB = nrows gridA)
    (hm : ∀ i, i < nrows gridA → rowLen gridB i = rowLen gridA i)
    (hle : ∀ i j, i < nrows gridA → j < rowLen gridA i → cell gridA i j ≤ cell gridB i j)
    (hlim : LimitsOk gridA limits) (hk : KOk gridA limits k) (rA rB : Std.I64)
    (hrA : max_sum gridA limits k = ok rA) (hrB : max_sum gridB limits k = ok rB), rA.val ≤ rB.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite set S of pairs (i,j) with 0 <= i < n and 0 <= j < m such that, for every i, the number of j with (i,j) in S is at most limits[i], the total number of pairs in S is at most k, and sum_{(i,j) in S} grid[i][j] equals the integer represented by r.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    ∃ S : Finset (Nat × Nat), Feasible grid limits k.val S ∧ weight grid S = r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), ∃ S : Finset (Nat × Nat), Feasible grid limits k.val S ∧ weight grid S = r.val) := by
  sorry

/-- Whenever the function returns a result r, for each i let T_i be the multiset of the limits[i] largest entries of row i (with multiplicity; empty if limits[i]=0). Let U be the multiset union of T_0,...,T_{n-1}. Then the integer represented by r equals the sum of the k largest entries of U (with multiplicity; 0 if k=0).
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_15 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    r.val = topSumI (perRowTopList grid limits) k.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), r.val = topSumI (perRowTopList grid limits) k.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite set S of pairs (i,j) with 0 <= i < n and 0 <= j < m such that, for every i, the number of j with (i,j) in S is at most limits[i], the total number of pairs in S is exactly k, and sum_{(i,j) in S} grid[i][j] equals the integer represented by r.
  Preconditions: Let n = len(grid). Let m be the common length of every grid[i]. Preconditions: 1 <= n <= 500, 1 <= m <= 500, len(limits) = n, 0 <= limits[i] <= m for every 0 <= i < n, 0 <= grid[i][j] <= 100000 for every 0 <= i < n and 0 <= j < m, and 0 <= k <= min(n*m, sum_{i=0}^{n-1} limits[i]). -/
theorem spec_16 (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r) :
    ∃ S : Finset (Nat × Nat), Feasible grid limits k.val S ∧ (S.card : Int) = k.val ∧
      weight grid S = r.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (limits : Slice Std.I64) (k : Std.I64)
    (hpre : Precondition grid limits k) (r : Std.I64)
    (hr : max_sum grid limits k = ok r), ∃ S : Finset (Nat × Nat), Feasible grid limits k.val S ∧ (S.card : Int) = k.val ∧
      weight grid S = r.val) := by
  sorry

end AegisSpec.MaxSum
