import Aegis.SortMatrix.Code.Funs

/-!
# Specifications of `Aegis.SortMatrix.sort_matrix`

LeetCode problem `sort-matrix-by-diagonals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SortMatrix (sort_matrix)

namespace AegisSpec.SortMatrix

def rowOf (m : List (alloc.vec.Vec I64)) (i : ℕ) : List I64 := (m[i]?).elim [] (fun r => r.val)

def ent (m : List (alloc.vec.Vec I64)) (i j : ℕ) : ℤ := ((rowOf m i)[j]?).elim 0 (fun v => v.val)

def firstRow (d : ℤ) : ℕ := (-d).toNat

def lastRow (n : ℕ) (d : ℤ) : ℕ := min (n - 1) ((n : ℤ) - 1 - d).toNat

def OnDiag (n : ℕ) (d : ℤ) (k : ℕ) : Prop := firstRow d ≤ k ∧ k ≤ lastRow n d

def diagIdx (n : ℕ) (d : ℤ) : List ℕ :=
  (List.range n).filter (fun k => decide (firstRow d ≤ k ∧ k ≤ lastRow n d))

def diagEnt (m : List (alloc.vec.Vec I64)) (k : ℕ) (d : ℤ) : ℤ := ent m k ((k : ℤ) + d).toNat

def diagVals (m : List (alloc.vec.Vec I64)) (d : ℤ) : List ℤ :=
  (diagIdx m.length d).map (fun k => diagEnt m k d)

def SortedDesc (l : List ℤ) : Prop := l.Pairwise (fun a b => b ≤ a)

def SortedAsc (l : List ℤ) : Prop := l.Pairwise (fun a b => a ≤ b)

def listMin (l : List ℤ) : ℤ := match l with | [] => 0 | x :: xs => xs.foldr min x

def listMax (l : List ℤ) : ℤ := match l with | [] => 0 | x :: xs => xs.foldr max x

def IsMaxOf (x : ℤ) (l : List ℤ) : Prop := x ∈ l ∧ ∀ a ∈ l, a ≤ x

def IsMinOf (x : ℤ) (l : List ℤ) : Prop := x ∈ l ∧ ∀ a ∈ l, x ≤ a

/-- The function returns a result `out` such that len(out) = n, len(out[i]) = n for every 0 <= i < n, and for every integer d with -(n-1) <= d <= n-1 the following holds. Let A_d = [grid[k][k+d] for k = max(0,-d), max(0,-d)+1, ..., min(n-1,n-1-d)] and B_d = [out[k][k+d] for the same k values], both listed in increasing k. If d <= 0, then B_d is exactly the sequence obtained by arranging all entries of A_d in non-increasing order. If d > 0, then B_d is exactly the sequence obtained by arranging all entries of A_d in non-decreasing order.
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, so grid is an n by n square matrix, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000) :
    ∃ out : alloc.vec.Vec (alloc.vec.Vec I64),
      sort_matrix grid = ok out ∧ out.val.length = n ∧
        (∀ i, i < n → (rowOf out.val i).length = n) ∧
        (∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
          (d ≤ 0 → SortedDesc (diagVals out.val d) ∧
            (diagVals out.val d).Perm (diagVals grid.val d)) ∧
          (0 < d → SortedAsc (diagVals out.val d) ∧
            (diagVals out.val d).Perm (diagVals grid.val d))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000), ∃ out : alloc.vec.Vec (alloc.vec.Vec I64),
      sort_matrix grid = ok out ∧ out.val.length = n ∧
        (∀ i, i < n → (rowOf out.val i).length = n) ∧
        (∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
          (d ≤ 0 → SortedDesc (diagVals out.val d) ∧
            (diagVals out.val d).Perm (diagVals grid.val d)) ∧
          (0 < d → SortedAsc (diagVals out.val d) ∧
            (diagVals out.val d).Perm (diagVals grid.val d)))) := by
  sorry

/-- The function returns a result `out` for every input satisfying the preconditions; in particular, it does not fail, panic, or overflow.
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000) :
    ∃ out : alloc.vec.Vec (alloc.vec.Vec I64), sort_matrix grid = ok out := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000), ∃ out : alloc.vec.Vec (alloc.vec.Vec I64), sort_matrix grid = ok out) := by
  sorry

/-- Whenever the function returns a result `out`, len(out) = n and for every i with 0 <= i < n, len(out[i]) = n.
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    out.val.length = n ∧ ∀ i, i < n → (rowOf out.val i).length = n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), out.val.length = n ∧ ∀ i, i < n → (rowOf out.val i).length = n) := by
  sorry

/-- Whenever the function returns a result `out`, for every i,j with 0 <= i < n and 0 <= j < n, let d = j - i. Then the minimum and maximum below are taken over all k with max(0,-d) <= k <= min(n-1,n-1-d), and they satisfy min_k grid[k][k+d] <= out[i][j] <= max_k grid[k][k+d].
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    ∀ i j, i < n → j < n →
      listMin (diagVals grid.val ((j : ℤ) - (i : ℤ))) ≤ ent out.val i j ∧
        ent out.val i j ≤ listMax (diagVals grid.val ((j : ℤ) - (i : ℤ))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), ∀ i j, i < n → j < n →
      listMin (diagVals grid.val ((j : ℤ) - (i : ℤ))) ≤ ent out.val i j ∧
        ent out.val i j ≤ listMax (diagVals grid.val ((j : ℤ) - (i : ℤ)))) := by
  sorry

/-- Whenever the function returns a result `out`, for every integer d with -(n-1) <= d <= n-1, let A_d and B_d be the input and output values on diagonal d, namely A_d = [grid[k][k+d]] and B_d = [out[k][k+d]] for k from max(0,-d) to min(n-1,n-1-d). The multiset of entries of B_d is equal to the multiset of entries of A_d.
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
      (diagVals out.val d).Perm (diagVals grid.val d) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
      (diagVals out.val d).Perm (diagVals grid.val d)) := by
  sorry

/-- Whenever the function returns a result `out`, for every integer d with -(n-1) <= d <= 0 and for every k with max(0,-d) <= k < min(n-1,n-1-d), we have out[k][k+d] >= out[k+1][k+1+d].
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ 0 → ∀ k : ℕ,
      firstRow d ≤ k → k < lastRow n d →
        diagEnt out.val (k + 1) d ≤ diagEnt out.val k d := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ 0 → ∀ k : ℕ,
      firstRow d ≤ k → k < lastRow n d →
        diagEnt out.val (k + 1) d ≤ diagEnt out.val k d) := by
  sorry

/-- Whenever the function returns a result `out`, for every integer d with 1 <= d <= n-1 and for every k with max(0,-d) <= k < min(n-1,n-1-d), we have out[k][k+d] <= out[k+1][k+1+d].
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    ∀ d : ℤ, 1 ≤ d → d ≤ (n : ℤ) - 1 → ∀ k : ℕ,
      firstRow d ≤ k → k < lastRow n d →
        diagEnt out.val k d ≤ diagEnt out.val (k + 1) d := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), ∀ d : ℤ, 1 ≤ d → d ≤ (n : ℤ) - 1 → ∀ k : ℕ,
      firstRow d ≤ k → k < lastRow n d →
        diagEnt out.val k d ≤ diagEnt out.val (k + 1) d) := by
  sorry

/-- Whenever the function returns a result `out`, for every integer d with -(n-1) <= d <= n-1, let s = max(0,-d) be the first row index on diagonal d and let A_d = [grid[k][k+d] for k = max(0,-d), ..., min(n-1,n-1-d)]. If d <= 0, then out[s][s+d] = max(A_d). If d > 0, then out[s][s+d] = min(A_d).
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
      (d ≤ 0 → IsMaxOf (diagEnt out.val (firstRow d) d) (diagVals grid.val d)) ∧
      (0 < d → IsMinOf (diagEnt out.val (firstRow d) d) (diagVals grid.val d)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
      (d ≤ 0 → IsMaxOf (diagEnt out.val (firstRow d) d) (diagVals grid.val d)) ∧
      (0 < d → IsMinOf (diagEnt out.val (firstRow d) d) (diagVals grid.val d))) := by
  sorry

/-- Whenever the function returns a result `out`, for every integer d with -(n-1) <= d <= n-1, let e = min(n-1,n-1-d) be the last row index on diagonal d and let A_d = [grid[k][k+d] for k = max(0,-d), ..., min(n-1,n-1-d)]. If d <= 0, then out[e][e+d] = min(A_d). If d > 0, then out[e][e+d] = max(A_d).
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
      (d ≤ 0 → IsMinOf (diagEnt out.val (lastRow n d) d) (diagVals grid.val d)) ∧
      (0 < d → IsMaxOf (diagEnt out.val (lastRow n d) d) (diagVals grid.val d)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), ∀ d : ℤ, -((n : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
      (d ≤ 0 → IsMinOf (diagEnt out.val (lastRow n d) d) (diagVals grid.val d)) ∧
      (0 < d → IsMaxOf (diagEnt out.val (lastRow n d) d) (diagVals grid.val d))) := by
  sorry

/-- Whenever the function returns a result `out`, for every i,j with 0 <= i < n and 0 <= j < n, let d = j - i. There exists k with max(0,-d) <= k <= min(n-1,n-1-d) such that out[i][j] = grid[k][k+d].
  Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 10, for every i with 0 <= i < n, len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n, -100000 <= grid[i][j] <= 100000. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out) :
    ∀ i j, i < n → j < n → ∃ k : ℕ,
      OnDiag n ((j : ℤ) - (i : ℤ)) k ∧
        ent out.val i j = diagEnt grid.val k ((j : ℤ) - (i : ℤ)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : ℕ) (hn : n = grid.val.length)
    (hn1 : 1 ≤ n) (hn10 : n ≤ 10)
    (hlens : ∀ i, i < n → (rowOf grid.val i).length = n)
    (hrange : ∀ i j, i < n → j < n → -100000 ≤ ent grid.val i j ∧ ent grid.val i j ≤ 100000)
    (out : alloc.vec.Vec (alloc.vec.Vec I64)) (hres : sort_matrix grid = ok out), ∀ i j, i < n → j < n → ∃ k : ℕ,
      OnDiag n ((j : ℤ) - (i : ℤ)) k ∧
        ent out.val i j = diagEnt grid.val k ((j : ℤ) - (i : ℤ))) := by
  sorry

end AegisSpec.SortMatrix
