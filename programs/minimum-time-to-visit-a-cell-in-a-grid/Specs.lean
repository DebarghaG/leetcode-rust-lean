import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `minimum-time-to-visit-a-cell-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumTime

open Aeneas Aeneas.Std Result
open Aegis.MinimumTime

def toMatrix (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def colCount (grid : Slice (alloc.vec.Vec Std.I64)) : Option Nat :=
  (grid.val[0]?).map (fun row => row.val.length)

def cell (g : List (List Int)) (i j : Nat) : Option Int :=
  (g[i]?).bind (fun row => row[j]?)

def Adj (p q : Nat × Nat) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
    (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

def WalkValid (g : List (List Int)) (m n L : Nat) (p : Nat → Nat × Nat) : Prop :=
  p 0 = (0, 0) ∧
    p L = (m - 1, n - 1) ∧
    (∀ t, t < L → Adj (p t) (p (t + 1))) ∧
    (∀ t, t ≤ L → ∀ v, cell g (p t).1 (p t).2 = some v → v ≤ (t : Int))

def Reachable (g : List (List Int)) (m n : Nat) : Prop :=
  ∃ (L : Nat) (p : Nat → Nat × Nat), WalkValid g m n L p

def IsMinWalkLen (g : List (List Int)) (m n : Nat) (r : Int) : Prop :=
  0 ≤ r ∧
    (∃ p : Nat → Nat × Nat, WalkValid g m n r.toNat p) ∧
    (∀ L : Nat, (L : Int) < r → ¬ ∃ p : Nat → Nat × Nat, WalkValid g m n L p)

def gridMax (g : List (List Int)) : Int :=
  g.foldl (fun acc row => row.foldl (fun acc x => max acc x) acc) 0

/-- Let D = m+n-2. A valid start-to-target walk of length L is a finite sequence of cells p_0,...,p_L with p_0=(0,0), p_L=(m-1,n-1), such that for every t with 0 <= t < L, p_t and p_{t+1} are adjacent in the four cardinal directions (they differ by 1 in exactly one coordinate and agree in the other), and for every t with 0 <= t <= L, grid[p_t.row][p_t.col] <= t. The function returns a result r (it does not fail) and: if at least one valid start-to-target walk exists, then r is the least L >= 0 for which a valid start-to-target walk of length L exists; equivalently, r >= 0, a valid start-to-target walk of length r exists, and no valid start-to-target walk of length less than r exists. If no valid start-to-target walk exists, then r = -1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∃ r : Std.I64,
      minimum_time grid = ok r ∧
        (Reachable (toMatrix grid) m n → IsMinWalkLen (toMatrix grid) m n r.val) ∧
        (¬ Reachable (toMatrix grid) m n → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∃ r : Std.I64,
      minimum_time grid = ok r ∧
        (Reachable (toMatrix grid) m n → IsMinWalkLen (toMatrix grid) m n r.val) ∧
        (¬ Reachable (toMatrix grid) m n → r.val = -1)) := by
  sorry

/-- The function returns a result r and does not fail (no overflow, out-of-bounds access, panic, or other Lean failure). The value r may be -1 or a nonnegative integer.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∃ r : Std.I64, minimum_time grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∃ r : Std.I64, minimum_time grid = ok r) := by
  sorry

/-- Let r be the result returned by the function. Then r = -1 if and only if grid[0][1] > 1 and grid[1][0] > 1. Equivalently, the bottom-right cell is unreachable exactly when neither of the two cells adjacent to the start can be entered at time 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∃ r : Std.I64,
      minimum_time grid = ok r ∧
        (r.val = -1 ↔
          (∀ a, cell (toMatrix grid) 0 1 = some a → 1 < a) ∧
            (∀ b, cell (toMatrix grid) 1 0 = some b → 1 < b)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∃ r : Std.I64,
      minimum_time grid = ok r ∧
        (r.val = -1 ↔
          (∀ a, cell (toMatrix grid) 0 1 = some a → 1 < a) ∧
            (∀ b, cell (toMatrix grid) 1 0 = some b → 1 < b))) := by
  sorry

/-- Whenever the function returns a result r, if r >= 0 then r >= (m-1)+(n-1) = m+n-2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r →
      0 ≤ r.val → (m : Int) + (n : Int) - 2 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r →
      0 ≤ r.val → (m : Int) + (n : Int) - 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if r >= 0 then r >= grid[m-1][n-1].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      ∀ v, cell (toMatrix grid) (m - 1) (n - 1) = some v → v ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      ∀ v, cell (toMatrix grid) (m - 1) (n - 1) = some v → v ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if r >= 0 then r mod 2 = (m+n-2) mod 2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r →
      0 ≤ r.val → r.val % 2 = ((m : Int) + (n : Int) - 2) % 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r →
      0 ≤ r.val → r.val % 2 = ((m : Int) + (n : Int) - 2) % 2) := by
  sorry

/-- Let M = max{ grid[i][j] : 0 <= i < m and 0 <= j < n }. Whenever the function returns a result r, if r >= 0 then r <= M + (m+n-2).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      r.val ≤ gridMax (toMatrix grid) + ((m : Int) + (n : Int) - 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      r.val ≤ gridMax (toMatrix grid) + ((m : Int) + (n : Int) - 2)) := by
  sorry

/-- Whenever the function returns a result r, if r >= 0 then there exists a valid start-to-target walk of length r, where a valid walk is as in spec_1: p_0=(0,0), p_r=(m-1,n-1), consecutive cells are adjacent in the four cardinal directions, and grid[p_t.row][p_t.col] <= t for every t with 0 <= t <= r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      ∃ p : Nat → Nat × Nat, WalkValid (toMatrix grid) m n r.val.toNat p := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      ∃ p : Nat → Nat × Nat, WalkValid (toMatrix grid) m n r.val.toNat p) := by
  sorry

/-- Whenever the function returns a result r, if r >= 0 then for every valid start-to-target walk of length L (defined as in spec_1), L >= r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      ∀ (L : Nat) (p : Nat → Nat × Nat), WalkValid (toMatrix grid) m n L p →
        r.val ≤ (L : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r → 0 ≤ r.val →
      ∀ (L : Nat) (p : Nat → Nat × Nat), WalkValid (toMatrix grid) m n L p →
        r.val ≤ (L : Int)) := by
  sorry

/-- Whenever the function returns a result r, if r = -1 then no valid start-to-target walk (defined as in spec_1) exists.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r → r.val = -1 →
      ¬ Reachable (toMatrix grid) m n := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r → r.val = -1 →
      ¬ Reachable (toMatrix grid) m n) := by
  sorry

/-- Let D = m+n-2. Whenever the function returns a result r, r = D if and only if there exists a valid start-to-target walk of length D (valid walk as defined in spec_1).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies: m >= 2, n >= 2, m*n <= 100000; every row of grid has length n; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 100000; and grid[0][0] = 0. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0) :
    ∀ r : Std.I64, minimum_time grid = ok r →
      (r.val = (m : Int) + (n : Int) - 2 ↔
        ∃ p : Nat → Nat × Nat, WalkValid (toMatrix grid) m n (m + n - 2) p) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm : m = grid.val.length) (hn : colCount grid = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrows : ∀ row ∈ toMatrix grid, row.length = n)
    (hbounds : ∀ row ∈ toMatrix grid, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstart : cell (toMatrix grid) 0 0 = some 0), ∀ r : Std.I64, minimum_time grid = ok r →
      (r.val = (m : Int) + (n : Int) - 2 ↔
        ∃ p : Nat → Nat × Nat, WalkValid (toMatrix grid) m n (m + n - 2) p)) := by
  sorry

/-- Let rA be the result of minimum_time(A) and rB be the result of minimum_time(B). If rB >= 0, then rA >= 0 and rA <= rB. Equivalently, lowering cell thresholds cannot increase the minimum arrival time, and if the higher-threshold grid is reachable then the lower-threshold grid is also reachable.
  Preconditions: Let A and B be two inputs each satisfying the preconditions of spec_1 with the same row count m and column count n: m >= 2, n >= 2, m*n <= 100000; all rows have length n; all entries are between 0 and 100000; A[0][0]=0 and B[0][0]=0; and A[i][j] <= B[i][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (A B : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmA : m = A.val.length) (hmB : m = B.val.length)
    (hnA : colCount A = some n) (hnB : colCount B = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrowsA : ∀ row ∈ toMatrix A, row.length = n)
    (hrowsB : ∀ row ∈ toMatrix B, row.length = n)
    (hboundsA : ∀ row ∈ toMatrix A, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hboundsB : ∀ row ∈ toMatrix B, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstartA : cell (toMatrix A) 0 0 = some 0)
    (hstartB : cell (toMatrix B) 0 0 = some 0)
    (hle : ∀ (i j : Nat) (a b : Int),
      cell (toMatrix A) i j = some a → cell (toMatrix B) i j = some b → a ≤ b)
    (rA rB : Std.I64) (hA : minimum_time A = ok rA) (hB : minimum_time B = ok rB) :
    0 ≤ rB.val → 0 ≤ rA.val ∧ rA.val ≤ rB.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmA : m = A.val.length) (hmB : m = B.val.length)
    (hnA : colCount A = some n) (hnB : colCount B = some n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hsize : m * n ≤ 100000)
    (hrowsA : ∀ row ∈ toMatrix A, row.length = n)
    (hrowsB : ∀ row ∈ toMatrix B, row.length = n)
    (hboundsA : ∀ row ∈ toMatrix A, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hboundsB : ∀ row ∈ toMatrix B, ∀ x ∈ row, 0 ≤ x ∧ x ≤ 100000)
    (hstartA : cell (toMatrix A) 0 0 = some 0)
    (hstartB : cell (toMatrix B) 0 0 = some 0)
    (hle : ∀ (i j : Nat) (a b : Int),
      cell (toMatrix A) i j = some a → cell (toMatrix B) i j = some b → a ≤ b)
    (rA rB : Std.I64) (hA : minimum_time A = ok rA) (hB : minimum_time B = ok rB), 0 ≤ rB.val → 0 ≤ rA.val ∧ rA.val ≤ rB.val) := by
  sorry

end AegisSpec.MinimumTime
