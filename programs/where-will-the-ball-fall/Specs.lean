import Aegis.FindBall.Code.Funs

/-!
# Specifications of `Aegis.FindBall.find_ball`

LeetCode problem `where-will-the-ball-fall`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.FindBall

def entry (l : List Std.I64) (i : ℕ) : Option Int :=
  if h : i < l.length then some (l.get ⟨i, h⟩).val else none

def rowOf (grid : Slice (alloc.vec.Vec Std.I64)) (r : ℕ) : List Std.I64 :=
  if h : r < grid.val.length then (grid.val.get ⟨r, h⟩).val else []

def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (r : ℕ) : ℕ := (rowOf grid r).length

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (r c : ℕ) : Option Int :=
  entry (rowOf grid r) c

def vecEntry (v : alloc.vec.Vec Std.I64) (i : ℕ) : Option Int := entry v.val i

def ExitsAt (grid : Slice (alloc.vec.Vec Std.I64)) (m n i k : ℕ) : Prop :=
  ∃ c : ℕ → ℕ,
    c 0 = i ∧ c m = k ∧
      ∀ r, r < m →
        c r < n ∧
          (cell grid r (c r) = some 1 →
            c r + 1 < n ∧ cell grid r (c r + 1) = some 1 ∧ c (r + 1) = c r + 1) ∧
          (cell grid r (c r) = some (-1) →
            0 < c r ∧ cell grid r (c r - 1) = some (-1) ∧ c (r + 1) = c r - 1)

def StuckAt (grid : Slice (alloc.vec.Vec Std.I64)) (n r c : ℕ) : Prop :=
  (cell grid r c = some 1 ∧ (c + 1 = n ∨ (c + 1 < n ∧ cell grid r (c + 1) = some (-1)))) ∨
    (cell grid r c = some (-1) ∧ (c = 0 ∨ (0 < c ∧ cell grid r (c - 1) = some 1)))

/-- Let m = len(grid) and n = len(grid[0]). Say the ball starting at column i exits at column k if there exist columns c_0,...,c_m such that c_0 = i, c_m = k, and for every r with 0 <= r < m: 0 <= c_r < n; if grid[r][c_r] = 1 then c_r < n-1, grid[r][c_r+1] = 1, and c_{r+1} = c_r+1; if grid[r][c_r] = -1 then c_r > 0, grid[r][c_r-1] = -1, and c_{r+1} = c_r-1. Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n: ans[i] = -1 if and only if there is no k with 0 <= k < n such that the ball starting at column i exits at column k; and for every k with 0 <= k < n, if the ball starting at column i exits at column k then ans[i] = k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (vecEntry ans i = some (-1) ↔ ¬ ∃ k, k < n ∧ ExitsAt grid m n i k) ∧
            (∀ k, k < n → ExitsAt grid m n i k → vecEntry ans i = some (k : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (vecEntry ans i = some (-1) ↔ ¬ ∃ k, k < n ∧ ExitsAt grid m n i k) ∧
            (∀ k, k < n → ExitsAt grid m n i k → vecEntry ans i = some (k : Int))) := by
  sorry

/-- The function returns a result r (does not fail) for every grid satisfying the preconditions.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∃ ans : alloc.vec.Vec Std.I64, Aegis.FindBall.find_ball grid = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∃ ans : alloc.vec.Vec Std.I64, Aegis.FindBall.find_ball grid = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, for every i with 0 <= i < len(ans), ans[i] = -1 or (0 <= ans[i] < len(grid[0])).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ∀ i, i < ans.val.length →
        vecEntry ans i = some (-1) ∨
          ∃ k : Int, vecEntry ans i = some k ∧ 0 ≤ k ∧ k < (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ∀ i, i < ans.val.length →
        vecEntry ans i = some (-1) ∨
          ∃ k : Int, vecEntry ans i = some k ∧ 0 ≤ k ∧ k < (n : Int)) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n: if i > 0 and grid[0][i] = -1 and grid[0][i-1] = -1 then ans[i] = i-1; if i < n-1 and grid[0][i] = 1 and grid[0][i+1] = 1 then ans[i] = i+1; in every other case ans[i] = -1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. Additionally, m = 1. -/
theorem spec_4
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hm_one : m = 1) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (0 < i → cell grid 0 i = some (-1) → cell grid 0 (i - 1) = some (-1) →
            vecEntry ans i = some ((i : Int) - 1)) ∧
          (i + 1 < n → cell grid 0 i = some 1 → cell grid 0 (i + 1) = some 1 →
            vecEntry ans i = some ((i : Int) + 1)) ∧
          (¬ ((0 < i ∧ cell grid 0 i = some (-1) ∧ cell grid 0 (i - 1) = some (-1)) ∨
                (i + 1 < n ∧ cell grid 0 i = some 1 ∧ cell grid 0 (i + 1) = some 1)) →
            vecEntry ans i = some (-1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hm_one : m = 1), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (0 < i → cell grid 0 i = some (-1) → cell grid 0 (i - 1) = some (-1) →
            vecEntry ans i = some ((i : Int) - 1)) ∧
          (i + 1 < n → cell grid 0 i = some 1 → cell grid 0 (i + 1) = some 1 →
            vecEntry ans i = some ((i : Int) + 1)) ∧
          (¬ ((0 < i ∧ cell grid 0 i = some (-1) ∧ cell grid 0 (i - 1) = some (-1)) ∨
                (i + 1 < n ∧ cell grid 0 i = some 1 ∧ cell grid 0 (i + 1) = some 1)) →
            vecEntry ans i = some (-1))) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n, if either (grid[0][i] = 1 and (i = n-1 or (i < n-1 and grid[0][i+1] = -1))) or (grid[0][i] = -1 and (i = 0 or (i > 0 and grid[0][i-1] = 1))), then ans[i] = -1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_5
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → StuckAt grid n 0 i → vecEntry ans i = some (-1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → StuckAt grid n 0 i → vecEntry ans i = some (-1)) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n: if i + m <= n-1 then ans[i] = i + m, otherwise ans[i] = -1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. Additionally, for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1. -/
theorem spec_6
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hall_one : ∀ r c, r < m → c < n → cell grid r c = some 1) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (i + m < n → vecEntry ans i = some ((i : Int) + (m : Int))) ∧
            (n ≤ i + m → vecEntry ans i = some (-1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hall_one : ∀ r c, r < m → c < n → cell grid r c = some 1), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (i + m < n → vecEntry ans i = some ((i : Int) + (m : Int))) ∧
            (n ≤ i + m → vecEntry ans i = some (-1))) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n: if i >= m then ans[i] = i - m, otherwise ans[i] = -1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. Additionally, for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = -1. -/
theorem spec_7
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hall_neg : ∀ r c, r < m → c < n → cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (m ≤ i → vecEntry ans i = some ((i : Int) - (m : Int))) ∧
            (i < m → vecEntry ans i = some (-1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hall_neg : ∀ r c, r < m → c < n → cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n →
          (m ≤ i → vecEntry ans i = some ((i : Int) - (m : Int))) ∧
            (i < m → vecEntry ans i = some (-1))) := by
  sorry

/-- Define H by H[r][c] = -grid[r][n-1-c] for 0 <= r < m and 0 <= c < n. Whenever the function returns ans on grid and ansH on H, len(ans) = n, len(ansH) = n, and for every i with 0 <= i < n: if ans[i] = -1 then ansH[n-1-i] = -1; and if ans[i] = k with 0 <= k < n then ansH[n-1-i] = n-1-k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_8
    (grid H : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hmH : m = H.val.length) (hnH : n = rowLen H 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hHrows : ∀ r, r < m → rowLen H r = n)
    (hHvals : ∀ r c, r < m → c < n → cell H r c = some 1 ∨ cell H r c = some (-1))
    (hH : ∀ r c, r < m → c < n → cell H r c = (cell grid r (n - 1 - c)).map (fun x => -x)) :
    ∀ ans ansH, Aegis.FindBall.find_ball grid = ok ans →
      Aegis.FindBall.find_ball H = ok ansH →
        ans.val.length = n ∧ ansH.val.length = n ∧
          ∀ i, i < n →
            (vecEntry ans i = some (-1) → vecEntry ansH (n - 1 - i) = some (-1)) ∧
              (∀ k : Int, vecEntry ans i = some k → 0 ≤ k → k < (n : Int) →
                vecEntry ansH (n - 1 - i) = some ((n : Int) - 1 - k)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid H : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hmH : m = H.val.length) (hnH : n = rowLen H 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1))
    (hHrows : ∀ r, r < m → rowLen H r = n)
    (hHvals : ∀ r c, r < m → c < n → cell H r c = some 1 ∨ cell H r c = some (-1))
    (hH : ∀ r c, r < m → c < n → cell H r c = (cell grid r (n - 1 - c)).map (fun x => -x)), ∀ ans ansH, Aegis.FindBall.find_ball grid = ok ans →
      Aegis.FindBall.find_ball H = ok ansH →
        ans.val.length = n ∧ ansH.val.length = n ∧
          ∀ i, i < n →
            (vecEntry ans i = some (-1) → vecEntry ansH (n - 1 - i) = some (-1)) ∧
              (∀ k : Int, vecEntry ans i = some k → 0 ≤ k → k < (n : Int) →
                vecEntry ansH (n - 1 - i) = some ((n : Int) - 1 - k))) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n, if ans[i] = k and k >= 0 then |k - i| <= m.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_9
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → ∀ k : Int, vecEntry ans i = some k → 0 ≤ k →
          |k - (i : Int)| ≤ (m : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → ∀ k : Int, vecEntry ans i = some k → 0 ≤ k →
          |k - (i : Int)| ≤ (m : Int)) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n, if ans[i] = k and k >= 0 then (k - i - m) is even.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_10
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → ∀ k : Int, vecEntry ans i = some k → 0 ≤ k →
          Even (k - (i : Int) - (m : Int)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → ∀ k : Int, vecEntry ans i = some k → 0 ≤ k →
          Even (k - (i : Int) - (m : Int))) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i, j with 0 <= i < j < n, if ans[i] >= 0 and ans[j] >= 0 then ans[i] < ans[j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_11
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i j, i < j → j < n → ∀ a b : Int,
          vecEntry ans i = some a → vecEntry ans j = some b → 0 ≤ a → 0 ≤ b → a < b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i j, i < j → j < n → ∀ a b : Int,
          vecEntry ans i = some a → vecEntry ans j = some b → 0 ≤ a → 0 ≤ b → a < b) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n, if ans[i] = k and k >= 0, then there exist columns c_0,...,c_m such that c_0 = i, c_m = k, and for every r with 0 <= r < m: 0 <= c_r < n; if grid[r][c_r] = 1 then c_r < n-1, grid[r][c_r+1] = 1, and c_{r+1} = c_r+1; if grid[r][c_r] = -1 then c_r > 0, grid[r][c_r-1] = -1, and c_{r+1} = c_r-1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_12
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → ∀ k : ℕ, vecEntry ans i = some (k : Int) → ExitsAt grid m n i k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → ∀ k : ℕ, vecEntry ans i = some (k : Int) → ExitsAt grid m n i k) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) = n and for every i with 0 <= i < n, if ans[i] = -1, then there exist r with 0 <= r < m and columns c_0,...,c_r such that c_0 = i, for every q with 0 <= q < r: 0 <= c_q < n and either (grid[q][c_q] = 1 and c_q < n-1 and grid[q][c_q+1] = 1 and c_{q+1} = c_q+1) or (grid[q][c_q] = -1 and c_q > 0 and grid[q][c_q-1] = -1 and c_{q+1} = c_q-1), and at row r the ball is stuck: 0 <= c_r < n and either (grid[r][c_r] = 1 and (c_r = n-1 or (c_r < n-1 and grid[r][c_r+1] = -1))) or (grid[r][c_r] = -1 and (c_r = 0 or (c_r > 0 and grid[r][c_r-1] = 1))).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The parameters satisfy m >= 1, n >= 1, m <= 100, n <= 100, every row of grid has length n, and for every r, c with 0 <= r < m and 0 <= c < n, grid[r][c] = 1 or grid[r][c] = -1. -/
theorem spec_13
    (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)) :
    ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → vecEntry ans i = some (-1) →
          ∃ (r : ℕ) (c : ℕ → ℕ),
            r < m ∧ c 0 = i ∧ c r < n ∧
              (∀ q, q < r →
                c q < n ∧
                  ((cell grid q (c q) = some 1 ∧ c q + 1 < n ∧
                      cell grid q (c q + 1) = some 1 ∧ c (q + 1) = c q + 1) ∨
                    (cell grid q (c q) = some (-1) ∧ 0 < c q ∧
                      cell grid q (c q - 1) = some (-1) ∧ c (q + 1) = c q - 1))) ∧
              StuckAt grid n r (c r) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : m = grid.val.length) (hn : n = rowLen grid 0)
    (hm_ge : 1 ≤ m) (hn_ge : 1 ≤ n) (hm_le : m ≤ 100) (hn_le : n ≤ 100)
    (hrows : ∀ r, r < m → rowLen grid r = n)
    (hvals : ∀ r c, r < m → c < n → cell grid r c = some 1 ∨ cell grid r c = some (-1)), ∀ ans, Aegis.FindBall.find_ball grid = ok ans →
      ans.val.length = n ∧
        ∀ i, i < n → vecEntry ans i = some (-1) →
          ∃ (r : ℕ) (c : ℕ → ℕ),
            r < m ∧ c 0 = i ∧ c r < n ∧
              (∀ q, q < r →
                c q < n ∧
                  ((cell grid q (c q) = some 1 ∧ c q + 1 < n ∧
                      cell grid q (c q + 1) = some 1 ∧ c (q + 1) = c q + 1) ∨
                    (cell grid q (c q) = some (-1) ∧ 0 < c q ∧
                      cell grid q (c q - 1) = some (-1) ∧ c (q + 1) = c q - 1))) ∧
              StuckAt grid n r (c r)) := by
  sorry

end AegisSpec.FindBall
