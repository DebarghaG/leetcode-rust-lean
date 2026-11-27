import Aegis.GridGame.Code.Funs

/-!
# Specifications of `Aegis.GridGame.grid_game`

LeetCode problem `grid-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GridGame

def row (grid : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
  (grid.val.drop i).head?.elim [] (fun v => v.val.map (fun x => x.val))

def entry (l : List ℤ) (c : ℕ) : ℤ := l.getD c 0

def segSum (l : List ℤ) (a b : ℕ) : ℤ := ((l.drop a).take (b - a)).sum

def L (grid : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : ℤ := segSum (row grid 1) 0 k

def R (grid : Slice (alloc.vec.Vec Std.I64)) (n k : ℕ) : ℤ := segSum (row grid 0) (k + 1) n

def listMin (l : List ℤ) : ℤ :=
  match l with
  | [] => 0
  | x :: xs => xs.foldr min x

def candidates (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : List ℤ :=
  (List.range n).map (fun k => max (L grid k) (R grid n k))

def gameValue (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : ℤ :=
  listMin (candidates grid n)

def score (grid : Slice (alloc.vec.Vec Std.I64)) (k j : ℕ) : ℤ :=
  segSum (row grid 0) (k + 1) (j + 1) + segSum (row grid 1) j k

/-- The function returns a result r, and r = min_{0 <= k < n} max( L(k), R(k) ), where L(k) = sum_{c=0}^{k-1} grid[1][c] and R(k) = sum_{c=k+1}^{n-1} grid[0][c]. Equivalently, this is the game value: the first robot chooses the column k where it moves from row 0 to row 1, then the second robot's maximum possible collection is max(L(k), R(k)), and the first robot minimizes this maximum over all k.
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. All indices are 0-based; a sum over an empty index range is 0. -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res ∧ res.val = gameValue grid n := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res ∧ res.val = gameValue grid n) := by
  sorry

/-- The function returns a result r and does not fail: there is no panic, no out-of-bounds access, and no i64 overflow.
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res ∧ 0 ≤ res.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res ∧ 0 ≤ res.val) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{1} sum_{c=0}^{n-1} grid[i][c].
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. -/
theorem spec_4
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64,
      Aegis.GridGame.grid_game grid = ok res ∧
        res.val ≤ segSum (row grid 0) 0 n + segSum (row grid 1) 0 n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64,
      Aegis.GridGame.grid_game grid = ok res ∧
        res.val ≤ segSum (row grid 0) 0 n + segSum (row grid 1) 0 n) := by
  sorry

/-- The function returns a result r and r <= min( sum_{c=1}^{n-1} grid[0][c], sum_{c=0}^{n-2} grid[1][c] ).
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. Empty sums are 0. -/
theorem spec_5
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64,
      Aegis.GridGame.grid_game grid = ok res ∧
        res.val ≤ min (segSum (row grid 0) 1 n) (segSum (row grid 1) 0 (n - 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64,
      Aegis.GridGame.grid_game grid = ok res ∧
        res.val ≤ min (segSum (row grid 0) 1 n) (segSum (row grid 1) 0 (n - 1))) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000; and n >= 2. -/
theorem spec_6
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000) (hn_two : 2 ≤ n)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res ∧ 1 ≤ res.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000) (hn_two : 2 ≤ n)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64, Aegis.GridGame.grid_game grid = ok res ∧ 1 ≤ res.val) := by
  sorry

/-- The function returns a result r and there exists an integer k with 0 <= k < n such that r = max(L(k), R(k)), where L(k) = sum_{c=0}^{k-1} grid[1][c] and R(k) = sum_{c=k+1}^{n-1} grid[0][c].
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. Empty sums are 0. -/
theorem spec_7
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64, ∃ k : ℕ,
      Aegis.GridGame.grid_game grid = ok res ∧ k < n ∧ res.val = max (L grid k) (R grid n k) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64, ∃ k : ℕ,
      Aegis.GridGame.grid_game grid = ok res ∧ k < n ∧ res.val = max (L grid k) (R grid n k)) := by
  sorry

/-- The function returns a result r and for every integer k with 0 <= k < n, max(L(k), R(k)) >= r, where L(k) = sum_{c=0}^{k-1} grid[1][c] and R(k) = sum_{c=k+1}^{n-1} grid[0][c].
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. Empty sums are 0. -/
theorem spec_8
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64,
      Aegis.GridGame.grid_game grid = ok res ∧
        ∀ k : ℕ, k < n → res.val ≤ max (L grid k) (R grid n k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64,
      Aegis.GridGame.grid_game grid = ok res ∧
        ∀ k : ℕ, k < n → res.val ≤ max (L grid k) (R grid n k)) := by
  sorry

/-- The function returns a result r and there exist integers k and j with 0 <= k < n and 0 <= j < n such that r = score(k,j) and, for every integer j' with 0 <= j' < n, score(k,j') <= r, where score(k,j) = (sum_{c=k+1}^{j} grid[0][c] if j > k, and 0 otherwise) + (sum_{c=j}^{k-1} grid[1][c] if j < k, and 0 otherwise).
  Preconditions: len(grid)=2; there is an integer n with 1 <= n <= 50000 such that len(grid[0])=len(grid[1])=n; for every r in {0,1} and every c with 0 <= c < n, 1 <= grid[r][c] <= 100000. Empty sums are 0. -/
theorem spec_9
    (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000) :
    ∃ res : Std.I64, ∃ k j : ℕ,
      Aegis.GridGame.grid_game grid = ok res ∧ k < n ∧ j < n ∧
        res.val = score grid k j ∧
        (∀ j' : ℕ, j' < n → score grid k j' ≤ res.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000), ∃ res : Std.I64, ∃ k j : ℕ,
      Aegis.GridGame.grid_game grid = ok res ∧ k < n ∧ j < n ∧
        res.val = score grid k j ∧
        (∀ j' : ℕ, j' < n → score grid k j' ≤ res.val)) := by
  sorry

/-- If the function returns r on grid and r2 on grid2, then r = r2.
  Preconditions: Let grid satisfy len(grid)=2; there is n with 1 <= n <= 50000 and len(grid[0])=len(grid[1])=n; all entries are in [1,100000]. Define grid2 by len(grid2)=2, len(grid2[0])=len(grid2[1])=n, grid2[0][c] = grid[1][n-1-c] and grid2[1][c] = grid[0][n-1-c] for 0 <= c < n. Then grid2 also satisfies the same constraints. -/
theorem spec_10
    (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000)
    (hlen2 : grid2.val.length = 2)
    (hrow2_0 : (row grid2 0).length = n) (hrow2_1 : (row grid2 1).length = n)
    (hgrid2_0 : ∀ c : ℕ, c < n → entry (row grid2 0) c = entry (row grid 1) (n - 1 - c))
    (hgrid2_1 : ∀ c : ℕ, c < n → entry (row grid2 1) c = entry (row grid 0) (n - 1 - c))
    (res res2 : Std.I64)
    (hres : Aegis.GridGame.grid_game grid = ok res)
    (hres2 : Aegis.GridGame.grid_game grid2 = ok res2) :
    res.val = res2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000)
    (hlen2 : grid2.val.length = 2)
    (hrow2_0 : (row grid2 0).length = n) (hrow2_1 : (row grid2 1).length = n)
    (hgrid2_0 : ∀ c : ℕ, c < n → entry (row grid2 0) c = entry (row grid 1) (n - 1 - c))
    (hgrid2_1 : ∀ c : ℕ, c < n → entry (row grid2 1) c = entry (row grid 0) (n - 1 - c))
    (res res2 : Std.I64)
    (hres : Aegis.GridGame.grid_game grid = ok res)
    (hres2 : Aegis.GridGame.grid_game grid2 = ok res2), res.val = res2.val) := by
  sorry

/-- If the function returns r on grid and r2 on grid2, then r <= r2.
  Preconditions: Let grid and grid2 be two valid inputs satisfying len=2, with the same n where 1 <= n <= 50000, equal row lengths n, and all entries in [1,100000]. Suppose grid[i][c] <= grid2[i][c] for every i in {0,1} and every c with 0 <= c < n. -/
theorem spec_11
    (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000)
    (hlen2 : grid2.val.length = 2)
    (hrow2_0 : (row grid2 0).length = n) (hrow2_1 : (row grid2 1).length = n)
    (hentries2 : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid2 i) c ∧ entry (row grid2 i) c ≤ 100000)
    (hmono : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      entry (row grid i) c ≤ entry (row grid2 i) c)
    (res res2 : Std.I64)
    (hres : Aegis.GridGame.grid_game grid = ok res)
    (hres2 : Aegis.GridGame.grid_game grid2 = ok res2) :
    res.val ≤ res2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000)
    (hlen2 : grid2.val.length = 2)
    (hrow2_0 : (row grid2 0).length = n) (hrow2_1 : (row grid2 1).length = n)
    (hentries2 : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid2 i) c ∧ entry (row grid2 i) c ≤ 100000)
    (hmono : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      entry (row grid i) c ≤ entry (row grid2 i) c)
    (res res2 : Std.I64)
    (hres : Aegis.GridGame.grid_game grid = ok res)
    (hres2 : Aegis.GridGame.grid_game grid2 = ok res2), res.val ≤ res2.val) := by
  sorry

/-- If the function returns r on grid and r2 on grid2, then r2 = q*r.
  Preconditions: Let grid be valid with len=2, row lengths n, 1 <= n <= 50000, and entries in [1,100000]. Let q be an integer with q >= 1 such that q*grid[i][c] <= 100000 for every i in {0,1} and every c with 0 <= c < n. Define grid2 by grid2[i][c] = q*grid[i][c]; then grid2 is also a valid input. -/
theorem spec_12
    (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (q : ℤ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000)
    (hq : 1 ≤ q)
    (hqbound : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n → q * entry (row grid i) c ≤ 100000)
    (hlen2 : grid2.val.length = 2)
    (hrow2_0 : (row grid2 0).length = n) (hrow2_1 : (row grid2 1).length = n)
    (hgrid2 : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      entry (row grid2 i) c = q * entry (row grid i) c)
    (res res2 : Std.I64)
    (hres : Aegis.GridGame.grid_game grid = ok res)
    (hres2 : Aegis.GridGame.grid_game grid2 = ok res2) :
    res2.val = q * res.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (q : ℤ)
    (hlen : grid.val.length = 2)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hrow0 : (row grid 0).length = n) (hrow1 : (row grid 1).length = n)
    (hentries : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      1 ≤ entry (row grid i) c ∧ entry (row grid i) c ≤ 100000)
    (hq : 1 ≤ q)
    (hqbound : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n → q * entry (row grid i) c ≤ 100000)
    (hlen2 : grid2.val.length = 2)
    (hrow2_0 : (row grid2 0).length = n) (hrow2_1 : (row grid2 1).length = n)
    (hgrid2 : ∀ (i c : ℕ), (i = 0 ∨ i = 1) → c < n →
      entry (row grid2 i) c = q * entry (row grid i) c)
    (res res2 : Std.I64)
    (hres : Aegis.GridGame.grid_game grid = ok res)
    (hres2 : Aegis.GridGame.grid_game grid2 = ok res2), res2.val = q * res.val) := by
  sorry

end AegisSpec.GridGame
