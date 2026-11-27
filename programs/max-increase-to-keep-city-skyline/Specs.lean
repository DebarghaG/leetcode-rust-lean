import Aegis.MaxIncreaseKeepingSkyline.Code.Funs

/-!
# Specifications of `Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline`

LeetCode problem `max-increase-to-keep-city-skyline`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxIncreaseKeepingSkyline

def mat (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def dim (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := grid.val.length

def entry (M : List (List Int)) (i j : Nat) : Int := (M.getD i []).getD j 0

def rowMax (M : List (List Int)) (i : Nat) : Int := (M.getD i []).foldr max 0

def colMax (M : List (List Int)) (j : Nat) : Int :=
  M.foldr (fun row acc => max (row.getD j 0) acc) 0

def Hmat (M : List (List Int)) (n : Nat) : List (List Int) :=
  (List.range n).map (fun i => (List.range n).map (fun j => min (rowMax M i) (colMax M j)))

def sqSum (n : Nat) (f : Nat → Nat → Int) : Int :=
  (List.range n).foldl
    (fun acc i => acc + (List.range n).foldl (fun acc j => acc + f i j) 0) 0

def transpose (M : List (List Int)) (n : Nat) : List (List Int) :=
  (List.range n).map (fun i => (List.range n).map (fun j => entry M j i))

/-- The function returns a result r. Define R_i = max_{0 <= j < n} grid[i][j] for 0 <= i < n and C_j = max_{0 <= i < n} grid[i][j] for 0 <= j < n. Then r = sum_{i=0}^{n-1} sum_{j=0}^{n-1} (min(R_i, C_j) - grid[i][j]).
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∃ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r ∧
      r.val = sqSum (dim grid)
        (fun i j => min (rowMax (mat grid) i) (colMax (mat grid) j) - entry (mat grid) i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∃ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r ∧
      r.val = sqSum (dim grid)
        (fun i j => min (rowMax (mat grid) i) (colMax (mat grid) j) - entry (mat grid) i j)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail (no overflow, out-of-bounds access, or panic) on any input satisfying the preconditions.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∃ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∃ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 100 * n * n.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      r.val ≤ 100 * (dim grid : Int) * (dim grid : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      r.val ≤ 100 * (dim grid : Int) * (dim grid : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] = min(R_i, C_j), where R_i = max_{0 <= k < n} grid[i][k] and C_j = max_{0 <= k < n} grid[k][j].
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      (r.val = 0 ↔ ∀ i j, i < dim grid → j < dim grid →
        entry (mat grid) i j = min (rowMax (mat grid) i) (colMax (mat grid) j)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      (r.val = 0 ↔ ∀ i j, i < dim grid → j < dim grid →
        entry (mat grid) i j = min (rowMax (mat grid) i) (colMax (mat grid) j))) := by
  sorry

/-- Whenever the function returns a result r, define R_i = max_{0 <= j < n} grid[i][j] and C_j = max_{0 <= i < n} grid[i][j]. For every n x n integer matrix h satisfying (1) h[i][j] >= grid[i][j] for all 0 <= i,j < n, (2) max_{0 <= j < n} h[i][j] = R_i for every row i, and (3) max_{0 <= i < n} h[i][j] = C_j for every column j, one has sum_{i=0}^{n-1} sum_{j=0}^{n-1} (h[i][j] - grid[i][j]) <= r.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      ∀ h : List (List Int), h.length = dim grid →
      (∀ i, i < dim grid → (h.getD i []).length = dim grid) →
      (∀ i j, i < dim grid → j < dim grid → entry (mat grid) i j ≤ entry h i j) →
      (∀ i, i < dim grid → rowMax h i = rowMax (mat grid) i) →
      (∀ j, j < dim grid → colMax h j = colMax (mat grid) j) →
      sqSum (dim grid) (fun i j => entry h i j - entry (mat grid) i j) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      ∀ h : List (List Int), h.length = dim grid →
      (∀ i, i < dim grid → (h.getD i []).length = dim grid) →
      (∀ i j, i < dim grid → j < dim grid → entry (mat grid) i j ≤ entry h i j) →
      (∀ i, i < dim grid → rowMax h i = rowMax (mat grid) i) →
      (∀ j, j < dim grid → colMax h j = colMax (mat grid) j) →
      sqSum (dim grid) (fun i j => entry h i j - entry (mat grid) i j) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, define R_i = max_{0 <= j < n} grid[i][j], C_j = max_{0 <= i < n} grid[i][j], and H[i][j] = min(R_i, C_j) for all 0 <= i,j < n. Then H satisfies: (a) H[i][j] >= grid[i][j] for all i,j; (b) max_{0 <= j < n} H[i][j] = R_i for every row i; (c) max_{0 <= i < n} H[i][j] = C_j for every column j; and (d) sum_{i=0}^{n-1} sum_{j=0}^{n-1} (H[i][j] - grid[i][j]) = r.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      (∀ i j, i < dim grid → j < dim grid →
        entry (mat grid) i j ≤ entry (Hmat (mat grid) (dim grid)) i j) ∧
      (∀ i, i < dim grid →
        rowMax (Hmat (mat grid) (dim grid)) i = rowMax (mat grid) i) ∧
      (∀ j, j < dim grid →
        colMax (Hmat (mat grid) (dim grid)) j = colMax (mat grid) j) ∧
      sqSum (dim grid)
        (fun i j => entry (Hmat (mat grid) (dim grid)) i j - entry (mat grid) i j) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      (∀ i j, i < dim grid → j < dim grid →
        entry (mat grid) i j ≤ entry (Hmat (mat grid) (dim grid)) i j) ∧
      (∀ i, i < dim grid →
        rowMax (Hmat (mat grid) (dim grid)) i = rowMax (mat grid) i) ∧
      (∀ j, j < dim grid →
        colMax (Hmat (mat grid) (dim grid)) j = colMax (mat grid) j) ∧
      sqSum (dim grid)
        (fun i j => entry (Hmat (mat grid) (dim grid)) i j - entry (mat grid) i j) = r.val) := by
  sorry

/-- Whenever the function returns a result r, define R_i = max_{0 <= j < n} grid[i][j], C_j = max_{0 <= i < n} grid[i][j], and H[i][j] = min(R_i, C_j). For every n x n integer matrix h satisfying h[i][j] >= grid[i][j] for all i,j, max_{0 <= j < n} h[i][j] = R_i for every row i, max_{0 <= i < n} h[i][j] = C_j for every column j, and sum_{i=0}^{n-1} sum_{j=0}^{n-1} (h[i][j] - grid[i][j]) = r, one has h[i][j] = H[i][j] for every i,j.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100) :
    ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      ∀ h : List (List Int), h.length = dim grid →
      (∀ i, i < dim grid → (h.getD i []).length = dim grid) →
      (∀ i j, i < dim grid → j < dim grid → entry (mat grid) i j ≤ entry h i j) →
      (∀ i, i < dim grid → rowMax h i = rowMax (mat grid) i) →
      (∀ j, j < dim grid → colMax h j = colMax (mat grid) j) →
      sqSum (dim grid) (fun i j => entry h i j - entry (mat grid) i j) = r.val →
      ∀ i j, i < dim grid → j < dim grid →
        entry h i j = entry (Hmat (mat grid) (dim grid)) i j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100), ∀ r : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      ∀ h : List (List Int), h.length = dim grid →
      (∀ i, i < dim grid → (h.getD i []).length = dim grid) →
      (∀ i j, i < dim grid → j < dim grid → entry (mat grid) i j ≤ entry h i j) →
      (∀ i, i < dim grid → rowMax h i = rowMax (mat grid) i) →
      (∀ j, j < dim grid → colMax h j = colMax (mat grid) j) →
      sqSum (dim grid) (fun i j => entry h i j - entry (mat grid) i j) = r.val →
      ∀ i j, i < dim grid → j < dim grid →
        entry h i j = entry (Hmat (mat grid) (dim grid)) i j) := by
  sorry

/-- Define the transposed matrix T by T[i][j] = grid[j][i] for all 0 <= i,j < n. If the function returns r on grid and returns r_T on T, then r = r_T.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_9 (grid T : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hTlen : (mat T).length = dim grid)
    (hTrows : ∀ i, i < dim grid → ((mat T).getD i []).length = dim grid)
    (hT : ∀ i j, i < dim grid → j < dim grid →
      entry (mat T) i j = entry (mat grid) j i) :
    ∀ r rT : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline T = ok rT →
      r.val = rT.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid T : Slice (alloc.vec.Vec Std.I64))
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hTlen : (mat T).length = dim grid)
    (hTrows : ∀ i, i < dim grid → ((mat T).getD i []).length = dim grid)
    (hT : ∀ i j, i < dim grid → j < dim grid →
      entry (mat T) i j = entry (mat grid) j i), ∀ r rT : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline T = ok rT →
      r.val = rT.val) := by
  sorry

/-- Let pi be any permutation of {0,1,...,n-1}. Define G[i][j] = grid[pi(i)][j] for all 0 <= i,j < n. If the function returns r on grid and returns r_G on G, then r = r_G.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_10 (grid G : Slice (alloc.vec.Vec Std.I64)) (π : Nat → Nat)
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hGlen : (mat G).length = dim grid)
    (hGrows : ∀ i, i < dim grid → ((mat G).getD i []).length = dim grid)
    (hπmem : ∀ i, i < dim grid → π i < dim grid)
    (hπinj : ∀ i j, i < dim grid → j < dim grid → π i = π j → i = j)
    (hG : ∀ i j, i < dim grid → j < dim grid →
      entry (mat G) i j = entry (mat grid) (π i) j) :
    ∀ r rG : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline G = ok rG →
      r.val = rG.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid G : Slice (alloc.vec.Vec Std.I64)) (π : Nat → Nat)
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hGlen : (mat G).length = dim grid)
    (hGrows : ∀ i, i < dim grid → ((mat G).getD i []).length = dim grid)
    (hπmem : ∀ i, i < dim grid → π i < dim grid)
    (hπinj : ∀ i j, i < dim grid → j < dim grid → π i = π j → i = j)
    (hG : ∀ i j, i < dim grid → j < dim grid →
      entry (mat G) i j = entry (mat grid) (π i) j), ∀ r rG : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline G = ok rG →
      r.val = rG.val) := by
  sorry

/-- Let pi be any permutation of {0,1,...,n-1}. Define G[i][j] = grid[i][pi(j)] for all 0 <= i,j < n. If the function returns r on grid and returns r_G on G, then r = r_G.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. -/
theorem spec_11 (grid G : Slice (alloc.vec.Vec Std.I64)) (π : Nat → Nat)
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hGlen : (mat G).length = dim grid)
    (hGrows : ∀ i, i < dim grid → ((mat G).getD i []).length = dim grid)
    (hπmem : ∀ j, j < dim grid → π j < dim grid)
    (hπinj : ∀ i j, i < dim grid → j < dim grid → π i = π j → i = j)
    (hG : ∀ i j, i < dim grid → j < dim grid →
      entry (mat G) i j = entry (mat grid) i (π j)) :
    ∀ r rG : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline G = ok rG →
      r.val = rG.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid G : Slice (alloc.vec.Vec Std.I64)) (π : Nat → Nat)
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hGlen : (mat G).length = dim grid)
    (hGrows : ∀ i, i < dim grid → ((mat G).getD i []).length = dim grid)
    (hπmem : ∀ j, j < dim grid → π j < dim grid)
    (hπinj : ∀ i j, i < dim grid → j < dim grid → π i = π j → i = j)
    (hG : ∀ i j, i < dim grid → j < dim grid →
      entry (mat G) i j = entry (mat grid) i (π j)), ∀ r rG : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline G = ok rG →
      r.val = rG.val) := by
  sorry

/-- Define G[i][j] = grid[i][j] + c for all 0 <= i,j < n. If the function returns r on grid and returns r_G on G, then r = r_G.
  Preconditions: Let n = len(grid). The preconditions are: 2 <= n <= 50; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100. Let c be an integer with c >= 0 and grid[i][j] + c <= 100 for all i,j. -/
theorem spec_12 (grid G : Slice (alloc.vec.Vec Std.I64)) (c : Int)
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hc : 0 ≤ c)
    (hshift : ∀ i j, i < dim grid → j < dim grid → entry (mat grid) i j + c ≤ 100)
    (hGlen : (mat G).length = dim grid)
    (hGrows : ∀ i, i < dim grid → ((mat G).getD i []).length = dim grid)
    (hG : ∀ i j, i < dim grid → j < dim grid →
      entry (mat G) i j = entry (mat grid) i j + c) :
    ∀ r rG : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline G = ok rG →
      r.val = rG.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid G : Slice (alloc.vec.Vec Std.I64)) (c : Int)
    (hn2 : 2 ≤ dim grid) (hn50 : dim grid ≤ 50)
    (hrows : ∀ i, i < dim grid → ((mat grid).getD i []).length = dim grid)
    (hentries : ∀ i j, i < dim grid → j < dim grid →
      0 ≤ entry (mat grid) i j ∧ entry (mat grid) i j ≤ 100)
    (hc : 0 ≤ c)
    (hshift : ∀ i j, i < dim grid → j < dim grid → entry (mat grid) i j + c ≤ 100)
    (hGlen : (mat G).length = dim grid)
    (hGrows : ∀ i, i < dim grid → ((mat G).getD i []).length = dim grid)
    (hG : ∀ i j, i < dim grid → j < dim grid →
      entry (mat G) i j = entry (mat grid) i j + c), ∀ r rG : Std.I64,
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline grid = ok r →
      Aegis.MaxIncreaseKeepingSkyline.max_increase_keeping_skyline G = ok rG →
      r.val = rG.val) := by
  sorry

end AegisSpec.MaxIncreaseKeepingSkyline
