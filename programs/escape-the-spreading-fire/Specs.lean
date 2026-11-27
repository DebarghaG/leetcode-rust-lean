import Aegis.MaximumMinutes.Code.Funs

/-!
# Specifications of `Aegis.MaximumMinutes.maximum_minutes`

LeetCode problem `escape-the-spreading-fire`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumMinutes

  open Aegis.MaximumMinutes (maximum_minutes)

  def m (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := grid.val.length

  def n (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    match grid.val with
    | [] => 0
    | row :: _ => row.val.length

  def Rectangular (grid : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ row ∈ grid.val, row.val.length = n grid

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
    match grid.val[i]? with
    | none => none
    | some row => (row.val[j]?).map (fun v => v.val)

  def Adjacent (p q : Nat × Nat) : Prop :=
    (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
      (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

  inductive FireSpread (grid : Slice (alloc.vec.Vec Std.I64)) : Nat → Nat → Nat → Prop where
    | start {i j : Nat} (hi : i < m grid) (hj : j < n grid) (h1 : cell grid i j = some 1) :
        FireSpread grid 0 i j
    | step {t i j i' j' : Nat} (h : FireSpread grid t i j) (hi : i' < m grid)
        (hj : j' < n grid) (h2 : cell grid i' j' ≠ some 2) (hadj : Adjacent (i, j) (i', j')) :
        FireSpread grid (t + 1) i' j'

  noncomputable def F (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Nat := by
    classical
    exact if h : ∃ t, FireSpread grid t i j then some (Nat.find h) else none

  def ltF (w : Nat) : Option Nat → Prop
    | none => True
    | some t => w < t

  def leF (w : Nat) : Option Nat → Prop
    | none => True
    | some t => w ≤ t

  def ZeroPath (grid : Slice (alloc.vec.Vec Std.I64)) (L : Nat) (p : Nat → Nat × Nat) : Prop :=
    1 ≤ L ∧
      p 0 = (0, 0) ∧
        p L = (m grid - 1, n grid - 1) ∧
          (∀ k, k ≤ L → cell grid (p k).1 (p k).2 = some 0) ∧
            ∀ k, 1 ≤ k → k ≤ L → Adjacent (p (k - 1)) (p k)

  def Feasible (grid : Slice (alloc.vec.Vec Std.I64)) (w : Nat) : Prop :=
    ∃ (L : Nat) (p : Nat → Nat × Nat),
      ZeroPath grid L p ∧
        ltF w (F grid (p 0).1 (p 0).2) ∧
          (∀ k, 1 ≤ k → k < L → ltF (w + k) (F grid (p k).1 (p k).2)) ∧
            leF (w + L) (F grid (p L).1 (p L).2)

  def IsMinZeroPathLength (grid : Slice (alloc.vec.Vec Std.I64)) (d : Nat) : Prop :=
    (∃ (L : Nat) (p : Nat → Nat × Nat), ZeroPath grid L p ∧ L = d) ∧
      ∀ (L : Nat) (p : Nat → Nat × Nat), ZeroPath grid L p → d ≤ L

  theorem F_eq_zero_of_fire_at_cell (grid : Slice (alloc.vec.Vec Std.I64)) (hm : 0 < m grid)
      (hn : 0 < n grid) (h : cell grid 0 0 = some 1) : F grid 0 0 = some 0 := by
    classical
    have hsp : FireSpread grid 0 0 0 := FireSpread.start hm hn h
    have hex : ∃ t, FireSpread grid t 0 0 := ⟨0, hsp⟩
    unfold AegisSpec.MaximumMinutes.F
    rw [dite_eq_left hex]
    congr 1
    exact (Nat.find_eq_zero hex).mpr hsp

  theorem F_eq_none_of_wall (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat)
      (h : cell grid i j = some 2) : F grid i j = none := by
    classical
    have hne : ¬ ∃ t, FireSpread grid t i j := by
      rintro ⟨t, ht⟩
      induction ht with
      | start hi hj h1 => rw [h] at h1; exact absurd h1 (by decide)
      | step _ _ _ h2 _ => exact h2 h
    unfold AegisSpec.MaximumMinutes.F
    rw [dite_eq_right hne]

  theorem feasible_of_fire_never (grid : Slice (alloc.vec.Vec Std.I64)) (L : Nat)
      (p : Nat → Nat × Nat) (hz : ZeroPath grid L p) (hF : ∀ i j, F grid i j = none)
      (w : Nat) : Feasible grid w := by
    refine ⟨L, p, hz, ?_, ?_, ?_⟩
    · simp [ltF, hF]
    · intro k _ _
      simp [ltF, hF]
    · simp [leF, hF]

  /-- Define F(c), for a cell c with grid value not 2, as the least t >= 0 such that fire can reach c in t minutes from some cell of value 1, moving through adjacent cells of value not 2; if fire never reaches c, set F(c) = infinity. Call an integer w >= 0 feasible when there exist L >= 1 and cells p_0,...,p_L such that p_0=(0,0), p_L=(m-1,n-1), every p_k has grid value 0, p_k is adjacent (north, east, south, or west) to p_{k-1} for 1 <= k <= L, w < F(p_0), w+k < F(p_k) for every 1 <= k < L, and w+L <= F(p_L). Then maximum_minutes(grid) returns r such that: r = -1 if no w >= 0 is feasible; r = 1000000000 if every w >= 0 is feasible; otherwise r is the maximum feasible w, so r >= 0, r is feasible, and no w > r is feasible.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_1
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (r : Std.I64) (hr : maximum_minutes grid = ok r) :
      (r.val = -1 ∧ ∀ w : Nat, ¬ Feasible grid w) ∨
        (r.val = 1000000000 ∧ ∀ w : Nat, Feasible grid w) ∨
          (0 ≤ r.val ∧
            (∃ w : Nat, Feasible grid w ∧ (w : Int) = r.val) ∧
              ∀ w : Nat, Feasible grid w → (w : Int) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (r : Std.I64) (hr : maximum_minutes grid = ok r), (r.val = -1 ∧ ∀ w : Nat, ¬ Feasible grid w) ∨
          (r.val = 1000000000 ∧ ∀ w : Nat, Feasible grid w) ∨
            (0 ≤ r.val ∧
              (∃ w : Nat, Feasible grid w ∧ (w : Int) = r.val) ∧
                ∀ w : Nat, Feasible grid w → (w : Int) ≤ r.val)) := by
    sorry

  /-- The function maximum_minutes(grid) returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_2
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0) :
      ∃ r : Std.I64, maximum_minutes grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0), ∃ r : Std.I64, maximum_minutes grid = ok r) := by
    sorry

  /-- Whenever maximum_minutes(grid) returns r, either r = -1 or 0 <= r <= 1000000000.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_3
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (r : Std.I64) (hr : maximum_minutes grid = ok r) :
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 1000000000) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (r : Std.I64) (hr : maximum_minutes grid = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 1000000000)) := by
    sorry

  /-- Using the feasible-wait definition from spec_1, if r >= 0, then every integer w with 0 <= w <= r is feasible.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_4
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (r : Std.I64) (hr : maximum_minutes grid = ok r) (hr0 : 0 ≤ r.val) :
      ∀ w : Nat, (w : Int) ≤ r.val → Feasible grid w := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (r : Std.I64) (hr : maximum_minutes grid = ok r) (hr0 : 0 ≤ r.val), ∀ w : Nat, (w : Int) ≤ r.val → Feasible grid w) := by
    sorry

  /-- With F defined as in spec_1, if F(0,0) is finite and maximum_minutes(grid) returns r, then r <= F(0,0) - 1. In particular, r is not 1000000000 in this case.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_5
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (t : Nat) (hF : F grid 0 0 = some t)
      (r : Std.I64) (hr : maximum_minutes grid = ok r) :
      r.val ≤ (t : Int) - 1 ∧ r.val ≠ 1000000000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (t : Nat) (hF : F grid 0 0 = some t)
        (r : Std.I64) (hr : maximum_minutes grid = ok r), r.val ≤ (t : Int) - 1 ∧ r.val ≠ 1000000000) := by
    sorry

  /-- If there is no path from (0,0) to (m-1,n-1) whose cells all have grid value 0 and whose consecutive cells are adjacent, then maximum_minutes(grid) returns -1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_6
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (hno : ¬ ∃ (L : Nat) (p : Nat → Nat × Nat), ZeroPath grid L p) :
      maximum_minutes grid = ok (-1)#i64 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (hno : ¬ ∃ (L : Nat) (p : Nat → Nat × Nat), ZeroPath grid L p), maximum_minutes grid = ok (-1)#i64) := by
    sorry

  /-- With F defined as in spec_1, if there is a path from (0,0) to (m-1,n-1) whose cells all have grid value 0 and whose consecutive cells are adjacent, and if F(m-1,n-1) = infinity, then maximum_minutes(grid) returns 1000000000.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_7
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (hpath : ∃ (L : Nat) (p : Nat → Nat × Nat), ZeroPath grid L p)
      (hF : F grid (m grid - 1) (n grid - 1) = none) :
      maximum_minutes grid = ok (1000000000)#i64 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (hpath : ∃ (L : Nat) (p : Nat → Nat × Nat), ZeroPath grid L p)
        (hF : F grid (m grid - 1) (n grid - 1) = none), maximum_minutes grid = ok (1000000000)#i64) := by
    sorry

  /-- With F defined as in spec_1, if the returned r satisfies r >= 0, let d be the minimum number of moves in a path from (0,0) to (m-1,n-1) whose cells all have grid value 0 (such a d exists because r >= 0). If F(m-1,n-1) is finite, then r + d <= F(m-1,n-1).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_8
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (d : Nat) (hd : IsMinZeroPathLength grid d)
      (t : Nat) (hF : F grid (m grid - 1) (n grid - 1) = some t)
      (r : Std.I64) (hr : maximum_minutes grid = ok r) (hr0 : 0 ≤ r.val) :
      r.val + (d : Int) ≤ (t : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (d : Nat) (hd : IsMinZeroPathLength grid d)
        (t : Nat) (hF : F grid (m grid - 1) (n grid - 1) = some t)
        (r : Std.I64) (hr : maximum_minutes grid = ok r) (hr0 : 0 ≤ r.val), r.val + (d : Int) ≤ (t : Int)) := by
    sorry

  /-- With F defined as in spec_1, if F(0,0) = infinity, then maximum_minutes(grid) returns either -1 or 1000000000.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_9
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (hF : F grid 0 0 = none)
      (r : Std.I64) (hr : maximum_minutes grid = ok r) :
      r.val = -1 ∨ r.val = 1000000000 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (hF : F grid 0 0 = none)
        (r : Std.I64) (hr : maximum_minutes grid = ok r), r.val = -1 ∨ r.val = 1000000000) := by
    sorry

  /-- With F defined as in spec_1, if 0 <= r < 1000000000, then F(m-1,n-1) is finite.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_10
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (r : Std.I64) (hr : maximum_minutes grid = ok r)
      (hr0 : 0 ≤ r.val) (hr9 : r.val < 1000000000) :
      ∃ t : Nat, F grid (m grid - 1) (n grid - 1) = some t := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (r : Std.I64) (hr : maximum_minutes grid = ok r)
        (hr0 : 0 ≤ r.val) (hr9 : r.val < 1000000000), ∃ t : Nat, F grid (m grid - 1) (n grid - 1) = some t) := by
    sorry

  /-- With F defined as in spec_1, if maximum_minutes(grid) returns r = 1000000000, then F(0,0) = infinity and F(m-1,n-1) = infinity.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is rectangular: every row grid[i] has length n. 2 <= m,n <= 300, 4 <= m*n <= 20000. For every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2. grid[0][0] = 0 and grid[m-1][n-1] = 0. -/
  theorem spec_11
      (grid : Slice (alloc.vec.Vec Std.I64))
      (hrect : Rectangular grid)
      (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
      (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
      (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
      (hval : ∀ i j, i < m grid → j < n grid →
        cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
      (hstart : cell grid 0 0 = some 0)
      (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
      (r : Std.I64) (hr : maximum_minutes grid = ok r) (hr9 : r.val = 1000000000) :
      F grid 0 0 = none ∧ F grid (m grid - 1) (n grid - 1) = none := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrect : Rectangular grid)
        (hm : 2 ≤ m grid) (hm' : m grid ≤ 300)
        (hn : 2 ≤ n grid) (hn' : n grid ≤ 300)
        (hmn : 4 ≤ m grid * n grid) (hmn' : m grid * n grid ≤ 20000)
        (hval : ∀ i j, i < m grid → j < n grid →
          cell grid i j = some 0 ∨ cell grid i j = some 1 ∨ cell grid i j = some 2)
        (hstart : cell grid 0 0 = some 0)
        (hend : cell grid (m grid - 1) (n grid - 1) = some 0)
        (r : Std.I64) (hr : maximum_minutes grid = ok r) (hr9 : r.val = 1000000000), F grid 0 0 = none ∧ F grid (m grid - 1) (n grid - 1) = none) := by
    sorry

  end AegisSpec.MaximumMinutes
