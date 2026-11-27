import Aegis.NumEnclaves.Code.Funs

/-!
# Specifications of `Aegis.NumEnclaves.num_enclaves`

LeetCode problem `number-of-enclaves`. Each `spec_<n>` theorem states one property of the function.
-/

open Aegis.NumEnclaves
  open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumEnclaves

  def rows (grid : Slice (alloc.vec.Vec I64)) : List (List Int) :=
    grid.val.map (fun row => row.val.map (fun x => x.val))

  def numRows (grid : Slice (alloc.vec.Vec I64)) : Nat := (Slice.len grid).val

  def numCols (grid : Slice (alloc.vec.Vec I64)) : Nat := ((rows grid).headD []).length

  def rowAt (grid : Slice (alloc.vec.Vec I64)) (i : Nat) : List Int := (rows grid).getD i []

  def rowLen (grid : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat := (rowAt grid i).length

  def cellAt (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int := (rowAt grid i).getD j 0

  theorem numRows_eq_length (grid : Slice (alloc.vec.Vec I64)) :
      numRows grid = grid.val.length := by
    simp [numRows]

  def IsLand (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (i j : Nat) : Prop :=
    i < m ∧ j < n ∧ cellAt grid i j = 1

  def IsBoundary (m n : Nat) (i j : Nat) : Prop :=
    i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1

  def IsBoundaryLand (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (i j : Nat) : Prop :=
    IsBoundary m n i j ∧ IsLand grid m n i j

  def manhattan (c d : Nat × Nat) : Nat :=
    (c.1 - d.1) + (d.1 - c.1) + (c.2 - d.2) + (d.2 - c.2)

  def LandStep (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (c d : Nat × Nat) : Prop :=
    IsLand grid m n c.1 c.2 ∧ IsLand grid m n d.1 d.2 ∧ manhattan c d = 1

  def LandPath (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (c d : Nat × Nat) : Prop :=
    IsLand grid m n c.1 c.2 ∧ Relation.ReflTransGen (LandStep grid m n) c d

  def ReachesBoundary (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (c : Nat × Nat) : Prop :=
    ∃ d : Nat × Nat, IsBoundaryLand grid m n d.1 d.2 ∧ LandPath grid m n c d

  def IsEnclosed (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (c : Nat × Nat) : Prop :=
    IsLand grid m n c.1 c.2 ∧ ¬ ReachesBoundary grid m n c

  noncomputable def countCells (m n : Nat) (p : Nat × Nat → Prop) : Nat := by
    classical
    exact (((Finset.range m).product (Finset.range n)).filter p).card

  noncomputable def landCount (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) : Nat :=
    countCells m n (fun c => IsLand grid m n c.1 c.2)

  noncomputable def enclaveCount (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) : Nat :=
    countCells m n (IsEnclosed grid m n)

  def totalCells (m n : Nat) : Nat := m * n

  def interiorCells (m n : Nat) : Nat := (m - 2) * (n - 2)

  noncomputable def componentOf (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (c : Nat × Nat) : Finset (Nat × Nat) := by
    classical
    exact ((Finset.range m).product (Finset.range n)).filter (fun d => LandPath grid m n c d)

  noncomputable def interiorComponents (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) :
      Finset (Finset (Nat × Nat)) := by
    classical
    exact ((((Finset.range m).product (Finset.range n)).filter
        (fun c => IsLand grid m n c.1 c.2)).image (fun c => componentOf grid m n c)).filter
      (fun C => ∀ d ∈ C, ¬ IsBoundary m n d.1 d.2)

  noncomputable def interiorComponentSum (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) : Nat :=
    (interiorComponents grid m n).sum (fun C => C.card)

  def IsTranspose (grid gridT : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    numRows gridT = n ∧ numCols gridT = m ∧
      (∀ a, a < n → rowLen gridT a = m) ∧
      (∀ a b, a < n → b < m → cellAt gridT a b = cellAt grid b a)

  def IsRowReversal (grid gridR : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    numRows gridR = m ∧ numCols gridR = n ∧
      (∀ i, i < m → rowLen gridR i = n) ∧
      (∀ i j, i < m → j < n → cellAt gridR i j = cellAt grid (m - 1 - i) j)

  /-- The function returns a result r, and r equals the number of cells (i,j) with 0 <= i < m, 0 <= j < n such that grid[i][j] = 1 and no land path leads from (i,j) to a boundary land cell. Formally: a land path is a finite sequence of cells c_0,...,c_k (k >= 0) with c_t = (a_t,b_t) satisfying 0 <= a_t < m, 0 <= b_t < n and grid[a_t][b_t] = 1 for all t, and |a_{t+1}-a_t| + |b_{t+1}-b_t| = 1 for all 0 <= t < k. A cell (i',j') is a boundary cell if i' = 0 or i' = m-1 or j' = 0 or j' = n-1. Then r = |{(i,j) : 0 <= i < m, 0 <= j < n, grid[i][j] = 1, and there is no boundary cell (i',j') with grid[i'][j'] = 1 reachable from (i,j) by a land path}|.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧ r.val = (enclaveCount grid m n : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧ r.val = (enclaveCount grid m n : Int)) := by
    sorry

  /-- The function returns a result r and 0 <= r <= L, where L = |{(i,j) : 0 <= i < m, 0 <= j < n, grid[i][j] = 1}| is the number of land cells; in particular 0 <= r <= m*n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧ 0 ≤ r.val ∧
        r.val ≤ (landCount grid m n : Int) ∧ r.val ≤ (totalCells m n : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧ 0 ≤ r.val ∧
          r.val ≤ (landCount grid m n : Int) ∧ r.val ≤ (totalCells m n : Int)) := by
    sorry

  /-- The function returns a result r for every grid satisfying the preconditions; it never fails (no overflow and no out-of-bounds access).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r) := by
    sorry

  /-- The function returns a result r, and if grid[i][j] = 0 for every boundary cell (i.e., for every 0 <= i < m, 0 <= j < n with i = 0 or i = m-1 or j = 0 or j = n-1), then r = L, the number of land cells.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (hboundary : ∀ i j, i < m → j < n → IsBoundary m n i j → cellAt grid i j = 0) :
      ∃ r : I64, num_enclaves grid = ok r ∧ r.val = (landCount grid m n : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (hboundary : ∀ i j, i < m → j < n → IsBoundary m n i j → cellAt grid i j = 0), ∃ r : I64, num_enclaves grid = ok r ∧ r.val = (landCount grid m n : Int)) := by
    sorry

  /-- The function returns a result r, and for every cell (i,j) that is counted (0 <= i < m, 0 <= j < n, grid[i][j] = 1, and no land path from (i,j) reaches any boundary land cell) it holds that 0 < i < m-1 and 0 < j < n-1; in particular no boundary cell is ever counted.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧
        (∀ i j, IsEnclosed grid m n (i, j) → 0 < i ∧ i < m - 1 ∧ 0 < j ∧ j < n - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧
          (∀ i j, IsEnclosed grid m n (i, j) → 0 < i ∧ i < m - 1 ∧ 0 < j ∧ j < n - 1)) := by
    sorry

  /-- The function returns a result r, and if m <= 2 or n <= 2 then r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧ (m ≤ 2 ∨ n ≤ 2 → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧ (m ≤ 2 ∨ n ≤ 2 → r.val = 0)) := by
    sorry

  /-- The function returns a result r, and if m >= 2 and n >= 2 then r <= (m-2)*(n-2), the number of strictly interior cells.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧
        (2 ≤ m → 2 ≤ n → r.val ≤ (interiorCells m n : Int)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧
          (2 ≤ m → 2 ≤ n → r.val ≤ (interiorCells m n : Int))) := by
    sorry

  /-- The function returns a result r, and if grid[i][j] = 1 for all 0 <= i < m and 0 <= j < n, then r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧
        ((∀ i j, i < m → j < n → cellAt grid i j = 1) → r.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧
          ((∀ i j, i < m → j < n → cellAt grid i j = 1) → r.val = 0)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if every land cell can reach the boundary, i.e., for every (i,j) with 0 <= i < m, 0 <= j < n and grid[i][j] = 1, there is a boundary land cell (i',j') and a land path from (i,j) to (i',j').
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧
        (r.val = 0 ↔ ∀ i j, i < m → j < n → cellAt grid i j = 1 →
          ReachesBoundary grid m n (i, j)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧
          (r.val = 0 ↔ ∀ i j, i < m → j < n → cellAt grid i j = 1 →
            ReachesBoundary grid m n (i, j))) := by
    sorry

  /-- The function returns a result r, and r equals the sum of the cardinalities of all 4-connected land components that contain no boundary cell, where a 4-connected land component is a maximal set C of cells such that every (a,b) ∈ C satisfies 0 <= a < m, 0 <= b < n and grid[a][b] = 1, and any two cells of C are joined by a land path (consecutive cells differing by exactly one step in one coordinate, all cells land).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r : I64, num_enclaves grid = ok r ∧
        r.val = (interiorComponentSum grid m n : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r : I64, num_enclaves grid = ok r ∧
          r.val = (interiorComponentSum grid m n : Int)) := by
    sorry

  /-- Let gridT be the n x m transpose defined by gridT[a][b] = grid[b][a] for 0 <= a < n, 0 <= b < m. Then num_enclaves(grid) returns r, num_enclaves(gridT) returns rT, and r = rT.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_11 (grid gridT : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hT : IsTranspose grid gridT m n)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r rT : I64, num_enclaves grid = ok r ∧ num_enclaves gridT = ok rT ∧ r.val = rT.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid gridT : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hT : IsTranspose grid gridT m n)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r rT : I64, num_enclaves grid = ok r ∧ num_enclaves gridT = ok rT ∧ r.val = rT.val) := by
    sorry

  /-- Let gridR be the m x n grid defined by gridR[i][j] = grid[m-1-i][j] for 0 <= i < m, 0 <= j < n. Then num_enclaves(grid) returns r, num_enclaves(gridR) returns rR, and r = rR.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m <= 500, 1 <= n <= 500, every row grid[i] (0 <= i < m) has length exactly n, and grid[i][j] ∈ {0,1} for all 0 <= i < m, 0 <= j < n. -/
  theorem spec_12 (grid gridR : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hR : IsRowReversal grid gridR m n)
      (hm : m = numRows grid) (hn : n = numCols grid)
      (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
      (hrow : ∀ i, i < m → rowLen grid i = n)
      (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r rR : I64, num_enclaves grid = ok r ∧ num_enclaves gridR = ok rR ∧ r.val = rR.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid gridR : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hR : IsRowReversal grid gridR m n)
        (hm : m = numRows grid) (hn : n = numCols grid)
        (hm1 : 1 ≤ m) (hm500 : m ≤ 500) (hn1 : 1 ≤ n) (hn500 : n ≤ 500)
        (hrow : ∀ i, i < m → rowLen grid i = n)
        (hbin : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r rR : I64, num_enclaves grid = ok r ∧ num_enclaves gridR = ok rR ∧ r.val = rR.val) := by
    sorry

  end AegisSpec.NumEnclaves
