import Aegis.NumMagicSquaresInside.Code.Funs

/-!
# Specifications of `Aegis.NumMagicSquaresInside.num_magic_squares_inside`

LeetCode problem `magic-squares-in-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumMagicSquaresInside

  def ncols (grid : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    match grid.val with
    | [] => 0
    | v :: _ => v.val.length

  def rowwidth (grid : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
    match grid.val[i]? with
    | none => 0
    | some v => v.val.length

  def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    match grid.val[i]? with
    | none => 0
    | some v => ((v.val[j]?).map (fun x => x.val)).getD 0

  def rowSum (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    entry grid i j + entry grid i (j + 1) + entry grid i (j + 2)

  def colSum (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    entry grid i j + entry grid (i + 1) j + entry grid (i + 2) j

  def diagSum (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    entry grid i j + entry grid (i + 1) (j + 1) + entry grid (i + 2) (j + 2)

  def antiDiagSum (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    entry grid i (j + 2) + entry grid (i + 1) (j + 1) + entry grid (i + 2) j

  def SumsEq (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) (S : ℤ) : Prop :=
    rowSum grid i j = S ∧ rowSum grid (i + 1) j = S ∧ rowSum grid (i + 2) j = S ∧
    colSum grid i j = S ∧ colSum grid i (j + 1) = S ∧ colSum grid i (j + 2) = S ∧
    diagSum grid i j = S ∧ antiDiagSum grid i j = S

  def IsMagic3 (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : Prop :=
    (∀ a b : ℕ, a < 3 → b < 3 → 1 ≤ entry grid (i + a) (j + b) ∧ entry grid (i + a) (j + b) ≤ 9) ∧
    (∀ a b a' b' : ℕ, a < 3 → b < 3 → a' < 3 → b' < 3 →
      entry grid (i + a) (j + b) = entry grid (i + a') (j + b') → a = a' ∧ b = b') ∧
    (∃ S : ℤ, SumsEq grid i j S)

  noncomputable def magicPairs (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ) :
      Finset (ℕ × ℕ) := by
    classical
    exact ((Finset.range row).product (Finset.range col)).filter
      (fun p => p.1 + 3 ≤ row ∧ p.2 + 3 ≤ col ∧ IsMagic3 grid p.1 p.2)

  noncomputable def numMagicPairs (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ) : ℕ :=
    (magicPairs grid row col).card

  /-- For 0 <= i <= row-3 and 0 <= j <= col-3, call the 3 x 3 subgrid with top-left (i,j) magic when: (1) each of its nine entries grid[i+a][j+b] (0 <= a < 3, 0 <= b < 3) lies in {1,2,...,9}; (2) these nine entries are pairwise distinct; and (3) there exists an integer S such that sum_{b=0}^{2} grid[i+a][j+b] = S for a=0,1,2, sum_{a=0}^{2} grid[i+a][j+b] = S for b=0,1,2, grid[i][j]+grid[i+1][j+1]+grid[i+2][j+2] = S, and grid[i][j+2]+grid[i+1][j+1]+grid[i+2][j] = S. The function returns a result r, and r is exactly the number of pairs (i,j) with 0 <= i <= row-3 and 0 <= j <= col-3 for which the subgrid with top-left (i,j) is magic.
    Preconditions: Let row = len(grid) and col = len(grid[0]). The preconditions are: row >= 1, col >= 1, row <= 10, col <= 10, len(grid[i]) = col for every i with 0 <= i < row, and 0 <= grid[i][j] <= 15 for every i,j with 0 <= i < row and 0 <= j < col. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
      (hrow : grid.val.length = row) (hcol : ncols grid = col)
      (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
      (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
      (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
      (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15) :
      ∃ r : Std.I64,
        Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
        r.val = (numMagicPairs grid row col : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
        (hrow : grid.val.length = row) (hcol : ncols grid = col)
        (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
        (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
        (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
        (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15), ∃ r : Std.I64,
          Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
          r.val = (numMagicPairs grid row col : ℤ)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail, panic, or go out of bounds for any grid satisfying the preconditions.
    Preconditions: Let row = len(grid) and col = len(grid[0]). The preconditions are: row >= 1, col >= 1, row <= 10, col <= 10, len(grid[i]) = col for every i with 0 <= i < row, and 0 <= grid[i][j] <= 15 for every i,j with 0 <= i < row and 0 <= j < col. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
      (hrow : grid.val.length = row) (hcol : ncols grid = col)
      (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
      (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
      (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
      (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15) :
      ∃ r : Std.I64, Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
        (hrow : grid.val.length = row) (hcol : ncols grid = col)
        (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
        (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
        (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
        (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15), ∃ r : Std.I64, Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= max(0, row-2) * max(0, col-2); in particular, since row <= 10 and col <= 10, r <= 64.
    Preconditions: Let row = len(grid) and col = len(grid[0]). The preconditions are: row >= 1, col >= 1, row <= 10, col <= 10, len(grid[i]) = col for every i with 0 <= i < row, and 0 <= grid[i][j] <= 15 for every i,j with 0 <= i < row and 0 <= j < col. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
      (hrow : grid.val.length = row) (hcol : ncols grid = col)
      (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
      (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
      (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
      (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15) :
      ∀ r : Std.I64, Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r →
        r.val ≤ ((row - 2 : ℕ) : ℤ) * ((col - 2 : ℕ) : ℤ) ∧ r.val ≤ 64 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
        (hrow : grid.val.length = row) (hcol : ncols grid = col)
        (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
        (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
        (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
        (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15), ∀ r : Std.I64, Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r →
          r.val ≤ ((row - 2 : ℕ) : ℤ) * ((col - 2 : ℕ) : ℤ) ∧ r.val ≤ 64) := by
    sorry

  /-- Let gt be the col x row grid defined by gt[j][i] = grid[i][j] for all 0 <= i < row and 0 <= j < col. The function returns result r on grid and result rt on gt, and r = rt.
    Preconditions: Let row = len(grid) and col = len(grid[0]). The preconditions are: row >= 1, col >= 1, row <= 10, col <= 10, len(grid[i]) = col for every i with 0 <= i < row, and 0 <= grid[i][j] <= 15 for every i,j with 0 <= i < row and 0 <= j < col. -/
  theorem spec_4 (grid gt : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
      (hrow : grid.val.length = row) (hcol : ncols grid = col)
      (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
      (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
      (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
      (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15)
      (hgt_rows : gt.val.length = col)
      (hgt_width : ∀ j : ℕ, j < col → rowwidth gt j = row)
      (hgt : ∀ j i : ℕ, j < col → i < row → entry gt j i = entry grid i j) :
      ∃ r rt : Std.I64,
        Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
        Aegis.NumMagicSquaresInside.num_magic_squares_inside gt = ok rt ∧ r.val = rt.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid gt : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
        (hrow : grid.val.length = row) (hcol : ncols grid = col)
        (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
        (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
        (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
        (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15)
        (hgt_rows : gt.val.length = col)
        (hgt_width : ∀ j : ℕ, j < col → rowwidth gt j = row)
        (hgt : ∀ j i : ℕ, j < col → i < row → entry gt j i = entry grid i j), ∃ r rt : Std.I64,
          Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
          Aegis.NumMagicSquaresInside.num_magic_squares_inside gt = ok rt ∧ r.val = rt.val) := by
    sorry

  /-- Let gc be the row x col grid defined by gc[i][j] = grid[i][col-1-j] for all 0 <= i < row and 0 <= j < col. The function returns result r on grid and result rc on gc, and r = rc.
    Preconditions: Let row = len(grid) and col = len(grid[0]). The preconditions are: row >= 1, col >= 1, row <= 10, col <= 10, len(grid[i]) = col for every i with 0 <= i < row, and 0 <= grid[i][j] <= 15 for every i,j with 0 <= i < row and 0 <= j < col. -/
  theorem spec_5 (grid gc : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
      (hrow : grid.val.length = row) (hcol : ncols grid = col)
      (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
      (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
      (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
      (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15)
      (hgc_rows : gc.val.length = row)
      (hgc_width : ∀ i : ℕ, i < row → rowwidth gc i = col)
      (hgc : ∀ i j : ℕ, i < row → j < col → entry gc i j = entry grid i (col - 1 - j)) :
      ∃ r rc : Std.I64,
        Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
        Aegis.NumMagicSquaresInside.num_magic_squares_inside gc = ok rc ∧ r.val = rc.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid gc : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
        (hrow : grid.val.length = row) (hcol : ncols grid = col)
        (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
        (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
        (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
        (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15)
        (hgc_rows : gc.val.length = row)
        (hgc_width : ∀ i : ℕ, i < row → rowwidth gc i = col)
        (hgc : ∀ i j : ℕ, i < row → j < col → entry gc i j = entry grid i (col - 1 - j)), ∃ r rc : Std.I64,
          Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
          Aegis.NumMagicSquaresInside.num_magic_squares_inside gc = ok rc ∧ r.val = rc.val) := by
    sorry

  /-- Let gr be the row x col grid defined by gr[i][j] = grid[row-1-i][j] for all 0 <= i < row and 0 <= j < col. The function returns result r on grid and result rr on gr, and r = rr.
    Preconditions: Let row = len(grid) and col = len(grid[0]). The preconditions are: row >= 1, col >= 1, row <= 10, col <= 10, len(grid[i]) = col for every i with 0 <= i < row, and 0 <= grid[i][j] <= 15 for every i,j with 0 <= i < row and 0 <= j < col. -/
  theorem spec_6 (grid gr : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
      (hrow : grid.val.length = row) (hcol : ncols grid = col)
      (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
      (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
      (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
      (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15)
      (hgr_rows : gr.val.length = row)
      (hgr_width : ∀ i : ℕ, i < row → rowwidth gr i = col)
      (hgr : ∀ i j : ℕ, i < row → j < col → entry gr i j = entry grid (row - 1 - i) j) :
      ∃ r rr : Std.I64,
        Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
        Aegis.NumMagicSquaresInside.num_magic_squares_inside gr = ok rr ∧ r.val = rr.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid gr : Slice (alloc.vec.Vec Std.I64)) (row col : ℕ)
        (hrow : grid.val.length = row) (hcol : ncols grid = col)
        (hrow_pos : 1 ≤ row) (hcol_pos : 1 ≤ col)
        (hrow_le : row ≤ 10) (hcol_le : col ≤ 10)
        (hwidth : ∀ i : ℕ, i < row → rowwidth grid i = col)
        (hentries : ∀ i j : ℕ, i < row → j < col → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15)
        (hgr_rows : gr.val.length = row)
        (hgr_width : ∀ i : ℕ, i < row → rowwidth gr i = col)
        (hgr : ∀ i j : ℕ, i < row → j < col → entry gr i j = entry grid (row - 1 - i) j), ∃ r rr : Std.I64,
          Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
          Aegis.NumMagicSquaresInside.num_magic_squares_inside gr = ok rr ∧ r.val = rr.val) := by
    sorry

  /-- The function returns a result r. If r = 1, then the three row sums, the three column sums, and the two diagonal sums of grid are all equal to 15.
    Preconditions: Let row = len(grid) and col = len(grid[0]). row = col = 3, len(grid[i]) = 3 for i=0,1,2, and 0 <= grid[i][j] <= 15 for all 0 <= i,j < 3. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64))
      (hrow : grid.val.length = 3)
      (hwidth : ∀ i : ℕ, i < 3 → rowwidth grid i = 3)
      (hentries : ∀ i j : ℕ, i < 3 → j < 3 → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15) :
      ∃ r : Std.I64,
        Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
        (r.val = 1 →
          rowSum grid 0 0 = 15 ∧ rowSum grid 1 0 = 15 ∧ rowSum grid 2 0 = 15 ∧
          colSum grid 0 0 = 15 ∧ colSum grid 0 1 = 15 ∧ colSum grid 0 2 = 15 ∧
          diagSum grid 0 0 = 15 ∧ antiDiagSum grid 0 0 = 15) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
        (hrow : grid.val.length = 3)
        (hwidth : ∀ i : ℕ, i < 3 → rowwidth grid i = 3)
        (hentries : ∀ i j : ℕ, i < 3 → j < 3 → 0 ≤ entry grid i j ∧ entry grid i j ≤ 15), ∃ r : Std.I64,
          Aegis.NumMagicSquaresInside.num_magic_squares_inside grid = ok r ∧
          (r.val = 1 →
            rowSum grid 0 0 = 15 ∧ rowSum grid 1 0 = 15 ∧ rowSum grid 2 0 = 15 ∧
            colSum grid 0 0 = 15 ∧ colSum grid 0 1 = 15 ∧ colSum grid 0 2 = 15 ∧
            diagSum grid 0 0 = 15 ∧ antiDiagSum grid 0 0 = 15)) := by
    sorry

  end AegisSpec.NumMagicSquaresInside
