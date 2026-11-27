import Aegis.PossibleToStamp.Code.Funs

/-!
# Specifications of `Aegis.PossibleToStamp.possible_to_stamp`

LeetCode problem `stamping-the-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PossibleToStamp

  abbrev Grid := Slice (alloc.vec.Vec I64)

  def cellVal (grid : Grid) (i j : Nat) : Option Int :=
    (grid.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))

  def AllZero (grid : Grid) (m n : Nat) : Prop :=
    ∀ i j, i < m → j < n → cellVal grid i j = some 0

  def AllOne (grid : Grid) (m n : Nat) : Prop :=
    ∀ i j, i < m → j < n → cellVal grid i j = some 1

  def Covers (h w : Int) (top left i j : Nat) : Prop :=
    top ≤ i ∧ i < top + h.toNat ∧ left ≤ j ∧ j < left + w.toNat

  def AllZeroIn (grid : Grid) (h w : Int) (top left : Nat) : Prop :=
    ∀ u v, top ≤ u → u < top + h.toNat → left ≤ v → v < left + w.toNat →
      cellVal grid u v = some 0

  def Stampable (grid : Grid) (m n : Nat) (h w : Int) : Prop :=
    ∀ i j, i < m → j < n → cellVal grid i j = some 0 →
      ∃ top left, top + h.toNat ≤ m ∧ left + w.toNat ≤ n ∧
        Covers h w top left i j ∧ AllZeroIn grid h w top left

  def Blocked (grid : Grid) (m n : Nat) (h w : Int) (i j : Nat) : Prop :=
    ∀ top left, top + h.toNat ≤ m → left + w.toNat ≤ n → Covers h w top left i j →
      ∃ u v, top ≤ u ∧ u < top + h.toNat ∧ left ≤ v ∧ v < left + w.toNat ∧
        cellVal grid u v = some 1

  def IsTranspose (grid transposed : Grid) (m n : Nat) : Prop :=
    transposed.val.length = n ∧
      (∀ row ∈ transposed.val, row.val.length = m) ∧
      (∀ j i, j < n → i < m → cellVal transposed j i = cellVal grid i j)

  open Aegis.PossibleToStamp

  /-- Whenever possible_to_stamp(grid, stampHeight, stampWidth) returns a result r, r is true if and only if for every cell (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 0, there exist integers top and left (the 0-based row and column of the stamp top-left corner) such that 0 <= top <= m - stampHeight, 0 <= left <= n - stampWidth, top <= i < top + stampHeight, left <= j < left + stampWidth, and for every u,v with top <= u < top + stampHeight and left <= v < left + stampWidth, grid[u][v] = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_1
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000) :
      ∀ r, possible_to_stamp grid stampHeight stampWidth = ok r →
        (r = true ↔ Stampable grid m n stampHeight.val stampWidth.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000), ∀ r, possible_to_stamp grid stampHeight stampWidth = ok r →
          (r = true ↔ Stampable grid m n stampHeight.val stampWidth.val)) := by
    sorry

  /-- For every input satisfying the preconditions, possible_to_stamp(grid, stampHeight, stampWidth) returns some Result Bool value; it does not fail, panic, overflow, or access any grid cell out of bounds.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_2
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000) :
      ∃ r, possible_to_stamp grid stampHeight stampWidth = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000), ∃ r, possible_to_stamp grid stampHeight stampWidth = ok r) := by
    sorry

  /-- If grid[i][j] = 1 for every 0 <= i < m and every 0 <= j < n, then the function returns true.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_3
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hones : AllOne grid m n) :
      possible_to_stamp grid stampHeight stampWidth = ok true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hones : AllOne grid m n), possible_to_stamp grid stampHeight stampWidth = ok true) := by
    sorry

  /-- If grid[i][j] = 0 for every 0 <= i < m and every 0 <= j < n, then the function returns true if and only if stampHeight <= m and stampWidth <= n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_4
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hzeros : AllZero grid m n) :
      (possible_to_stamp grid stampHeight stampWidth = ok true ↔
        stampHeight.val ≤ (m : Int) ∧ stampWidth.val ≤ (n : Int)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hzeros : AllZero grid m n), (possible_to_stamp grid stampHeight stampWidth = ok true ↔
          stampHeight.val ≤ (m : Int) ∧ stampWidth.val ≤ (n : Int))) := by
    sorry

  /-- If stampHeight = 1 and stampWidth = 1, then the function returns true.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_5
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hsh : stampHeight.val = 1) (hsw : stampWidth.val = 1) :
      possible_to_stamp grid stampHeight stampWidth = ok true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hsh : stampHeight.val = 1) (hsw : stampWidth.val = 1), possible_to_stamp grid stampHeight stampWidth = ok true) := by
    sorry

  /-- If the function returns true and there is at least one empty cell, meaning some cell (i,j) has grid[i][j] = 0, then stampHeight <= m and stampWidth <= n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_6
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hres : possible_to_stamp grid stampHeight stampWidth = ok true)
      (hempty : ∃ i j, i < m ∧ j < n ∧ cellVal grid i j = some 0) :
      stampHeight.val ≤ (m : Int) ∧ stampWidth.val ≤ (n : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hres : possible_to_stamp grid stampHeight stampWidth = ok true)
        (hempty : ∃ i j, i < m ∧ j < n ∧ cellVal grid i j = some 0), stampHeight.val ≤ (m : Int) ∧ stampWidth.val ≤ (n : Int)) := by
    sorry

  /-- If stampHeight = m and stampWidth = n, then the function returns true if and only if either grid[i][j] = 0 for every cell or grid[i][j] = 1 for every cell; equivalently, there do not exist both a cell with value 0 and a cell with value 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_7
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hsh : stampHeight.val = (m : Int)) (hsw : stampWidth.val = (n : Int)) :
      (possible_to_stamp grid stampHeight stampWidth = ok true ↔
        AllZero grid m n ∨ AllOne grid m n) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hsh : stampHeight.val = (m : Int)) (hsw : stampWidth.val = (n : Int)), (possible_to_stamp grid stampHeight stampWidth = ok true ↔
          AllZero grid m n ∨ AllOne grid m n)) := by
    sorry

  /-- For any integers h' and w' with 1 <= h' <= stampHeight and 1 <= w' <= stampWidth, if possible_to_stamp(grid, stampHeight, stampWidth) returns true, then possible_to_stamp(grid, h', w') returns true.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_8
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (h' w' : I64)
      (hh'_pos : 1 ≤ h'.val) (hh'_le : h'.val ≤ stampHeight.val)
      (hw'_pos : 1 ≤ w'.val) (hw'_le : w'.val ≤ stampWidth.val)
      (hres : possible_to_stamp grid stampHeight stampWidth = ok true) :
      possible_to_stamp grid h' w' = ok true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (h' w' : I64)
        (hh'_pos : 1 ≤ h'.val) (hh'_le : h'.val ≤ stampHeight.val)
        (hw'_pos : 1 ≤ w'.val) (hw'_le : w'.val ≤ stampWidth.val)
        (hres : possible_to_stamp grid stampHeight stampWidth = ok true), possible_to_stamp grid h' w' = ok true) := by
    sorry

  /-- Let transposed be the n x m grid defined by transposed[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Then possible_to_stamp(grid, stampHeight, stampWidth) returns true if and only if possible_to_stamp(transposed, stampWidth, stampHeight) returns true.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_9
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (transposed : Grid) (ht : IsTranspose grid transposed m n) :
      (possible_to_stamp grid stampHeight stampWidth = ok true ↔
        possible_to_stamp transposed stampWidth stampHeight = ok true) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (transposed : Grid) (ht : IsTranspose grid transposed m n), (possible_to_stamp grid stampHeight stampWidth = ok true ↔
          possible_to_stamp transposed stampWidth stampHeight = ok true)) := by
    sorry

  /-- If possible_to_stamp(grid, stampHeight, stampWidth) returns false, then there exists a cell (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 0 such that for every pair of integers (top,left) satisfying 0 <= top <= m - stampHeight, 0 <= left <= n - stampWidth, top <= i < top + stampHeight, and left <= j < left + stampWidth, there exists a cell (u,v) with top <= u < top + stampHeight, left <= v < left + stampWidth, and grid[u][v] = 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_10
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hres : possible_to_stamp grid stampHeight stampWidth = ok false) :
      ∃ i j, i < m ∧ j < n ∧ cellVal grid i j = some 0 ∧
        Blocked grid m n stampHeight.val stampWidth.val i j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hres : possible_to_stamp grid stampHeight stampWidth = ok false), ∃ i j, i < m ∧ j < n ∧ cellVal grid i j = some 0 ∧
          Blocked grid m n stampHeight.val stampWidth.val i j) := by
    sorry

  /-- If stampHeight = m and stampWidth = 1, then the function returns true if and only if for every column j with 0 <= j < n, either grid[i][j] = 0 for every i with 0 <= i < m, or grid[i][j] = 1 for every i with 0 <= i < m.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_11
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hsh : stampHeight.val = (m : Int)) (hsw : stampWidth.val = 1) :
      (possible_to_stamp grid stampHeight stampWidth = ok true ↔
        ∀ j, j < n →
          (∀ i, i < m → cellVal grid i j = some 0) ∨
            (∀ i, i < m → cellVal grid i j = some 1)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hsh : stampHeight.val = (m : Int)) (hsw : stampWidth.val = 1), (possible_to_stamp grid stampHeight stampWidth = ok true ↔
          ∀ j, j < n →
            (∀ i, i < m → cellVal grid i j = some 0) ∨
              (∀ i, i < m → cellVal grid i j = some 1))) := by
    sorry

  /-- If stampHeight > m or stampWidth > n, then the function returns true if and only if grid[i][j] = 1 for every cell (i,j) with 0 <= i < m and 0 <= j < n; that is, if and only if there are no empty cells.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 100000, 1 <= n <= 100000, every row of grid has length n, 1 <= m*n <= 200000, every grid[r][c] is 0 or 1, and 1 <= stampHeight <= 100000 and 1 <= stampWidth <= 100000. -/
  theorem spec_12
      (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
      (hbin : ∀ i j, i < m → j < n →
        cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
      (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
      (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
      (hbig : (m : Int) < stampHeight.val ∨ (n : Int) < stampWidth.val) :
      (possible_to_stamp grid stampHeight stampWidth = ok true ↔
        AllOne grid m n) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Grid) (stampHeight stampWidth : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm_pos : 1 ≤ m) (hm_le : m ≤ 100000)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hprod_pos : 1 ≤ m * n) (hprod_le : m * n ≤ 200000)
        (hbin : ∀ i j, i < m → j < n →
          cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)
        (hsh_pos : 1 ≤ stampHeight.val) (hsh_le : stampHeight.val ≤ 100000)
        (hsw_pos : 1 ≤ stampWidth.val) (hsw_le : stampWidth.val ≤ 100000)
        (hbig : (m : Int) < stampHeight.val ∨ (n : Int) < stampWidth.val), (possible_to_stamp grid stampHeight stampWidth = ok true ↔
          AllOne grid m n)) := by
    sorry

  end AegisSpec.PossibleToStamp
