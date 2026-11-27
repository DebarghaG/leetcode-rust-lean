import Aegis.CheckValidGrid.Code.Funs

/-!
# Specifications of `Aegis.CheckValidGrid.check_valid_grid`

LeetCode problem `check-knight-tour-configuration`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  set_option maxHeartbeats 1000000

  namespace AegisSpec.CheckValidGrid

  def rowVals (grid : Slice (alloc.vec.Vec I64)) (i : Nat) : List I64 :=
    ((grid.val[i]?).map (fun r => r.val)).getD []

  def cellI (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : I64 :=
    ((rowVals grid i)[j]?).getD 0#i64

  def cellVal (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    (cellI grid i j).val

  def cellCoords (grid : Slice (alloc.vec.Vec I64)) : List (Nat × Nat) :=
    (List.range grid.val.length).flatMap (fun i =>
      (List.range (rowVals grid i).length).map (fun j => (i, j)))

  def posOf? (grid : Slice (alloc.vec.Vec I64)) (k : Int) : Option (Nat × Nat) :=
    (cellCoords grid).findSome? (fun p => if cellVal grid p.1 p.2 = k then some p else none)

  def posRow (grid : Slice (alloc.vec.Vec I64)) (k : Nat) : Nat :=
    ((posOf? grid (k : Int)).getD (0, 0)).1

  def posCol (grid : Slice (alloc.vec.Vec I64)) (k : Nat) : Nat :=
    ((posOf? grid (k : Int)).getD (0, 0)).2

  def diffSet (r c r' c' : Nat) : Finset Nat :=
    {Int.natAbs ((r : Int) - (r' : Int)), Int.natAbs ((c : Int) - (c' : Int))}

  abbrev IsKnightStep (r c r' c' : Nat) : Prop :=
    diffSet r c r' c' = {1, 2}

  def listNOfList {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
    | [] => .nil
    | a :: l => .cons a (listNOfList l)

  def sliceOfList {α : Type} (l : List α) : Slice α :=
    Slice.mk (l.take Usize.max).length (listNOfList (l.take Usize.max))
      (List.length_take_le Usize.max l)

  def vecOfList (l : List I64) : alloc.vec.Vec I64 :=
    ⟨sliceOfList l⟩

  def transpose (grid : Slice (alloc.vec.Vec I64)) : Slice (alloc.vec.Vec I64) :=
    sliceOfList ((List.range grid.val.length).map (fun j =>
      vecOfList ((List.range grid.val.length).map (fun i => cellI grid i j))))

  /-- For 0 <= k < n*n, let (r_k, c_k) be the unique cell with grid[r_k][c_k] = k. The function returns Ok b, where b is true if and only if grid[0][0] = 0 and for every k with 0 <= k < n*n - 1, {|r_k - r_{k+1}|, |c_k - c_{k+1}|} = {1,2}. Otherwise b is false.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      ∃ b : Bool, Aegis.CheckValidGrid.check_valid_grid grid = ok b ∧
        (b = true ↔
          cellVal grid 0 0 = 0 ∧
          ∀ k : Nat, k + 1 < n * n →
            IsKnightStep (posRow grid k) (posCol grid k)
              (posRow grid (k + 1)) (posCol grid (k + 1))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), ∃ b : Bool, Aegis.CheckValidGrid.check_valid_grid grid = ok b ∧
          (b = true ↔
            cellVal grid 0 0 = 0 ∧
            ∀ k : Nat, k + 1 < n * n →
              IsKnightStep (posRow grid k) (posCol grid k)
                (posRow grid (k + 1)) (posCol grid (k + 1)))) := by
    sorry

  /-- The function returns Ok b for some Boolean b (i.e., it does not return Err and does not fail).
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      ∃ b : Bool, Aegis.CheckValidGrid.check_valid_grid grid = ok b := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), ∃ b : Bool, Aegis.CheckValidGrid.check_valid_grid grid = ok b) := by
    sorry

  /-- If the function returns Ok true, then grid[0][0] = 0.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      Aegis.CheckValidGrid.check_valid_grid grid = ok true → cellVal grid 0 0 = 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), Aegis.CheckValidGrid.check_valid_grid grid = ok true → cellVal grid 0 0 = 0) := by
    sorry

  /-- For 0 <= k < n*n, let (r_k, c_k) be the unique cell with grid[r_k][c_k] = k. If the function returns Ok true, then for every k with 0 <= k < n*n - 1, {|r_k - r_{k+1}|, |c_k - c_{k+1}|} = {1,2}.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      Aegis.CheckValidGrid.check_valid_grid grid = ok true →
        ∀ k : Nat, k + 1 < n * n →
          IsKnightStep (posRow grid k) (posCol grid k)
            (posRow grid (k + 1)) (posCol grid (k + 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), Aegis.CheckValidGrid.check_valid_grid grid = ok true →
          ∀ k : Nat, k + 1 < n * n →
            IsKnightStep (posRow grid k) (posCol grid k)
              (posRow grid (k + 1)) (posCol grid (k + 1))) := by
    sorry

  /-- For 0 <= k < n*n, let (r_k, c_k) be the unique cell with grid[r_k][c_k] = k. If grid[0][0] = 0 and for every k with 0 <= k < n*n - 1, {|r_k - r_{k+1}|, |c_k - c_{k+1}|} = {1,2}, then the function returns Ok true.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      cellVal grid 0 0 = 0 →
        (∀ k : Nat, k + 1 < n * n →
          IsKnightStep (posRow grid k) (posCol grid k)
            (posRow grid (k + 1)) (posCol grid (k + 1))) →
        Aegis.CheckValidGrid.check_valid_grid grid = ok true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), cellVal grid 0 0 = 0 →
          (∀ k : Nat, k + 1 < n * n →
            IsKnightStep (posRow grid k) (posCol grid k)
              (posRow grid (k + 1)) (posCol grid (k + 1))) →
          Aegis.CheckValidGrid.check_valid_grid grid = ok true) := by
    sorry

  /-- If grid[0][0] != 0, then the function returns Ok false.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      cellVal grid 0 0 ≠ 0 → Aegis.CheckValidGrid.check_valid_grid grid = ok false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), cellVal grid 0 0 ≠ 0 → Aegis.CheckValidGrid.check_valid_grid grid = ok false) := by
    sorry

  /-- For 0 <= k < n*n, let (r_k, c_k) be the unique cell with grid[r_k][c_k] = k. If there exists k with 0 <= k < n*n - 1 such that {|r_k - r_{k+1}|, |c_k - c_{k+1}|} != {1,2}, then the function returns Ok false.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      (∃ k : Nat, k + 1 < n * n ∧
        ¬ IsKnightStep (posRow grid k) (posCol grid k)
            (posRow grid (k + 1)) (posCol grid (k + 1))) →
        Aegis.CheckValidGrid.check_valid_grid grid = ok false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), (∃ k : Nat, k + 1 < n * n ∧
          ¬ IsKnightStep (posRow grid k) (posCol grid k)
              (posRow grid (k + 1)) (posCol grid (k + 1))) →
          Aegis.CheckValidGrid.check_valid_grid grid = ok false) := by
    sorry

  /-- Let transpose(grid) be the n x n grid defined by transpose(grid)[i][j] = grid[j][i] for 0 <= i,j < n. Then the function returns Ok b on grid if and only if it returns Ok b on transpose(grid), for the same Boolean b.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      ∀ b : Bool,
        (Aegis.CheckValidGrid.check_valid_grid grid = ok b ↔
          Aegis.CheckValidGrid.check_valid_grid (transpose grid) = ok b) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), ∀ b : Bool,
          (Aegis.CheckValidGrid.check_valid_grid grid = ok b ↔
            Aegis.CheckValidGrid.check_valid_grid (transpose grid) = ok b)) := by
    sorry

  /-- The function returns Ok false.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct; and n = 3. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j')
      (hn3 : n = 3) :
      Aegis.CheckValidGrid.check_valid_grid grid = ok false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j')
        (hn3 : n = 3), Aegis.CheckValidGrid.check_valid_grid grid = ok false) := by
    sorry

  /-- For 0 <= k < n*n, let (r_k, c_k) be the unique cell with grid[r_k][c_k] = k. If the function returns Ok true, then for every k with 0 <= k < n*n, (r_k + c_k) mod 2 = k mod 2.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      Aegis.CheckValidGrid.check_valid_grid grid = ok true →
        ∀ k : Nat, k < n * n → (posRow grid k + posCol grid k) % 2 = k % 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), Aegis.CheckValidGrid.check_valid_grid grid = ok true →
          ∀ k : Nat, k < n * n → (posRow grid k + posCol grid k) % 2 = k % 2) := by
    sorry

  /-- For 0 <= k < n*n, let (r_k, c_k) be the unique cell with grid[r_k][c_k] = k. If the function returns Ok true, then the sequence ((r_0,c_0), (r_1,c_1), ..., (r_{n*n-1}, c_{n*n-1})) is a valid knight's tour: (r_0,c_0) = (0,0), all cells are distinct, and for every k with 0 <= k < n*n - 1, the cells (r_k,c_k) and (r_{k+1},c_{k+1}) are a knight move apart.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      Aegis.CheckValidGrid.check_valid_grid grid = ok true →
        posRow grid 0 = 0 ∧ posCol grid 0 = 0 ∧
        (∀ k k' : Nat, k < n * n → k' < n * n →
          (posRow grid k, posCol grid k) = (posRow grid k', posCol grid k') → k = k') ∧
        (∀ k : Nat, k + 1 < n * n →
          IsKnightStep (posRow grid k) (posCol grid k)
            (posRow grid (k + 1)) (posCol grid (k + 1))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), Aegis.CheckValidGrid.check_valid_grid grid = ok true →
          posRow grid 0 = 0 ∧ posCol grid 0 = 0 ∧
          (∀ k k' : Nat, k < n * n → k' < n * n →
            (posRow grid k, posCol grid k) = (posRow grid k', posCol grid k') → k = k') ∧
          (∀ k : Nat, k + 1 < n * n →
            IsKnightStep (posRow grid k) (posCol grid k)
              (posRow grid (k + 1)) (posCol grid (k + 1)))) := by
    sorry

  /-- For 0 <= k < n*n, let (r_k, c_k) be the unique cell with grid[r_k][c_k] = k. If the function returns Ok false, then either grid[0][0] != 0, or there exists k with 0 <= k < n*n - 1 such that {|r_k - r_{k+1}|, |c_k - c_{k+1}|} != {1,2}.
    Preconditions: Let n = len(grid). The following hold: (i) for every i with 0 <= i < n, len(grid[i]) = n; (ii) 3 <= n <= 7; (iii) for every i,j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] < n*n; (iv) all values grid[i][j] are distinct. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
      (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
      (h_size : 3 ≤ n ∧ n ≤ 7)
      (h_range : ∀ i j, i < n → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
      (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
        cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j') :
      Aegis.CheckValidGrid.check_valid_grid grid = ok false →
        cellVal grid 0 0 ≠ 0 ∨
          ∃ k : Nat, k + 1 < n * n ∧
            ¬ IsKnightStep (posRow grid k) (posCol grid k)
                (posRow grid (k + 1)) (posCol grid (k + 1)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (n : Nat) (hn : n = grid.val.length)
        (h_rows : ∀ i, i < n → (rowVals grid i).length = n)
        (h_size : 3 ≤ n ∧ n ≤ 7)
        (h_range : ∀ i j, i < n → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < (n : Int) * (n : Int))
        (h_distinct : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          cellVal grid i j = cellVal grid i' j' → i = i' ∧ j = j'), Aegis.CheckValidGrid.check_valid_grid grid = ok false →
          cellVal grid 0 0 ≠ 0 ∨
            ∃ k : Nat, k + 1 < n * n ∧
              ¬ IsKnightStep (posRow grid k) (posCol grid k)
                  (posRow grid (k + 1)) (posCol grid (k + 1))) := by
    sorry

  end AegisSpec.CheckValidGrid
