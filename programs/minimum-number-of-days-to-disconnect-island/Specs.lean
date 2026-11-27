import Aegis.MinDays.Code.Funs

/-!
# Specifications of `Aegis.MinDays.min_days`

LeetCode problem `minimum-number-of-days-to-disconnect-island`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.MinDays

  namespace AegisSpec.MinDays

  def rowVals (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    match grid.val[i]? with
    | some row => row.val.map (fun c => c.val)
    | none => []

  def cellAt (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (rowVals grid i).getD j 0

  def gridFun (grid : Slice (alloc.vec.Vec Std.I64)) : Nat → Nat → Int :=
    fun i j => cellAt grid i j

  def IsLand (G : Nat → Nat → Int) (p : Nat × Nat) : Prop :=
    G p.1 p.2 = 1

  def InLand (G : Nat → Nat → Int) (m n : Nat) (p : Nat × Nat) : Prop :=
    p.1 < m ∧ p.2 < n ∧ IsLand G p

  def dist (p q : Nat × Nat) : Nat :=
    ((p.1 : Int) - (q.1 : Int)).natAbs + ((p.2 : Int) - (q.2 : Int)).natAbs

  def Adj (p q : Nat × Nat) : Prop :=
    dist p q = 1

  inductive Conn (G : Nat → Nat → Int) : Nat × Nat → Nat × Nat → Prop
    | refl (p) : IsLand G p → Conn G p p
    | step (p q) : IsLand G p → IsLand G q → Adj p q → Conn G p q
    | symm {p q} : Conn G p q → Conn G q p
    | trans {p q r} : Conn G p q → Conn G q r → Conn G p r

  def LandCell (G : Nat → Nat → Int) (m n : Nat) : Type :=
    {p : Nat × Nat // InLand G m n p}

  noncomputable def numIslands (G : Nat → Nat → Int) (m n : Nat) : Nat :=
    Nat.card (Quot (fun p q : LandCell G m n => Conn G p.1 q.1))

  def Disconnected (G : Nat → Nat → Int) (m n : Nat) : Prop :=
    numIslands G m n = 0 ∨ 2 ≤ numIslands G m n

  def SetToZero (G : Nat → Nat → Int) (S : Finset (Nat × Nat)) : Nat → Nat → Int :=
    fun i j => if (i, j) ∈ S then 0 else G i j

  def landCount (G : Nat → Nat → Int) (m n : Nat) : Nat :=
    ((Finset.range m).product (Finset.range n)).filter (fun p => G p.1 p.2 = 1) |>.card

  /-- The function returns a result r (it does not fail). Let L = {(i,j) | 0 ≤ i < m, 0 ≤ j < n, grid[i][j] = 1}. For S ⊆ L, let G_S be the grid obtained from grid by changing exactly the cells in S from 1 to 0. Call G_S disconnected if the set of cells of G_S equal to 1 has either 0 or at least 2 maximal 4-directionally connected components, where two 1-cells are in the same component iff they are connected by a path of 1-cells moving only up, down, left, or right. Then r = min { |S| : S ⊆ L and G_S is disconnected }.
    Preconditions: Let m = len(grid). Assume the input satisfies the problem constraints: m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_1
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r, min_days grid = ok r ∧
        (∃ S : Finset (Nat × Nat),
          (∀ p ∈ S, InLand (gridFun grid) m n p) ∧
          Disconnected (SetToZero (gridFun grid) S) m n ∧
          r.val = (S.card : Int)) ∧
        (∀ S : Finset (Nat × Nat),
          (∀ p ∈ S, InLand (gridFun grid) m n p) →
          Disconnected (SetToZero (gridFun grid) S) m n →
          r.val ≤ (S.card : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r, min_days grid = ok r ∧
          (∃ S : Finset (Nat × Nat),
            (∀ p ∈ S, InLand (gridFun grid) m n p) ∧
            Disconnected (SetToZero (gridFun grid) S) m n ∧
            r.val = (S.card : Int)) ∧
          (∀ S : Finset (Nat × Nat),
            (∀ p ∈ S, InLand (gridFun grid) m n p) →
            Disconnected (SetToZero (gridFun grid) S) m n →
            r.val ≤ (S.card : Int))) := by
    sorry

  /-- The function returns a result r on every input satisfying the preconditions; it never overflows, panics, or goes out of bounds.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_2
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∃ r, min_days grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∃ r, min_days grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 ≤ r ≤ 2.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_3
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∀ r, min_days grid = ok r → 0 ≤ r.val ∧ r.val ≤ 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∀ r, min_days grid = ok r → 0 ≤ r.val ∧ r.val ≤ 2) := by
    sorry

  /-- Let k be the number of islands in the initial grid, i.e. the number of maximal 4-directionally connected components of cells with value 1, where k may be 0. Whenever the function returns r, r = 0 if and only if k ≠ 1; equivalently, r = 0 exactly when the initial grid is already disconnected.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_4
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∀ r, min_days grid = ok r →
        (r.val = 0 ↔ numIslands (gridFun grid) m n ≠ 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∀ r, min_days grid = ok r →
          (r.val = 0 ↔ numIslands (gridFun grid) m n ≠ 1)) := by
    sorry

  /-- Whenever the function returns r, r = 1 if and only if the initial grid has exactly one island and there exists a land cell (i,j) with grid[i][j] = 1 such that changing only that cell from 1 to 0 produces a grid whose number of islands is not 1.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_5
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∀ r, min_days grid = ok r →
        (r.val = 1 ↔
          numIslands (gridFun grid) m n = 1 ∧
          ∃ p : Nat × Nat,
            InLand (gridFun grid) m n p ∧
            numIslands (SetToZero (gridFun grid) ({p} : Finset (Nat × Nat))) m n ≠ 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∀ r, min_days grid = ok r →
          (r.val = 1 ↔
            numIslands (gridFun grid) m n = 1 ∧
            ∃ p : Nat × Nat,
              InLand (gridFun grid) m n p ∧
              numIslands (SetToZero (gridFun grid) ({p} : Finset (Nat × Nat))) m n ≠ 1)) := by
    sorry

  /-- Whenever the function returns r, r = 2 if and only if the initial grid has exactly one island and, for every land cell (i,j) with grid[i][j] = 1, changing only that cell from 1 to 0 leaves a grid with exactly one island.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_6
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∀ r, min_days grid = ok r →
        (r.val = 2 ↔
          numIslands (gridFun grid) m n = 1 ∧
          ∀ p : Nat × Nat,
            InLand (gridFun grid) m n p →
            numIslands (SetToZero (gridFun grid) ({p} : Finset (Nat × Nat))) m n = 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∀ r, min_days grid = ok r →
          (r.val = 2 ↔
            numIslands (gridFun grid) m n = 1 ∧
            ∀ p : Nat × Nat,
              InLand (gridFun grid) m n p →
              numIslands (SetToZero (gridFun grid) ({p} : Finset (Nat × Nat))) m n = 1)) := by
    sorry

  /-- Whenever the function returns r and r = 2, there exist two distinct land cells (i1,j1) and (i2,j2) of the initial grid such that changing both from 1 to 0 produces a grid whose number of islands is not 1.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_7
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1) :
      ∀ r, min_days grid = ok r → r.val = 2 →
        ∃ p q : Nat × Nat,
          InLand (gridFun grid) m n p ∧
          InLand (gridFun grid) m n q ∧
          p ≠ q ∧
          numIslands (SetToZero (gridFun grid) ({p, q} : Finset (Nat × Nat))) m n ≠ 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1), ∀ r, min_days grid = ok r → r.val = 2 →
          ∃ p q : Nat × Nat,
            InLand (gridFun grid) m n p ∧
            InLand (gridFun grid) m n q ∧
            p ≠ q ∧
            numIslands (SetToZero (gridFun grid) ({p, q} : Finset (Nat × Nat))) m n ≠ 1) := by
    sorry

  /-- The function returns r = 1.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n; and there is exactly one pair (i,j) with grid[i][j] = 1. -/
  theorem spec_8
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (i0 j0 : Nat) (hi0 : i0 < m) (hj0 : j0 < n)
      (hland : cellAt grid i0 j0 = 1)
      (huniq : ∀ i j, i < m → j < n → cellAt grid i j = 1 → i = i0 ∧ j = j0) :
      ∃ r, min_days grid = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (i0 j0 : Nat) (hi0 : i0 < m) (hj0 : j0 < n)
        (hland : cellAt grid i0 j0 = 1)
        (huniq : ∀ i j, i < m → j < n → cellAt grid i j = 1 → i = i0 ∧ j = j0), ∃ r, min_days grid = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns r, and r = 1 if k = 1 or k ≥ 3, while r = 2 if k = 2.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n; either m = 1 or n = 1; and the initial grid has exactly one island. Let k be the number of cells equal to 1; then k ≥ 1. -/
  theorem spec_9
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (hline : m = 1 ∨ n = 1)
      (hisle : numIslands (gridFun grid) m n = 1) :
      ∃ r, min_days grid = ok r ∧
        ((landCount (gridFun grid) m n = 1 ∨ 3 ≤ landCount (gridFun grid) m n) → r.val = 1) ∧
        (landCount (gridFun grid) m n = 2 → r.val = 2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (hline : m = 1 ∨ n = 1)
        (hisle : numIslands (gridFun grid) m n = 1), ∃ r, min_days grid = ok r ∧
          ((landCount (gridFun grid) m n = 1 ∨ 3 ≤ landCount (gridFun grid) m n) → r.val = 1) ∧
          (landCount (gridFun grid) m n = 2 → r.val = 2)) := by
    sorry

  /-- The function returns r = 0 if |i1-i2| + |j1-j2| ≠ 1, and returns r = 2 if |i1-i2| + |j1-j2| = 1.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n; and exactly two cells, (i1,j1) and (i2,j2), have value 1. -/
  theorem spec_10
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (i1 j1 i2 j2 : Nat)
      (hi1 : i1 < m) (hj1 : j1 < n) (hi2 : i2 < m) (hj2 : j2 < n)
      (hne : (i1, j1) ≠ (i2, j2))
      (hex : ∀ i j, i < m → j < n →
        (cellAt grid i j = 1 ↔ (i = i1 ∧ j = j1) ∨ (i = i2 ∧ j = j2))) :
      ∃ r, min_days grid = ok r ∧
        (dist (i1, j1) (i2, j2) ≠ 1 → r.val = 0) ∧
        (dist (i1, j1) (i2, j2) = 1 → r.val = 2) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (i1 j1 i2 j2 : Nat)
        (hi1 : i1 < m) (hj1 : j1 < n) (hi2 : i2 < m) (hj2 : j2 < n)
        (hne : (i1, j1) ≠ (i2, j2))
        (hex : ∀ i j, i < m → j < n →
          (cellAt grid i j = 1 ↔ (i = i1 ∧ j = j1) ∨ (i = i2 ∧ j = j2))), ∃ r, min_days grid = ok r ∧
          (dist (i1, j1) (i2, j2) ≠ 1 → r.val = 0) ∧
          (dist (i1, j1) (i2, j2) = 1 → r.val = 2)) := by
    sorry

  /-- Let gridT be the n × m grid defined by gridT[j][i] = grid[i][j] for all i,j. If r is the result of the function on grid and rT is the result of the function on gridT, then r = rT.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_11
      (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (hTm : gridT.val.length = n)
      (hTn : ∀ i, i < n → (rowVals gridT i).length = m)
      (hT : ∀ i j, i < m → j < n → cellAt gridT j i = cellAt grid i j) :
      ∀ r rT, min_days grid = ok r → min_days gridT = ok rT → r.val = rT.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (hTm : gridT.val.length = n)
        (hTn : ∀ i, i < n → (rowVals gridT i).length = m)
        (hT : ∀ i j, i < m → j < n → cellAt gridT j i = cellAt grid i j), ∀ r rT, min_days grid = ok r → min_days gridT = ok rT → r.val = rT.val) := by
    sorry

  /-- Let H be the grid obtained by reversing the order of the rows of grid, so H[i][j] = grid[m-1-i][j], and let K be the grid obtained by reversing each row of grid, so K[i][j] = grid[i][n-1-j]. If r, rH, and rK are the results of the function on grid, H, and K respectively, then r = rH = rK.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. -/
  theorem spec_12
      (grid H K : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (hHm : H.val.length = m)
      (hHn : ∀ i, i < m → (rowVals H i).length = n)
      (hH : ∀ i j, i < m → j < n → cellAt H i j = cellAt grid (m - 1 - i) j)
      (hKm : K.val.length = m)
      (hKn : ∀ i, i < m → (rowVals K i).length = n)
      (hK : ∀ i j, i < m → j < n → cellAt K i j = cellAt grid i (n - 1 - j)) :
      ∀ r rH rK, min_days grid = ok r → min_days H = ok rH → min_days K = ok rK →
        r.val = rH.val ∧ r.val = rK.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid H K : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (hHm : H.val.length = m)
        (hHn : ∀ i, i < m → (rowVals H i).length = n)
        (hH : ∀ i j, i < m → j < n → cellAt H i j = cellAt grid (m - 1 - i) j)
        (hKm : K.val.length = m)
        (hKn : ∀ i, i < m → (rowVals K i).length = n)
        (hK : ∀ i j, i < m → j < n → cellAt K i j = cellAt grid i (n - 1 - j)), ∀ r rH rK, min_days grid = ok r → min_days H = ok rH → min_days K = ok rK →
          r.val = rH.val ∧ r.val = rK.val) := by
    sorry

  /-- If r is the result of the function on grid and r' is the result of the function on grid', then r = r'.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; and grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n. Let grid' be any M' × N' binary grid with 1 ≤ M',N' ≤ 30 obtained from grid by inserting some number of all-zero rows above and below and all-zero columns to the left and right, so that grid occurs as a contiguous subgrid of grid' and every other cell of grid' is 0. -/
  theorem spec_13
      (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n M' N' ro co : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (hM'1 : 1 ≤ M') (hM'30 : M' ≤ 30) (hN'1 : 1 ≤ N') (hN'30 : N' ≤ 30)
      (hgm : grid'.val.length = M')
      (hgn : ∀ i, i < M' → (rowVals grid' i).length = N')
      (hfit : ro + m ≤ M' ∧ co + n ≤ N')
      (hpaste : ∀ i j, i < M' → j < N' →
        cellAt grid' i j =
          if ro ≤ i ∧ i < ro + m ∧ co ≤ j ∧ j < co + n
          then cellAt grid (i - ro) (j - co) else 0) :
      ∀ r r', min_days grid = ok r → min_days grid' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n M' N' ro co : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (hM'1 : 1 ≤ M') (hM'30 : M' ≤ 30) (hN'1 : 1 ≤ N') (hN'30 : N' ≤ 30)
        (hgm : grid'.val.length = M')
        (hgn : ∀ i, i < M' → (rowVals grid' i).length = N')
        (hfit : ro + m ≤ M' ∧ co + n ≤ N')
        (hpaste : ∀ i j, i < M' → j < N' →
          cellAt grid' i j =
            if ro ≤ i ∧ i < ro + m ∧ co ≤ j ∧ j < co + n
            then cellAt grid (i - ro) (j - co) else 0), ∀ r r', min_days grid = ok r → min_days grid' = ok r' → r.val = r'.val) := by
    sorry

  /-- The function returns r = 2.
    Preconditions: Let m = len(grid). Assume m ≥ 1; there is an integer n ≥ 1 with len(grid[i]) = n for every 0 ≤ i < m; m ≤ 30 and n ≤ 30; grid[i][j] ∈ {0,1} for every 0 ≤ i < m and 0 ≤ j < n; grid[i][j] = 1 for every i,j; and m ≥ 2 and n ≥ 2. -/
  theorem spec_14
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hn : ∀ i, i < m → (rowVals grid i).length = n)
      (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
      (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
      (hfull : ∀ i j, i < m → j < n → cellAt grid i j = 1)
      (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) :
      ∃ r, min_days grid = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hn : ∀ i, i < m → (rowVals grid i).length = n)
        (hm1 : 1 ≤ m) (hm30 : m ≤ 30) (hn1 : 1 ≤ n) (hn30 : n ≤ 30)
        (hb : ∀ i j, i < m → j < n → cellAt grid i j = 0 ∨ cellAt grid i j = 1)
        (hfull : ∀ i j, i < m → j < n → cellAt grid i j = 1)
        (hm2 : 2 ≤ m) (hn2 : 2 ≤ n), ∃ r, min_days grid = ok r ∧ r.val = 2) := by
    sorry

  end AegisSpec.MinDays
