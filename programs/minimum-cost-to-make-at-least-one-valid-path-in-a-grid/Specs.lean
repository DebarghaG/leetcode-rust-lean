import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `minimum-cost-to-make-at-least-one-valid-path-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinCost

  abbrev Grid := Slice (alloc.vec.Vec Std.I64)

  def cell (grid : Grid) (i j : Nat) : Option Int :=
    (grid.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))

  def PointsTo (s : Int) (p q : Nat × Nat) : Prop :=
    (s = 1 ∧ q.1 = p.1 ∧ q.2 = p.2 + 1) ∨
    (s = 2 ∧ q.1 = p.1 ∧ p.2 = q.2 + 1) ∨
    (s = 3 ∧ q.1 = p.1 + 1 ∧ q.2 = p.2) ∨
    (s = 4 ∧ p.1 = q.1 + 1 ∧ q.2 = p.2)

  instance decidablePointsTo (s : Int) (p q : Nat × Nat) : Decidable (PointsTo s p q) := by
    unfold PointsTo
    infer_instance

  def Adj (p q : Nat × Nat) : Prop :=
    (p.1 = q.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)) ∨
    (p.2 = q.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1))

  def IsPath (m n : Nat) (P : List (Nat × Nat)) : Prop :=
    P.head? = some (0, 0) ∧
    P.getLast? = some (m - 1, n - 1) ∧
    P.Nodup ∧
    (∀ p ∈ P, p.1 < m ∧ p.2 < n) ∧
    (∀ pq ∈ P.zip P.tail, Adj pq.1 pq.2)

  def stepCost (grid : Grid) (p q : Nat × Nat) : Nat :=
    match cell grid p.1 p.2 with
    | some s => if PointsTo s p q then 0 else 1
    | none => 1

  def pathCost (grid : Grid) (P : List (Nat × Nat)) : Nat :=
    ((P.zip P.tail).map (fun pq => stepCost grid pq.1 pq.2)).sum

  def IsMinPathCost (grid : Grid) (m n : Nat) (c : Int) : Prop :=
    (∀ P, IsPath m n P → c ≤ (pathCost grid P : Int)) ∧
    ∃ P, IsPath m n P ∧ (pathCost grid P : Int) = c

  def ValidShape (grid : Grid) (m n : Nat) : Prop :=
    1 ≤ m ∧ 1 ≤ n ∧ m ≤ 100 ∧ n ≤ 100 ∧
    grid.val.length = m ∧
    (∀ i, i < m → ∀ row, grid.val[i]? = some row → row.val.length = n)

  def ValidGrid (grid : Grid) (m n : Nat) : Prop :=
    ValidShape grid m n ∧
    (∀ i j, i < m → j < n →
      ∃ s, cell grid i j = some s ∧ (s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4))

  def countNotEq (k : Nat) (f : Nat → Option Int) (s : Int) : Nat :=
    ((List.range k).filter (fun j => decide (f j ≠ some s))).length

  /-- Whenever min_cost(grid) returns a result r, r equals the minimum, over every simple path P = ((i_0,j_0),...,(i_L,j_L)) with L >= 0, (i_0,j_0) = (0,0), (i_L,j_L) = (m-1,n-1), 0 <= i_t < m, 0 <= j_t < n, all pairs (i_t,j_t) distinct, and |i_{t+1}-i_t| + |j_{t+1}-j_t| = 1 for every 0 <= t < L, of the number of indices t with 0 <= t < L such that grid[i_t][j_t] is not the sign pointing from (i_t,j_t) to (i_{t+1},j_{t+1}); here 1 points right to (i,j+1), 2 points left to (i,j-1), 3 points down to (i+1,j), and 4 points up to (i-1,j).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is in {1,2,3,4} for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r) :
      IsMinPathCost grid m n r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r), IsMinPathCost grid m n r.val) := by
    sorry

  /-- For every grid satisfying the preconditions, min_cost(grid) returns a result r (it does not fail).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is in {1,2,3,4} for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n) :
      ∃ r, Aegis.MinCost.min_cost grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : ValidGrid grid m n), ∃ r, Aegis.MinCost.min_cost grid = ok r) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r >= 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is in {1,2,3,4} for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r <= m + n - 2.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is in {1,2,3,4} for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r) :
      r.val ≤ (m : Int) + (n : Int) - 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r), r.val ≤ (m : Int) + (n : Int) - 2) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r = 0 if and only if there exists a simple path P = ((i_0,j_0),...,(i_L,j_L)) from (0,0) to (m-1,n-1) such that for every 0 <= t < L, grid[i_t][j_t] is exactly the sign pointing from (i_t,j_t) to (i_{t+1},j_{t+1}) (1 right, 2 left, 3 down, 4 up).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is in {1,2,3,4} for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r) :
      r.val = 0 ↔ ∃ P, IsPath m n P ∧ pathCost grid P = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r), r.val = 0 ↔ ∃ P, IsPath m n P ∧ pathCost grid P = 0) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, there exists a simple path P = ((i_0,j_0),...,(i_L,j_L)) from (0,0) to (m-1,n-1) whose cost is exactly r, where the cost of P is the number of indices t with 0 <= t < L such that grid[i_t][j_t] does not point from (i_t,j_t) to (i_{t+1},j_{t+1}) (1 right, 2 left, 3 down, 4 up).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is in {1,2,3,4} for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r) :
      ∃ P, IsPath m n P ∧ (pathCost grid P : Int) = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hgrid : ValidGrid grid m n) (h : Aegis.MinCost.min_cost grid = ok r), ∃ P, IsPath m n P ∧ (pathCost grid P : Int) = r.val) := by
    sorry

  /-- For any grid' satisfying the same preconditions with the same m and n and with grid'[i][j] = grid[i][j] for every cell except possibly (m-1,n-1), if min_cost(grid) returns r and min_cost(grid') returns r', then r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is in {1,2,3,4} for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (grid grid' : Grid) (m n : Nat) (r r' : Std.I64)
      (hgrid : ValidGrid grid m n) (hgrid' : ValidGrid grid' m n)
      (hagree : ∀ i j, i < m → j < n → (i, j) ≠ (m - 1, n - 1) →
        cell grid' i j = cell grid i j)
      (h : Aegis.MinCost.min_cost grid = ok r)
      (h' : Aegis.MinCost.min_cost grid' = ok r') :
      r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid grid' : Grid) (m n : Nat) (r r' : Std.I64)
        (hgrid : ValidGrid grid m n) (hgrid' : ValidGrid grid' m n)
        (hagree : ∀ i j, i < m → j < n → (i, j) ≠ (m - 1, n - 1) →
          cell grid' i j = cell grid i j)
        (h : Aegis.MinCost.min_cost grid = ok r)
        (h' : Aegis.MinCost.min_cost grid' = ok r'), r = r') := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r = |{ j | 0 <= j < n-1 and grid[0][j] != 1 }|.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m = 1, n >= 1, n <= 100, len(grid[0]) = n, and grid[0][j] is in {1,2,3,4} for every 0 <= j < n. -/
  theorem spec_8 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hgrid : ValidGrid grid m n) (hm : m = 1) (h : Aegis.MinCost.min_cost grid = ok r) :
      r.val = (countNotEq (n - 1) (fun j => cell grid 0 j) 1 : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hgrid : ValidGrid grid m n) (hm : m = 1) (h : Aegis.MinCost.min_cost grid = ok r), r.val = (countNotEq (n - 1) (fun j => cell grid 0 j) 1 : Int)) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r = |{ i | 0 <= i < m-1 and grid[i][0] != 3 }|.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n = 1, m <= 100, len(grid[i]) = 1 for every 0 <= i < m, and grid[i][0] is in {1,2,3,4} for every 0 <= i < m. -/
  theorem spec_9 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hgrid : ValidGrid grid m n) (hn : n = 1) (h : Aegis.MinCost.min_cost grid = ok r) :
      r.val = (countNotEq (m - 1) (fun i => cell grid i 0) 3 : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hgrid : ValidGrid grid m n) (hn : n = 1) (h : Aegis.MinCost.min_cost grid = ok r), r.val = (countNotEq (m - 1) (fun i => cell grid i 0) 3 : Int)) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r = m - 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] = 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hshape : ValidShape grid m n)
      (hconst : ∀ i j, i < m → j < n → cell grid i j = some 1)
      (h : Aegis.MinCost.min_cost grid = ok r) :
      r.val = (m : Int) - 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hshape : ValidShape grid m n)
        (hconst : ∀ i j, i < m → j < n → cell grid i j = some 1)
        (h : Aegis.MinCost.min_cost grid = ok r), r.val = (m : Int) - 1) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r = n - 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] = 3 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hshape : ValidShape grid m n)
      (hconst : ∀ i j, i < m → j < n → cell grid i j = some 3)
      (h : Aegis.MinCost.min_cost grid = ok r) :
      r.val = (n : Int) - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hshape : ValidShape grid m n)
        (hconst : ∀ i j, i < m → j < n → cell grid i j = some 3)
        (h : Aegis.MinCost.min_cost grid = ok r), r.val = (n : Int) - 1) := by
    sorry

  /-- Whenever min_cost(grid) returns a result r, r = m + n - 2.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] = 2 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (grid : Grid) (m n : Nat) (r : Std.I64)
      (hshape : ValidShape grid m n)
      (hconst : ∀ i j, i < m → j < n → cell grid i j = some 2)
      (h : Aegis.MinCost.min_cost grid = ok r) :
      r.val = (m : Int) + (n : Int) - 2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (r : Std.I64)
        (hshape : ValidShape grid m n)
        (hconst : ∀ i j, i < m → j < n → cell grid i j = some 2)
        (h : Aegis.MinCost.min_cost grid = ok r), r.val = (m : Int) + (n : Int) - 2) := by
    sorry

  end AegisSpec.MinCost
