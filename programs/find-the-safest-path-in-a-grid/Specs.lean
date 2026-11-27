import Aegis.MaximumSafenessFactor.Code.Funs

/-!
# Specifications of `Aegis.MaximumSafenessFactor.maximum_safeness_factor`

LeetCode problem `find-the-safest-path-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.MaximumSafenessFactor

  open Aegis.MaximumSafenessFactor

  def i64Cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Std.I64 :=
    ((grid.val[i]?).bind (fun r => r.val[j]?)).getD (0#i64)

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (i64Cell grid i j).val

  def manhattan (i j a b : Nat) : Nat :=
    Int.natAbs ((i : Int) - (a : Int)) + Int.natAbs ((j : Int) - (b : Int))

  def oneCells (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : List (Nat × Nat) :=
    ((List.range n).product (List.range n)).filter
      (fun p => cell grid p.1 p.2 == 1)

  def d (grid : Slice (alloc.vec.Vec Std.I64)) (n i j : Nat) : Nat :=
    ((oneCells grid n).map (fun p => manhattan i j p.1 p.2)).min?.getD 0

  def IsAdjacent (p q : Nat × Nat) : Prop :=
    manhattan p.1 p.2 q.1 q.2 = 1

  def IsPath (n : Nat) (P : List (Nat × Nat)) : Prop :=
    P ≠ [] ∧
    P.head? = some (0, 0) ∧
    P.getLast? = some (n - 1, n - 1) ∧
    (∀ p ∈ P, p.1 < n ∧ p.2 < n) ∧
    P.Nodup ∧
    (∀ (t : Nat) (p q : Nat × Nat),
      P[t]? = some p → P[t + 1]? = some q → IsAdjacent p q)

  def safe (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (P : List (Nat × Nat)) : Nat :=
    (P.map (fun p => d grid n p.1 p.2)).min?.getD 0

  def vecOfI64s (l : List Std.I64) (h : l.length ≤ Usize.max) :
      alloc.vec.Vec Std.I64 :=
    ⟨⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩⟩

  def transposedRows (grid : Slice (alloc.vec.Vec Std.I64)) :
      List (alloc.vec.Vec Std.I64) :=
    List.ofFn (fun (i : Fin grid.leng) =>
      vecOfI64s (List.ofFn (fun (j : Fin grid.leng) => i64Cell grid j.1 i.1))
        (by simpa using grid.bound))

  def transpose (grid : Slice (alloc.vec.Vec Std.I64)) :
      Slice (alloc.vec.Vec Std.I64) :=
    ⟨(transposedRows grid).length,
      Aeneas.Data.ListN.ListN.fromList (transposedRows grid),
      by simpa [transposedRows] using grid.bound⟩

  def rotatedRows (grid : Slice (alloc.vec.Vec Std.I64)) :
      List (alloc.vec.Vec Std.I64) :=
    List.ofFn (fun (i : Fin grid.leng) =>
      vecOfI64s
        (List.ofFn (fun (j : Fin grid.leng) =>
          i64Cell grid (grid.leng - 1 - j.1) (grid.leng - 1 - i.1)))
        (by simpa using grid.bound))

  def rot180 (grid : Slice (alloc.vec.Vec Std.I64)) :
      Slice (alloc.vec.Vec Std.I64) :=
    ⟨(rotatedRows grid).length,
      Aeneas.Data.ListN.ListN.fromList (rotatedRows grid),
      by simpa [rotatedRows] using grid.bound⟩

  /-- The function returns a result r and r = max { safe(P) : P is a path from (0,0) to (n-1,n-1) }. Here d(i,j) = min { |i-a| + |j-b| : 0 <= a,b < n and grid[a][b] = 1 } for every cell (i,j) in the grid. A path P is a finite sequence of cells p_0,...,p_k with k >= 0, p_0 = (0,0), p_k = (n-1,n-1), every p_t in the grid, no cell repeated in the sequence, and p_{t+1} adjacent to p_t (that is, |r_{t+1}-r_t| + |c_{t+1}-c_t| = 1) for every 0 <= t < k. safe(P) = min { d(p_t) : 0 <= t <= k }. Equivalently, r is the largest integer s >= 0 for which there exists a path from (0,0) to (n-1,n-1) such that d(q) >= s for every cell q on the path.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64,
        maximum_safeness_factor grid = ok r ∧
          IsGreatest
            {s : Int | 0 ≤ s ∧ ∃ P : List (Nat × Nat), IsPath n P ∧
              ∀ q ∈ P, s ≤ (d grid n q.1 q.2 : Int)}
            r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64,
          maximum_safeness_factor grid = ok r ∧
            IsGreatest
              {s : Int | 0 ≤ s ∧ ∃ P : List (Nat × Nat), IsPath n P ∧
                ∀ q ∈ P, s ≤ (d grid n q.1 q.2 : Int)}
              r.val) := by
    sorry

  /-- The function returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64, maximum_safeness_factor grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64, maximum_safeness_factor grid = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= n - 1.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ r.val ≤ (n : Int) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ r.val ≤ (n : Int) - 1) := by
    sorry

  /-- Let d(i,j) = min { |i-a| + |j-b| : 0 <= a,b < n and grid[a][b] = 1 }. The function returns a result r and r <= d(0,0).
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ r.val ≤ (d grid n 0 0 : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ r.val ≤ (d grid n 0 0 : Int)) := by
    sorry

  /-- Let d(i,j) = min { |i-a| + |j-b| : 0 <= a,b < n and grid[a][b] = 1 }. The function returns a result r and r <= d(n-1,n-1).
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64,
        maximum_safeness_factor grid = ok r ∧ r.val ≤ (d grid n (n - 1) (n - 1) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64,
          maximum_safeness_factor grid = ok r ∧ r.val ≤ (d grid n (n - 1) (n - 1) : Int)) := by
    sorry

  /-- With d(i,j) = min { |i-a| + |j-b| : 0 <= a,b < n and grid[a][b] = 1 } and paths defined as finite sequences p_0,...,p_k with p_0=(0,0), p_k=(n-1,n-1), all cells in the grid, no repeated cell, consecutive cells adjacent by Manhattan distance 1, and safe(P) = min { d(p_t) : 0 <= t <= k }, the function returns a result r and there exists a path P from (0,0) to (n-1,n-1) such that safe(P) = r.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64,
        maximum_safeness_factor grid = ok r ∧
          ∃ P : List (Nat × Nat), IsPath n P ∧ (safe grid n P : Int) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64,
          maximum_safeness_factor grid = ok r ∧
            ∃ P : List (Nat × Nat), IsPath n P ∧ (safe grid n P : Int) = r.val) := by
    sorry

  /-- With the same definitions of d and paths as in the main specification, the function returns a result r and for every path P from (0,0) to (n-1,n-1), safe(P) <= r.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64,
        maximum_safeness_factor grid = ok r ∧
          ∀ P : List (Nat × Nat), IsPath n P → (safe grid n P : Int) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64,
          maximum_safeness_factor grid = ok r ∧
            ∀ P : List (Nat × Nat), IsPath n P → (safe grid n P : Int) ≤ r.val) := by
    sorry

  /-- Let d(i,j) = min { |i-a| + |j-b| : 0 <= a,b < n and grid[a][b] = 1 }. The function returns a result r and for every integer s, s <= r if and only if there exists a path P from (0,0) to (n-1,n-1) (a finite sequence of cells with p_0=(0,0), p_k=(n-1,n-1), all cells in the grid, no repeated cell, and consecutive cells adjacent by Manhattan distance 1) such that d(q) >= s for every cell q occurring in P.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r : Std.I64,
        maximum_safeness_factor grid = ok r ∧
          ∀ s : Int,
            (s ≤ r.val ↔
              ∃ P : List (Nat × Nat), IsPath n P ∧
                ∀ q ∈ P, s ≤ (d grid n q.1 q.2 : Int)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r : Std.I64,
          maximum_safeness_factor grid = ok r ∧
            ∀ s : Int,
              (s ≤ r.val ↔
                ∃ P : List (Nat × Nat), IsPath n P ∧
                  ∀ q ∈ P, s ≤ (d grid n q.1 q.2 : Int))) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1, and grid[0][0] = 1 or grid[n-1][n-1] = 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1)
      (hcorner : cell grid 0 0 = 1 ∨ cell grid (n - 1) (n - 1) = 1) :
      ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1)
        (hcorner : cell grid 0 0 = 1 ∨ cell grid (n - 1) (n - 1) = 1), ∃ r : Std.I64, maximum_safeness_factor grid = ok r ∧ r.val = 0) := by
    sorry

  /-- Let grid^T be the n by n grid with grid^T[i][j] = grid[j][i] for 0 <= i,j < n. Let r be the result returned by maximum_safeness_factor(grid) and let r^T be the result returned by maximum_safeness_factor(grid^T). Then both calls return results and r = r^T.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r rT : Std.I64,
        maximum_safeness_factor grid = ok r ∧
          maximum_safeness_factor (transpose grid) = ok rT ∧ r.val = rT.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r rT : Std.I64,
          maximum_safeness_factor grid = ok r ∧
            maximum_safeness_factor (transpose grid) = ok rT ∧ r.val = rT.val) := by
    sorry

  /-- Let grid^R be the n by n grid with grid^R[i][j] = grid[n-1-j][n-1-i] for 0 <= i,j < n. Let r be the result returned by maximum_safeness_factor(grid) and let r^R be the result returned by maximum_safeness_factor(grid^R). Then both calls return results and r = r^R.
    Preconditions: Assume n = len(grid), 1 <= n <= 400, len(grid[i]) = n for every i with 0 <= i < n, grid[i][j] is 0 or 1 for every 0 <= i,j < n, and there exists at least one pair (a,b) with 0 <= a,b < n and grid[a][b] = 1. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1) :
      ∃ r rR : Std.I64,
        maximum_safeness_factor grid = ok r ∧
          maximum_safeness_factor (rot180 grid) = ok rR ∧ r.val = rR.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1), ∃ r rR : Std.I64,
          maximum_safeness_factor grid = ok r ∧
            maximum_safeness_factor (rot180 grid) = ok rR ∧ r.val = rR.val) := by
    sorry

  /-- Let r be the result returned by maximum_safeness_factor(grid) and let r2 be the result returned by maximum_safeness_factor(grid2). Then both calls return results and r2 <= r.
    Preconditions: Assume n = len(grid) = len(grid2), 1 <= n <= 400, len(grid[i]) = len(grid2[i]) = n for every 0 <= i < n, all entries of grid and grid2 are 0 or 1, grid contains at least one 1, and grid[i][j] <= grid2[i][j] for every 0 <= i,j < n. -/
  theorem spec_13 (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length)
      (hn2 : n = grid2.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
      (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
      (hrow2 : ∀ i : Nat, i < n → (grid2.val[i]?).map (fun r => r.val.length) = some n)
      (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hbin2 : ∀ i j : Nat, i < n → j < n → cell grid2 i j = 0 ∨ cell grid2 i j = 1)
      (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1)
      (hone2 : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid2 a b = 1)
      (hmono : ∀ i j : Nat, i < n → j < n → cell grid i j ≤ cell grid2 i j) :
      ∃ r r2 : Std.I64,
        maximum_safeness_factor grid = ok r ∧
          maximum_safeness_factor grid2 = ok r2 ∧ r2.val ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length)
        (hn2 : n = grid2.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 400)
        (hrow : ∀ i : Nat, i < n → (grid.val[i]?).map (fun r => r.val.length) = some n)
        (hrow2 : ∀ i : Nat, i < n → (grid2.val[i]?).map (fun r => r.val.length) = some n)
        (hbin : ∀ i j : Nat, i < n → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hbin2 : ∀ i j : Nat, i < n → j < n → cell grid2 i j = 0 ∨ cell grid2 i j = 1)
        (hone : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid a b = 1)
        (hone2 : ∃ a b : Nat, a < n ∧ b < n ∧ cell grid2 a b = 1)
        (hmono : ∀ i j : Nat, i < n → j < n → cell grid i j ≤ cell grid2 i j), ∃ r r2 : Std.I64,
          maximum_safeness_factor grid = ok r ∧
            maximum_safeness_factor grid2 = ok r2 ∧ r2.val ≤ r.val) := by
    sorry

  end AegisSpec.MaximumSafenessFactor
