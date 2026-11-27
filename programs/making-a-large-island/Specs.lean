import Aegis.LargestIsland.Code.Funs

/-!
# Specifications of `Aegis.LargestIsland.largest_island`

LeetCode problem `making-a-large-island`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LargestIsland

  def matOf (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map (fun r => r.val.map (fun x => x.val))

  def cells (n : Nat) : Finset (Nat × Nat) := (Finset.range n).product (Finset.range n)

  def row (M : List (List Int)) (i : Nat) : List Int := M.getD i []

  def entry (M : List (List Int)) (i j : Nat) : Int := (row M i).getD j 0

  def Orth (p q : Nat × Nat) : Prop :=
    (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨ (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨
      (p.1 = q.1 ∧ p.2 + 1 = q.2) ∨ (p.1 = q.1 ∧ q.2 + 1 = p.2)

  def IsConnectedCellSet (C : Finset (Nat × Nat)) : Prop :=
    C.Nonempty ∧
      ∀ p ∈ C, ∀ q ∈ C, Relation.ReflTransGen (fun a b => Orth a b ∧ a ∈ C ∧ b ∈ C) p q

  def IsIsland (M : List (List Int)) (n : Nat) (C : Finset (Nat × Nat)) : Prop :=
    C ⊆ cells n ∧ (∀ p ∈ C, entry M p.1 p.2 = 1) ∧ IsConnectedCellSet C ∧
      ∀ D, D ⊆ cells n → C ⊆ D → (∀ p ∈ D, entry M p.1 p.2 = 1) → IsConnectedCellSet D → D = C

  noncomputable def islands (M : List (List Int)) (n : Nat) : Finset (Finset (Nat × Nat)) :=
    by classical exact ((cells n).powerset).filter (fun C => IsIsland M n C)

  noncomputable def islandSize (M : List (List Int)) (n : Nat) : Nat :=
    (islands M n).sup (fun C => C.card)

  def flip (M : List (List Int)) (i j : Nat) : List (List Int) :=
    M.set i ((row M i).set j 1)

  def IsAllowedMod (M M' : List (List Int)) (n : Nat) : Prop :=
    M' = M ∨ ∃ i j, i < n ∧ j < n ∧ entry M i j = 0 ∧ M' = flip M i j

  noncomputable def bestIslandSize (M : List (List Int)) (n : Nat) : Nat :=
    max (islandSize M n) ((cells n).sup (fun p => islandSize (flip M p.1 p.2) n))

  noncomputable def adjacentIslands (M : List (List Int)) (n : Nat) (z : Nat × Nat) :
      Finset (Finset (Nat × Nat)) :=
    by classical exact (islands M n).filter (fun C => ∃ p ∈ C, Orth z p)

  noncomputable def zeroCellBest (M : List (List Int)) (n : Nat) : Nat :=
    (((cells n).filter (fun z => entry M z.1 z.2 = 0)).sup
      (fun z => 1 + (adjacentIslands M n z).sum (fun C => C.card)))

  def ValidInput (M : List (List Int)) (n : Nat) : Prop :=
    1 ≤ n ∧ n ≤ 500 ∧ M.length = n ∧ (∀ i, i < n → (row M i).length = n) ∧
      ∀ i j, i < n → j < n → entry M i j = 0 ∨ entry M i j = 1

  /-- An allowed modification of grid is either grid itself or a matrix M obtained by choosing exactly one index (i,j) with grid[i][j] = 0 and setting M[i][j] = 1 while leaving every other entry equal to grid. For any such M, let L(M) be 0 if M has no cell equal to 1, and otherwise the maximum size of a maximal set of cells with M = 1 that is connected by moves up, down, left, or right, where size is the number of cells. Whenever largest_island(grid) returns a result r, r = max { L(M) : M is an allowed modification of grid }.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        r.val = ((bestIslandSize (matOf grid) n : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          r.val = ((bestIslandSize (matOf grid) n : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, largest_island(grid) returns a result r; it does not fail, overflow, access out of bounds, or panic.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∃ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∃ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r) := by
    sorry

  /-- Whenever largest_island(grid) returns a result r, 1 <= r.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever largest_island(grid) returns a result r, r <= n*n.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        r.val ≤ ((n * n : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          r.val ≤ ((n * n : Nat) : Int)) := by
    sorry

  /-- Whenever largest_island(grid) returns a result r, r = 1.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. Also n = 1. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) (h1 : n = 1) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n) (h1 : n = 1), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → r.val = 1) := by
    sorry

  /-- Whenever largest_island(grid) returns a result r, r = n*n.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. Also grid[i][j] = 1 for every i,j with 0 <= i < n and 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n)
      (hall : ∀ i j, i < n → j < n → entry (matOf grid) i j = 1) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        r.val = ((n * n : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n)
        (hall : ∀ i j, i < n → j < n → entry (matOf grid) i j = 1), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          r.val = ((n * n : Nat) : Int)) := by
    sorry

  /-- An original island is a maximal nonempty set C of cells such that grid[i][j] = 1 for all (i,j) in C and any two cells of C can be joined by a path in C moving only up, down, left, or right. Whenever largest_island(grid) returns a result r, for every original island C, r >= |C|, where |C| is the number of cells in C.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        ∀ C : Finset (Nat × Nat), IsIsland (matOf grid) n C → ((C.card : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          ∀ C : Finset (Nat × Nat), IsIsland (matOf grid) n C → ((C.card : Nat) : Int) ≤ r.val) := by
    sorry

  /-- An original island is a maximal nonempty set C of cells such that grid[i][j] = 1 for all (i,j) in C and any two cells of C can be joined by a path in C moving only up, down, left, or right. For a zero cell z = (i,j) with grid[i][j] = 0, let Adj(z) be the set of distinct original islands that contain at least one cell orthogonally adjacent to z. Whenever largest_island(grid) returns a result r, for every zero cell z, r >= 1 + sum over C in Adj(z) of |C|.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        ∀ z, z ∈ cells n → entry (matOf grid) z.1 z.2 = 0 →
          (((adjacentIslands (matOf grid) n z).sum (fun C => (C.card : Nat)) : Nat) : Int) + 1 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          ∀ z, z ∈ cells n → entry (matOf grid) z.1 z.2 = 0 →
            (((adjacentIslands (matOf grid) n z).sum (fun C => (C.card : Nat)) : Nat) : Int) + 1 ≤ r.val) := by
    sorry

  /-- Call M an allowed modification of grid if M is either grid itself or obtained by changing exactly one 0-cell of grid to 1. Whenever largest_island(grid) returns a result r, there exist an allowed modification M and a maximal set C of cells with M = 1, connected by moves up, down, left, or right, such that |C| = r.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        ∃ (M : List (List Int)) (C : Finset (Nat × Nat)),
          IsAllowedMod (matOf grid) M n ∧ IsIsland M n C ∧ ((C.card : Nat) : Int) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          ∃ (M : List (List Int)) (C : Finset (Nat × Nat)),
            IsAllowedMod (matOf grid) M n ∧ IsIsland M n C ∧ ((C.card : Nat) : Int) = r.val) := by
    sorry

  /-- Call M an allowed modification of grid if M is either grid itself or obtained by changing exactly one 0-cell of grid to 1. Whenever largest_island(grid) returns a result r, for every allowed modification M and every maximal set C of cells with M = 1 connected by moves up, down, left, or right, |C| <= r.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        ∀ (M : List (List Int)) (C : Finset (Nat × Nat)),
          IsAllowedMod (matOf grid) M n → IsIsland M n C → ((C.card : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          ∀ (M : List (List Int)) (C : Finset (Nat × Nat)),
            IsAllowedMod (matOf grid) M n → IsIsland M n C → ((C.card : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever largest_island(A) returns a result rA and largest_island(B) returns a result rB, rA <= rB.
    Preconditions: Let n = len(A). Both A and B are n x n binary matrices satisfying the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(A[i]) = len(B[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, A[i][j] and B[i][j] are each either 0 or 1; and A[i][j] <= B[i][j] for every i,j with 0 <= i < n and 0 <= j < n. -/
  theorem spec_11 (A B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = A.val.length)
      (hnB : B.val.length = n)
      (hA : ValidInput (matOf A) n) (hB : ValidInput (matOf B) n)
      (hle : ∀ i j, i < n → j < n → entry (matOf A) i j ≤ entry (matOf B) i j) :
      ∀ rA rB : Std.I64, Aegis.LargestIsland.largest_island A = ok rA →
        Aegis.LargestIsland.largest_island B = ok rB → rA.val ≤ rB.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = A.val.length)
        (hnB : B.val.length = n)
        (hA : ValidInput (matOf A) n) (hB : ValidInput (matOf B) n)
        (hle : ∀ i j, i < n → j < n → entry (matOf A) i j ≤ entry (matOf B) i j), ∀ rA rB : Std.I64, Aegis.LargestIsland.largest_island A = ok rA →
          Aegis.LargestIsland.largest_island B = ok rB → rA.val ≤ rB.val) := by
    sorry

  /-- Let G^T be the n x n matrix with G^T[i][j] = grid[j][i] for all 0 <= i,j < n. Whenever largest_island(grid) returns a result r and largest_island(G^T) returns a result rT, r = rT.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_12 (grid T : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length) (hnT : n = T.val.length)
      (hv : ValidInput (matOf grid) n) (hvT : ValidInput (matOf T) n)
      (htrans : ∀ i j, i < n → j < n → entry (matOf T) i j = entry (matOf grid) j i) :
      ∀ r rT : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        Aegis.LargestIsland.largest_island T = ok rT → r.val = rT.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid T : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length) (hnT : n = T.val.length)
        (hv : ValidInput (matOf grid) n) (hvT : ValidInput (matOf T) n)
        (htrans : ∀ i j, i < n → j < n → entry (matOf T) i j = entry (matOf grid) j i), ∀ r rT : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          Aegis.LargestIsland.largest_island T = ok rT → r.val = rT.val) := by
    sorry

  /-- Let G' be the n x n matrix with G'[i][j] = grid[n-1-i][n-1-j] for all 0 <= i,j < n. Whenever largest_island(grid) returns a result r and largest_island(G') returns a result r', r = r'.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_13 (grid G' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = grid.val.length) (hnG : n = G'.val.length)
      (hv : ValidInput (matOf grid) n) (hvG : ValidInput (matOf G') n)
      (hrot : ∀ i j, i < n → j < n →
        entry (matOf G') i j = entry (matOf grid) (n - 1 - i) (n - 1 - j)) :
      ∀ r r' : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        Aegis.LargestIsland.largest_island G' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid G' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = grid.val.length) (hnG : n = G'.val.length)
        (hv : ValidInput (matOf grid) n) (hvG : ValidInput (matOf G') n)
        (hrot : ∀ i j, i < n → j < n →
          entry (matOf G') i j = entry (matOf grid) (n - 1 - i) (n - 1 - j)), ∀ r r' : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          Aegis.LargestIsland.largest_island G' = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever largest_island(grid) returns a result r, r = 2.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. Also n >= 2, and there is exactly one pair (i,j) with grid[i][j] = 1; every other entry is 0. -/
  theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) (hn2 : 2 ≤ n)
      (huniq : ∃ i j, i < n ∧ j < n ∧ entry (matOf grid) i j = 1 ∧
        ∀ a b, a < n → b < n → entry (matOf grid) a b = 1 → a = i ∧ b = j) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → r.val = 2 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n) (hn2 : 2 ≤ n)
        (huniq : ∃ i j, i < n ∧ j < n ∧ entry (matOf grid) i j = 1 ∧
          ∀ a b, a < n → b < n → entry (matOf grid) a b = 1 → a = i ∧ b = j), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → r.val = 2) := by
    sorry

  /-- Whenever largest_island(grid) returns a result r, r >= 2.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. Also n >= 2, and there exists at least one cell with value 1 and at least one cell with value 0. -/
  theorem spec_15 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) (hn2 : 2 ≤ n)
      (h1 : ∃ i j, i < n ∧ j < n ∧ entry (matOf grid) i j = 1)
      (h0 : ∃ i j, i < n ∧ j < n ∧ entry (matOf grid) i j = 0) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → 2 ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n) (hn2 : 2 ≤ n)
        (h1 : ∃ i j, i < n ∧ j < n ∧ entry (matOf grid) i j = 1)
        (h0 : ∃ i j, i < n ∧ j < n ∧ entry (matOf grid) i j = 0), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r → 2 ≤ r.val) := by
    sorry

  /-- Let an original island be a maximal nonempty 4-connected set of 1-cells of grid, and for a zero cell z let Adj(z) be the set of distinct original islands containing a cell orthogonally adjacent to z. If grid has at least one 0, then whenever largest_island(grid) returns r, r = max( max { |C| : C is an original island } (taking this maximum as 0 when there are no original islands), max { 1 + sum over C in Adj(z) of |C| : z is a zero cell } ). If grid has no 0, then r = n*n.
    Preconditions: Let n = len(grid). The input satisfies the problem constraints: 1 <= n <= 500; for every i with 0 <= i < n, len(grid[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_16 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
      (hv : ValidInput (matOf grid) n) :
      ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
        (((∃ z, z ∈ cells n ∧ entry (matOf grid) z.1 z.2 = 0) →
            r.val = ((max (islandSize (matOf grid) n) (zeroCellBest (matOf grid) n) : Nat) : Int)) ∧
          (∀ z, z ∈ cells n → entry (matOf grid) z.1 z.2 ≠ 0 →
            r.val = ((n * n : Nat) : Int))) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hn : n = grid.val.length)
        (hv : ValidInput (matOf grid) n), ∀ r : Std.I64, Aegis.LargestIsland.largest_island grid = ok r →
          (((∃ z, z ∈ cells n ∧ entry (matOf grid) z.1 z.2 = 0) →
              r.val = ((max (islandSize (matOf grid) n) (zeroCellBest (matOf grid) n) : Nat) : Int)) ∧
            (∀ z, z ∈ cells n → entry (matOf grid) z.1 z.2 ≠ 0 →
              r.val = ((n * n : Nat) : Int)))) := by
    sorry

  end AegisSpec.LargestIsland
