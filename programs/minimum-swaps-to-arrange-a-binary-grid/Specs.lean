import Aegis.MinSwaps.Code.Funs

/-!
# Specifications of `Aegis.MinSwaps.min_swaps`

LeetCode problem `minimum-swaps-to-arrange-a-binary-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinSwaps

  namespace AegisSpec.MinSwaps

  def rows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map (fun row => row.val.map (fun x => x.val))

  def gsize (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := (rows grid).length

  def cellAt (R : List (List Int)) (i j : Nat) : Int := (R.getD i []).getD j 0

  def tailOfRow (row : List Int) : Int :=
    (List.range row.length).foldl
      (fun acc j => if row.getD j 0 = 1 then (j : Int) else acc) (-1)

  def tailAt (R : List (List Int)) (i : Nat) : Int := tailOfRow (R.getD i [])

  def tails (R : List (List Int)) : List Int := R.map tailOfRow

  def sortedTails (R : List (List Int)) : List Int :=
    List.insertionSort (fun a b : Int => a ≤ b) (tails R)

  def countTailAbove (R : List (List Int)) (n : Nat) : Nat :=
    ((List.range n).filter (fun i => decide (tailAt R i > (i : Int)))).length

  def IsPerm (n : Nat) (p : Nat → Nat) : Prop :=
    (∀ k, k < n → p k < n) ∧ (∀ k, k < n → ∃ a, a < n ∧ p a = k)

  def inv (n : Nat) (p : Nat → Nat) : Nat :=
    (((List.range n).product (List.range n)).filter
        (fun ab => ab.1 < ab.2 && decide (p ab.2 < p ab.1))).length

  def Admissible (R : List (List Int)) (n : Nat) (p : Nat → Nat) : Prop :=
    IsPerm n p ∧ ∀ k, k < n → tailAt R (p k) ≤ (k : Int)

  def IsValidGrid (R : List (List Int)) (n : Nat) : Prop :=
    ∀ i j, i < n → i < j → j < n → cellAt R i j = 0

  def swapAdj (R : List (List Int)) (i : Nat) : List (List Int) :=
    (R.set i (R.getD (i + 1) [])).set (i + 1) (R.getD i [])

  inductive SwapSteps : Nat → List (List Int) → List (List Int) → Prop where
    | zero (R : List (List Int)) : SwapSteps 0 R R
    | succ {k : Nat} {R R' : List (List Int)} (i : Nat) (hi : i + 1 < R.length) :
        SwapSteps k (swapAdj R i) R' → SwapSteps (k + 1) R R'

  def MinAdjacentSwaps (R : List (List Int)) (n : Nat) (r : Int) : Prop :=
    (∃ k : Nat, (k : Int) = r ∧ ∃ R', SwapSteps k R R' ∧ IsValidGrid R' n ∧
        ∀ k' : Nat, (k' : Int) < r → ∀ R'', SwapSteps k' R R'' → ¬ IsValidGrid R'' n) ∨
      (r = -1 ∧ ∀ k : Nat, ∀ R', SwapSteps k R R' → ¬ IsValidGrid R' n)

  def WF (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    n = gsize grid ∧ 1 ≤ n ∧ n ≤ 200 ∧
      (∀ row ∈ rows grid, row.length = n) ∧
      (∀ row ∈ rows grid, ∀ x ∈ row, x = 0 ∨ x = 1)

  /-- Define tail(i), for 0 <= i < n, as the largest j with 0 <= j < n and grid[i][j] = 1, or -1 if no such j exists. Call a permutation p of {0,...,n-1} admissible if tail(p[k]) <= k for every 0 <= k < n, and let inv(p) be the number of pairs (a,b) with 0 <= a < b < n and p[a] > p[b]. The function returns a result r and either (i) there exists an admissible permutation and r is the minimum of inv(p) over all admissible permutations p, or (ii) no admissible permutation exists and r = -1. This r is exactly the minimum number of adjacent row swaps needed to make all cells above the main diagonal zero, or -1 if that is impossible.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∃ r : Std.I64, min_swaps grid = ok r ∧
        ((∃ p : Nat → Nat,
            Admissible (rows grid) n p ∧ (inv n p : Int) = r.val ∧
              ∀ q : Nat → Nat, Admissible (rows grid) n q → r.val ≤ (inv n q : Int)) ∨
          ((∀ p : Nat → Nat, ¬ Admissible (rows grid) n p) ∧ r.val = -1)) ∧
        MinAdjacentSwaps (rows grid) n r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∃ r : Std.I64, min_swaps grid = ok r ∧
          ((∃ p : Nat → Nat,
              Admissible (rows grid) n p ∧ (inv n p : Int) = r.val ∧
                ∀ q : Nat → Nat, Admissible (rows grid) n q → r.val ≤ (inv n q : Int)) ∨
            ((∀ p : Nat → Nat, ¬ Admissible (rows grid) n p) ∧ r.val = -1)) ∧
          MinAdjacentSwaps (rows grid) n r.val) := by
    sorry

  /-- The function returns a result r: it does not panic, fail an array-bound check, or overflow on any input satisfying the preconditions.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∃ r : Std.I64, min_swaps grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∃ r : Std.I64, min_swaps grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, -1 <= r <= n*(n-1)/2.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∀ r : Std.I64, min_swaps grid = ok r →
        -1 ≤ r.val ∧ r.val ≤ ((n * (n - 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∀ r : Std.I64, min_swaps grid = ok r →
          -1 ≤ r.val ∧ r.val ≤ ((n * (n - 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Define tail(i) as the largest j with grid[i][j] = 1, or -1 if no such j exists. Whenever the function returns a result r, r = -1 if and only if there is no permutation p of {0,...,n-1} such that tail(p[k]) <= k for every 0 <= k < n.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∀ r : Std.I64, min_swaps grid = ok r →
        (r.val = -1 ↔ ∀ p : Nat → Nat, ¬ Admissible (rows grid) n p) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∀ r : Std.I64, min_swaps grid = ok r →
          (r.val = -1 ↔ ∀ p : Nat → Nat, ¬ Admissible (rows grid) n p)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if the input grid is already valid, that is, grid[i][j] = 0 for every 0 <= i < j < n.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∀ r : Std.I64, min_swaps grid = ok r → (r.val = 0 ↔ IsValidGrid (rows grid) n) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∀ r : Std.I64, min_swaps grid = ok r → (r.val = 0 ↔ IsValidGrid (rows grid) n)) := by
    sorry

  /-- Define tail(i) as the largest j with grid[i][j] = 1, or -1 if no such j exists, and define inv(p) for a permutation p of {0,...,n-1} as the number of pairs (a,b) with 0 <= a < b < n and p[a] > p[b]. Whenever the function returns a result r with r >= 0, there exists a permutation p of {0,...,n-1} such that tail(p[k]) <= k for every 0 <= k < n and inv(p) = r.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∀ r : Std.I64, min_swaps grid = ok r → 0 ≤ r.val →
        ∃ p : Nat → Nat, Admissible (rows grid) n p ∧ (inv n p : Int) = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∀ r : Std.I64, min_swaps grid = ok r → 0 ≤ r.val →
          ∃ p : Nat → Nat, Admissible (rows grid) n p ∧ (inv n p : Int) = r.val) := by
    sorry

  /-- Define tail(i) as the largest j with grid[i][j] = 1, or -1 if no such j exists, and define inv(p) for a permutation p of {0,...,n-1} as the number of pairs (a,b) with 0 <= a < b < n and p[a] > p[b]. Whenever the function returns a result r with r >= 0, every permutation p of {0,...,n-1} satisfying tail(p[k]) <= k for all 0 <= k < n also satisfies inv(p) >= r.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∀ r : Std.I64, min_swaps grid = ok r → 0 ≤ r.val →
        ∀ p : Nat → Nat, Admissible (rows grid) n p → r.val ≤ (inv n p : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∀ r : Std.I64, min_swaps grid = ok r → 0 ≤ r.val →
          ∀ p : Nat → Nat, Admissible (rows grid) n p → r.val ≤ (inv n p : Int)) := by
    sorry

  /-- Define tail(i) as the largest j with grid[i][j] = 1, or -1 if no such j exists, and let t_0 <= t_1 <= ... <= t_{n-1} be the values tail(i) sorted in nondecreasing order. Whenever the function returns a result r, r = -1 if and only if there exists k with 0 <= k < n and t_k > k.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∀ r : Std.I64, min_swaps grid = ok r →
        (r.val = -1 ↔ ∃ k, k < n ∧ (sortedTails (rows grid)).getD k 0 > (k : Int)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∀ r : Std.I64, min_swaps grid = ok r →
          (r.val = -1 ↔ ∃ k, k < n ∧ (sortedTails (rows grid)).getD k 0 > (k : Int))) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(grid) = 1; grid[0] has length 1; grid[0][0] is either 0 or 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (hwf : WF grid 1) :
      ∃ r : Std.I64, min_swaps grid = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hwf : WF grid 1), ∃ r : Std.I64, min_swaps grid = ok r ∧ r.val = 0) := by
    sorry

  /-- Let a = grid[0][1] and b = grid[1][1]. The function returns a result r and: if a = 0 then r = 0; if a = 1 and b = 0 then r = 1; if a = 1 and b = 1 then r = -1.
    Preconditions: len(grid) = 2; every row grid[i] has length 2; and every grid[i][j] is either 0 or 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (hwf : WF grid 2) :
      let a := cellAt (rows grid) 0 1
      let b := cellAt (rows grid) 1 1
      ∃ r : Std.I64, min_swaps grid = ok r ∧
        (a = 0 → r.val = 0) ∧ (a = 1 → b = 0 → r.val = 1) ∧
          (a = 1 → b = 1 → r.val = -1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hwf : WF grid 2), let a := cellAt (rows grid) 0 1
        let b := cellAt (rows grid) 1 1
        ∃ r : Std.I64, min_swaps grid = ok r ∧
          (a = 0 → r.val = 0) ∧ (a = 1 → b = 0 → r.val = 1) ∧
            (a = 1 → b = 1 → r.val = -1)) := by
    sorry

  /-- The function returns a result r and r = -1.
    Preconditions: Let n = len(grid). n >= 2 and n <= 200; every row grid[i] has length n; every grid[i][j] is either 0 or 1; and there exist distinct row indices i,j with grid[i][n-1] = 1 and grid[j][n-1] = 1. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n)
      (hn : 2 ≤ n)
      (htwo : ∃ i j, i < n ∧ j < n ∧ i ≠ j ∧
        cellAt (rows grid) i (n - 1) = 1 ∧ cellAt (rows grid) j (n - 1) = 1) :
      ∃ r : Std.I64, min_swaps grid = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n)
        (hn : 2 ≤ n)
        (htwo : ∃ i j, i < n ∧ j < n ∧ i ≠ j ∧
          cellAt (rows grid) i (n - 1) = 1 ∧ cellAt (rows grid) j (n - 1) = 1), ∃ r : Std.I64, min_swaps grid = ok r ∧ r.val = -1) := by
    sorry

  /-- Whenever the function returns r on grid and rH on H, r = rH.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; every grid[i][j] is either 0 or 1. Let H be any grid satisfying the same size and binary conditions with the same n, and such that for every 0 <= i < n, the largest j with H[i][j] = 1, or -1 if none, equals the largest j with grid[i][j] = 1, or -1 if none. -/
  theorem spec_12 (grid H : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n)
      (hH : WF H n) (htails : ∀ i, i < n → tailAt (rows H) i = tailAt (rows grid) i) :
      ∀ r rH : Std.I64, min_swaps grid = ok r → min_swaps H = ok rH → r.val = rH.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid H : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n)
        (hH : WF H n) (htails : ∀ i, i < n → tailAt (rows H) i = tailAt (rows grid) i), ∀ r rH : Std.I64, min_swaps grid = ok r → min_swaps H = ok rH → r.val = rH.val) := by
    sorry

  /-- Define tail(i) as the largest j with grid[i][j] = 1, or -1 if no such j exists. Whenever the function returns a result r with r >= 0, r is at least the number of indices i with 0 <= i < n and tail(i) > i.
    Preconditions: Let n = len(grid). n >= 1 and n <= 200; every row grid[i] has length n; and for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n) :
      ∀ r : Std.I64, min_swaps grid = ok r → 0 ≤ r.val →
        (countTailAbove (rows grid) n : Int) ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hwf : WF grid n), ∀ r : Std.I64, min_swaps grid = ok r → 0 ≤ r.val →
          (countTailAbove (rows grid) n : Int) ≤ r.val) := by
    sorry

  end AegisSpec.MinSwaps
