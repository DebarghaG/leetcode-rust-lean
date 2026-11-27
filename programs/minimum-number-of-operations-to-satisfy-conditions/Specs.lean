import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-number-of-operations-to-satisfy-conditions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumOperations
  open scoped BigOperators

  namespace AegisSpec.MinimumOperations

  def rowsOf (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map fun row => row.val.map fun x => x.val

  def rowOf (rows : List (List Int)) (i : Nat) : List Int := rows.getD i []

  def cell (rows : List (List Int)) (i j : Nat) : Int := (rowOf rows i).getD j 0

  def Admissible (n : Nat) (v : Nat → Int) : Prop :=
    (∀ j, j < n → 0 ≤ v j) ∧ ∀ j, j + 1 < n → v j ≠ v (j + 1)

  def DigitAdmissible (n : Nat) (v : Nat → Int) : Prop :=
    (∀ j, j < n → 0 ≤ v j ∧ v j ≤ 9) ∧ ∀ j, j + 1 < n → v j ≠ v (j + 1)

  def colCost (rows : List (List Int)) (m j : Nat) (x : Int) : Nat :=
    ((Finset.range m).filter fun i => cell rows i j ≠ x).card

  def totalCost (rows : List (List Int)) (m n : Nat) (v : Nat → Int) : Nat :=
    ∑ j ∈ Finset.range n, colCost rows m j (v j)

  def colFreq (rows : List (List Int)) (m j : Nat) (x : Int) : Nat :=
    ((Finset.range m).filter fun i => cell rows i j = x).card

  def colValues (rows : List (List Int)) (m j : Nat) : Finset Int :=
    ((Finset.range m).image fun i => cell rows i j) ∪ {0}

  def colMaxFreq (rows : List (List Int)) (m j : Nat) : Nat :=
    (colValues rows m j).sup fun x => colFreq rows m j x

  def IndexSetOK (row : List Int) (n : Nat) (S : Finset Nat) : Prop :=
    S ⊆ Finset.range n ∧
      ∀ i, i + 1 < n → i ∈ S → i + 1 ∈ S → row.getD i 0 ≠ row.getD (i + 1) 0

  def MaxIndexSetSize (row : List Int) (n k : Nat) : Prop :=
    (∃ S, IndexSetOK row n S ∧ S.card = k) ∧ ∀ S, IndexSetOK row n S → S.card ≤ k

  def permApply {m : Nat} (π : Equiv.Perm (Fin m)) (i : Nat) : Nat :=
    if h : i < m then (π ⟨i, h⟩).val else i

  def digitPermApply (π : Equiv.Perm (Fin 10)) (x : Int) : Int :=
    ((π ⟨x.toNat % 10, Nat.mod_lt _ (by decide)⟩ : Fin 10).val : Int)

  /-- The function returns a result r, and r is the minimum value of C(v) over all functions v : {0,...,n-1} -> Z such that v(j) >= 0 for every j and v(j) != v(j+1) for every 0 <= j < n-1, where C(v) = sum_{j=0}^{n-1} #{ i | 0 <= i < m and grid[i][j] != v(j) }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        (∃ v : Nat → Int, Admissible n v ∧
          r.val = (totalCost (rowsOf grid) m n v : Int)) ∧
        (∀ v : Nat → Int, Admissible n v →
          r.val ≤ (totalCost (rowsOf grid) m n v : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          (∃ v : Nat → Int, Admissible n v ∧
            r.val = (totalCost (rowsOf grid) m n v : Int)) ∧
          (∀ v : Nat → Int, Admissible n v →
            r.val ≤ (totalCost (rowsOf grid) m n v : Int))) := by
    sorry

  /-- The function returns a result on every input satisfying the preconditions; it does not panic, overflow, or fail.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r) := by
    sorry

  /-- The function returns a result r, and 0 <= r <= m*n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        0 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          0 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if both of the following hold: (1) grid[i][j] = grid[i+1][j] for every 0 <= i < m-1 and 0 <= j < n; (2) grid[i][j] != grid[i][j+1] for every 0 <= i < m and 0 <= j < n-1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        (r.val = 0 ↔
          ((∀ i, i + 1 < m → ∀ j, j < n →
              cell (rowsOf grid) i j = cell (rowsOf grid) (i + 1) j) ∧
            (∀ i, i < m → ∀ j, j + 1 < n →
              cell (rowsOf grid) i j ≠ cell (rowsOf grid) i (j + 1)))) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          (r.val = 0 ↔
            ((∀ i, i + 1 < m → ∀ j, j < n →
                cell (rowsOf grid) i j = cell (rowsOf grid) (i + 1) j) ∧
              (∀ i, i < m → ∀ j, j + 1 < n →
                cell (rowsOf grid) i j ≠ cell (rowsOf grid) i (j + 1))))) := by
    sorry

  /-- The function returns a result r, and r = m - max_{x in Z, x >= 0} #{ i | 0 <= i < m and grid[i][0] = x }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n = 1, m <= 1000, len(grid[i]) = 1 for every 0 <= i < m, and 0 <= grid[i][0] <= 9 for every 0 <= i < m. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn : n = 1)
      (hm1000 : m ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        r.val = ((m : Int) - (colMaxFreq (rowsOf grid) m 0 : Int)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn : n = 1)
        (hm1000 : m ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          r.val = ((m : Int) - (colMaxFreq (rowsOf grid) m 0 : Int))) := by
    sorry

  /-- The function returns a result r, and r = n - max { |S| : S subset of {0,...,n-1} and for every i with 0 <= i < n-1, if i in S and i+1 in S then grid[0][i] != grid[0][i+1] }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m = 1, n >= 1, n <= 1000, len(grid[0]) = n, and 0 <= grid[0][j] <= 9 for every 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (row : List Int) (m n : Nat)
      (hm : grid.val.length = m) (hm_eq : m = 1) (hn1 : 1 ≤ n) (hn1000 : n ≤ 1000)
      (hrows : rowsOf grid = [row]) (hlen : row.length = n)
      (hbound : ∀ j, j < n → 0 ≤ row.getD j 0 ∧ row.getD j 0 ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        ∃ k : Nat, MaxIndexSetSize row n k ∧ r.val = ((n : Int) - (k : Int)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (row : List Int) (m n : Nat)
        (hm : grid.val.length = m) (hm_eq : m = 1) (hn1 : 1 ≤ n) (hn1000 : n ≤ 1000)
        (hrows : rowsOf grid = [row]) (hlen : row.length = n)
        (hbound : ∀ j, j < n → 0 ≤ row.getD j 0 ∧ row.getD j 0 ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          ∃ k : Nat, MaxIndexSetSize row n k ∧ r.val = ((n : Int) - (k : Int))) := by
    sorry

  /-- The function returns a result r, and r >= sum_{j=0}^{n-1} (m - f_j), where f_j = max_{x in Z, x >= 0} #{ i | 0 <= i < m and grid[i][j] = x }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        (∑ j ∈ Finset.range n,
            ((m : Int) - (colMaxFreq (rowsOf grid) m j : Int))) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          (∑ j ∈ Finset.range n,
              ((m : Int) - (colMaxFreq (rowsOf grid) m j : Int))) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and there exists a function v : {0,...,n-1} -> Z such that v(j) >= 0 for every j, v(j) != v(j+1) for every 0 <= j < n-1, and r = sum_{j=0}^{n-1} #{ i | 0 <= i < m and grid[i][j] != v(j) }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        ∃ v : Nat → Int, Admissible n v ∧
          r.val = (totalCost (rowsOf grid) m n v : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          ∃ v : Nat → Int, Admissible n v ∧
            r.val = (totalCost (rowsOf grid) m n v : Int)) := by
    sorry

  /-- The function returns a result r, and for every function v : {0,...,n-1} -> Z with v(j) >= 0 for every j and v(j) != v(j+1) for every 0 <= j < n-1, we have r <= sum_{j=0}^{n-1} #{ i | 0 <= i < m and grid[i][j] != v(j) }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        ∀ v : Nat → Int, Admissible n v →
          r.val ≤ (totalCost (rowsOf grid) m n v : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          ∀ v : Nat → Int, Admissible n v →
            r.val ≤ (totalCost (rowsOf grid) m n v : Int)) := by
    sorry

  /-- The function returns a result r on grid. Let pi be any permutation of {0,...,m-1}, and define grid' by len(grid') = m, len(grid'[i]) = n, and grid'[i][j] = grid[pi(i)][j] for all 0 <= i < m and 0 <= j < n. The function returns a result r' on grid', and r' = r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (π : Equiv.Perm (Fin m))
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
      (hrows' : (rowsOf grid').length = m)
      (hlen' : ∀ i, i < m → (rowOf (rowsOf grid') i).length = n)
      (hcells' : ∀ i j, i < m → j < n →
        cell (rowsOf grid') i j = cell (rowsOf grid) (permApply π i) j) :
      ∃ r r' : Std.I64, minimum_operations grid = ok r ∧
        minimum_operations grid' = ok r' ∧ r' = r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (π : Equiv.Perm (Fin m))
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
        (hrows' : (rowsOf grid').length = m)
        (hlen' : ∀ i, i < m → (rowOf (rowsOf grid') i).length = n)
        (hcells' : ∀ i j, i < m → j < n →
          cell (rowsOf grid') i j = cell (rowsOf grid) (permApply π i) j), ∃ r r' : Std.I64, minimum_operations grid = ok r ∧
          minimum_operations grid' = ok r' ∧ r' = r) := by
    sorry

  /-- The function returns a result r on grid. Define grid' by len(grid') = m, len(grid'[i]) = n, and grid'[i][j] = grid[i][n-1-j] for all 0 <= i < m and 0 <= j < n. The function returns a result r' on grid', and r' = r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
      (hrows' : (rowsOf grid').length = m)
      (hlen' : ∀ i, i < m → (rowOf (rowsOf grid') i).length = n)
      (hcells' : ∀ i j, i < m → j < n →
        cell (rowsOf grid') i j = cell (rowsOf grid) i (n - 1 - j)) :
      ∃ r r' : Std.I64, minimum_operations grid = ok r ∧
        minimum_operations grid' = ok r' ∧ r' = r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
        (hrows' : (rowsOf grid').length = m)
        (hlen' : ∀ i, i < m → (rowOf (rowsOf grid') i).length = n)
        (hcells' : ∀ i j, i < m → j < n →
          cell (rowsOf grid') i j = cell (rowsOf grid) i (n - 1 - j)), ∃ r r' : Std.I64, minimum_operations grid = ok r ∧
          minimum_operations grid' = ok r' ∧ r' = r) := by
    sorry

  /-- The function returns a result r on grid. Let pi be any permutation of {0,1,...,9}, and define grid'[i][j] = pi(grid[i][j]) for all 0 <= i < m and 0 <= j < n. The function returns a result r' on grid', and r' = r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (π : Equiv.Perm (Fin 10))
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
      (hrows' : (rowsOf grid').length = m)
      (hlen' : ∀ i, i < m → (rowOf (rowsOf grid') i).length = n)
      (hcells' : ∀ i j, i < m → j < n →
        cell (rowsOf grid') i j = digitPermApply π (cell (rowsOf grid) i j)) :
      ∃ r r' : Std.I64, minimum_operations grid = ok r ∧
        minimum_operations grid' = ok r' ∧ r' = r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (π : Equiv.Perm (Fin 10))
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
        (hrows' : (rowsOf grid').length = m)
        (hlen' : ∀ i, i < m → (rowOf (rowsOf grid') i).length = n)
        (hcells' : ∀ i j, i < m → j < n →
          cell (rowsOf grid') i j = digitPermApply π (cell (rowsOf grid) i j)), ∃ r r' : Std.I64, minimum_operations grid = ok r ∧
          minimum_operations grid' = ok r' ∧ r' = r) := by
    sorry

  /-- The function returns a result r, and r = m * floor(n/2).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, every entry is 0 <= grid[i][j] <= 9, and there exists c with 0 <= c <= 9 such that grid[i][j] = c for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
      (hc : ∃ c : Int, 0 ≤ c ∧ c ≤ 9 ∧
        ∀ i j, i < m → j < n → cell (rowsOf grid) i j = c) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        r.val = ((m * (n / 2) : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9)
        (hc : ∃ c : Int, 0 ≤ c ∧ c ≤ 9 ∧
          ∀ i j, i < m → j < n → cell (rowsOf grid) i j = c), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          r.val = ((m * (n / 2) : Nat) : Int)) := by
    sorry

  /-- The function returns a result r, and there exists a function v : {0,...,n-1} -> {0,...,9} such that v(j) != v(j+1) for every 0 <= j < n-1 and r = sum_{j=0}^{n-1} #{ i | 0 <= i < m and grid[i][j] != v(j) }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 1000, n <= 1000, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
      (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
      (hbound : ∀ i j, i < m → j < n →
        0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9) :
      ∃ r : Std.I64, minimum_operations grid = ok r ∧
        ∃ v : Nat → Int, DigitAdmissible n v ∧
          r.val = (totalCost (rowsOf grid) m n v : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hm1000 : m ≤ 1000) (hn1000 : n ≤ 1000)
        (hlen : ∀ i, i < m → (rowOf (rowsOf grid) i).length = n)
        (hbound : ∀ i j, i < m → j < n →
          0 ≤ cell (rowsOf grid) i j ∧ cell (rowsOf grid) i j ≤ 9), ∃ r : Std.I64, minimum_operations grid = ok r ∧
          ∃ v : Nat → Int, DigitAdmissible n v ∧
            r.val = (totalCost (rowsOf grid) m n v : Int)) := by
    sorry

  end AegisSpec.MinimumOperations
