import Aegis.OnesMinusZeros.Code.Funs

/-!
# Specifications of `Aegis.OnesMinusZeros.ones_minus_zeros`

LeetCode problem `difference-between-ones-and-zeros-in-row-and-column`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.OnesMinusZeros

  def gridInts (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map (fun row => row.val.map (fun x => x.val))

  def outInts (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) :=
    r.val.map (fun row => row.val.map (fun x => x.val))

  def gridEntry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((gridInts grid).getD i []).getD j 0

  def rowOnes (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    (((gridInts grid).getD i []).countP (fun x => x == 1) : Int)

  def colOnes (grid : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
    (((gridInts grid).map (fun row => row.getD j 0)).countP (fun x => x == 1) : Int)

  def totalOnes (grid : Slice (alloc.vec.Vec Std.I64)) : Int :=
    (((gridInts grid).flatten).countP (fun x => x == 1) : Int)

  def outAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((outInts r).getD i []).getD j 0

  /-- The function returns a result r and does not fail. Moreover, len(r) = m, for every 0 <= i < m len(r[i]) = n, and for every 0 <= i < m and 0 <= j < n, r[i][j] = R_i + C_j - (n - R_i) - (m - C_j), where R_i is the number of k with 0 <= k < n and grid[i][k] = 1, and C_j is the number of k with 0 <= k < m and grid[k][j] = 1. Equivalently, r[i][j] = 2*R_i + 2*C_j - (m + n).
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∃ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r ∧
        (outInts r).length = m ∧
        (∀ i, i < m → ((outInts r).getD i []).length = n) ∧
        (∀ i j, i < m → j < n →
          outAt r i j = rowOnes grid i + colOnes grid j - ((n : Int) - rowOnes grid i)
            - ((m : Int) - colOnes grid j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∃ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r ∧
          (outInts r).length = m ∧
          (∀ i, i < m → ((outInts r).getD i []).length = n) ∧
          (∀ i j, i < m → j < n →
            outAt r i j = rowOnes grid i + colOnes grid j - ((n : Int) - rowOnes grid i)
              - ((m : Int) - colOnes grid j))) := by
    sorry

  /-- The function returns a result r and does not fail.
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∃ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∃ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = m and for every 0 <= i < m, len(r[i]) = n.
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        (outInts r).length = m ∧ (∀ i, i < m → ((outInts r).getD i []).length = n) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          (outInts r).length = m ∧ (∀ i, i < m → ((outInts r).getD i []).length = n)) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and every 0 <= j < n and 0 <= k < n, r[i][j] - r[i][k] = 2*(C_j - C_k), where C_j is the number of q with 0 <= q < m and grid[q][j] = 1, and C_k is the number of q with 0 <= q < m and grid[q][k] = 1.
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ i j k, i < m → j < n → k < n →
          outAt r i j - outAt r i k = 2 * (colOnes grid j - colOnes grid k) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ i j k, i < m → j < n → k < n →
            outAt r i j - outAt r i k = 2 * (colOnes grid j - colOnes grid k)) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= j < n and every 0 <= i < m and 0 <= k < m, r[i][j] - r[k][j] = 2*(R_i - R_k), where R_i is the number of q with 0 <= q < n and grid[i][q] = 1, and R_k is the number of q with 0 <= q < n and grid[k][q] = 1.
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ j i k, j < n → i < m → k < m →
          outAt r i j - outAt r k j = 2 * (rowOnes grid i - rowOnes grid k) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ j i k, j < n → i < m → k < m →
            outAt r i j - outAt r k j = 2 * (rowOnes grid i - rowOnes grid k)) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= k < m, if R_i = R_k, where R_i and R_k are the numbers of ones in rows i and k respectively, then for every 0 <= j < n, r[i][j] = r[k][j].
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ i k, i < m → k < m → rowOnes grid i = rowOnes grid k →
          ∀ j, j < n → outAt r i j = outAt r k j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ i k, i < m → k < m → rowOnes grid i = rowOnes grid k →
            ∀ j, j < n → outAt r i j = outAt r k j) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= j < n and 0 <= l < n, if C_j = C_l, where C_j and C_l are the numbers of ones in columns j and l respectively, then for every 0 <= i < m, r[i][j] = r[i][l].
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ j l, j < n → l < n → colOnes grid j = colOnes grid l →
          ∀ i, i < m → outAt r i j = outAt r i l := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ j l, j < n → l < n → colOnes grid j = colOnes grid l →
            ∀ i, i < m → outAt r i j = outAt r i l) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, -(m + n) <= r[i][j] <= m + n.
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ i j, i < m → j < n → -((m : Int) + (n : Int)) ≤ outAt r i j ∧
          outAt r i j ≤ (m : Int) + (n : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ i j, i < m → j < n → -((m : Int) + (n : Int)) ≤ outAt r i j ∧
            outAt r i j ≤ (m : Int) + (n : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] + m + n is divisible by 2.
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ i j, i < m → j < n →
          (2 : Int) ∣ (outAt r i j + (m : Int) + (n : Int)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ i j, i < m → j < n →
            (2 : Int) ∣ (outAt r i j + (m : Int) + (n : Int))) := by
    sorry

  /-- Let T be the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1. Whenever the function returns a result r, the sum over all 0 <= i < m and 0 <= j < n of r[i][j] equals (m + n)*(2*T - m*n).
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, outAt r i j)
          = ((m : Int) + (n : Int)) *
              (2 * totalOnes grid - (m : Int) * (n : Int)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, outAt r i j)
            = ((m : Int) + (n : Int)) *
                (2 * totalOnes grid - (m : Int) * (n : Int))) := by
    sorry

  /-- Let T be the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1. Whenever the function returns a result r, for every 0 <= j < n, if C_j is the number of q with 0 <= q < m and grid[q][j] = 1, then the sum over 0 <= i < m of r[i][j] equals 2*T + 2*m*C_j - m*(m + n).
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ j, j < n →
          (∑ i ∈ Finset.range m, outAt r i j)
            = 2 * totalOnes grid + 2 * (m : Int) * colOnes grid j
                - (m : Int) * ((m : Int) + (n : Int)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ j, j < n →
            (∑ i ∈ Finset.range m, outAt r i j)
              = 2 * totalOnes grid + 2 * (m : Int) * colOnes grid j
                  - (m : Int) * ((m : Int) + (n : Int))) := by
    sorry

  /-- Let T be the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1. Whenever the function returns a result r, for every 0 <= i < m, if R_i is the number of q with 0 <= q < n and grid[i][q] = 1, then the sum over 0 <= j < n of r[i][j] equals 2*n*R_i + 2*T - n*(m + n).
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ i, i < m →
          (∑ j ∈ Finset.range n, outAt r i j)
            = 2 * (n : Int) * rowOnes grid i + 2 * totalOnes grid
                - (n : Int) * ((m : Int) + (n : Int)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ i, i < m →
            (∑ j ∈ Finset.range n, outAt r i j)
              = 2 * (n : Int) * rowOnes grid i + 2 * totalOnes grid
                  - (n : Int) * ((m : Int) + (n : Int))) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = m + n if and only if row i is all ones (grid[i][k] = 1 for every 0 <= k < n) and column j is all ones (grid[k][j] = 1 for every 0 <= k < m).
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ i j, i < m → j < n →
          (outAt r i j = (m : Int) + (n : Int) ↔
            (∀ k, k < n → gridEntry grid i k = 1) ∧
            (∀ k, k < m → gridEntry grid k j = 1)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ i j, i < m → j < n →
            (outAt r i j = (m : Int) + (n : Int) ↔
              (∀ k, k < n → gridEntry grid i k = 1) ∧
              (∀ k, k < m → gridEntry grid k j = 1))) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = -(m + n) if and only if row i is all zeros (grid[i][k] = 0 for every 0 <= k < n) and column j is all zeros (grid[k][j] = 0 for every 0 <= k < m).
    Preconditions: Let m = len(grid). The input grid is valid: m >= 1, there is an integer n >= 1 such that every row grid[i] for 0 <= i < m has length n, m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
  theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
      (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
      (hsize : m * n ≤ 100000)
      (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1) :
      ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
        ∀ i j, i < m → j < n →
          (outAt r i j = -((m : Int) + (n : Int)) ↔
            (∀ k, k < n → gridEntry grid i k = 0) ∧
            (∀ k, k < m → gridEntry grid k j = 0)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
        (hrows : ∀ i, i < m → ((gridInts grid).getD i []).length = n)
        (hsize : m * n ≤ 100000)
        (hentries : ∀ i j, i < m → j < n → gridEntry grid i j = 0 ∨ gridEntry grid i j = 1), ∀ r, Aegis.OnesMinusZeros.ones_minus_zeros grid = ok r →
          ∀ i j, i < m → j < n →
            (outAt r i j = -((m : Int) + (n : Int)) ↔
              (∀ k, k < n → gridEntry grid i k = 0) ∧
              (∀ k, k < m → gridEntry grid k j = 0))) := by
    sorry

  end AegisSpec.OnesMinusZeros
