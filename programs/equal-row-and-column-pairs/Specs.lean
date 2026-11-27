import Aegis.EqualPairs.Code.Funs

/-!
# Specifications of `Aegis.EqualPairs.equal_pairs`

LeetCode problem `equal-row-and-column-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace AegisSpec.EqualPairs

def entries (grid : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def entryAt (m : List (List ℤ)) (i k : Nat) : ℤ := (m.getD i []).getD k 0

def rowSeq (m : List (List ℤ)) (n : Nat) (i : Nat) : Fin n → ℤ := fun k => entryAt m i k

def colSeq (m : List (List ℤ)) (n : Nat) (j : Nat) : Fin n → ℤ := fun k => entryAt m k j

def RowEqCol (m : List (List ℤ)) (n : Nat) (i j : Nat) : Prop :=
  ∀ k, k < n → entryAt m i k = entryAt m k j

def RowEqRow (m : List (List ℤ)) (n : Nat) (i j : Nat) : Prop :=
  ∀ k, k < n → entryAt m i k = entryAt m j k

def ColEqRow (m : List (List ℤ)) (n : Nat) (i j : Nat) : Prop :=
  ∀ k, k < n → entryAt m k i = entryAt m j k

def ColEqCol (m : List (List ℤ)) (n : Nat) (i j : Nat) : Prop :=
  ∀ k, k < n → entryAt m k i = entryAt m k j

noncomputable def countPairs (n : Nat) (P : Nat → Nat → Prop) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n))).filter
    (fun p : Fin n × Fin n => P (p.1 : Nat) (p.2 : Nat)) |>.card

noncomputable def countIdx (n : Nat) (P : Nat → Prop) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => P (i : Nat))).card

noncomputable def rowImage (m : List (List ℤ)) (n : Nat) : Finset (Fin n → ℤ) := by
  classical
  exact (Finset.univ : Finset (Fin n)).image (fun i : Fin n => rowSeq m n (i : Nat))

noncomputable def colImage (m : List (List ℤ)) (n : Nat) : Finset (Fin n → ℤ) := by
  classical
  exact (Finset.univ : Finset (Fin n)).image (fun j : Fin n => colSeq m n (j : Nat))

noncomputable def rowMult (m : List (List ℤ)) (n : Nat) (v : Fin n → ℤ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => rowSeq m n (i : Nat) = v)).card

noncomputable def colMult (m : List (List ℤ)) (n : Nat) (v : Fin n → ℤ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n => colSeq m n (j : Nat) = v)).card

/-- Whenever equal_pairs(grid) returns a result r, r equals the number of ordered pairs (i, j) with 0 <= i < n and 0 <= j < n such that row i of grid equals column j of grid; equivalently, such that for every k with 0 <= k < n, grid[i][k] = grid[k][j].
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (countPairs n (fun i j => RowEqCol (entries grid) n i j) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (countPairs n (fun i j => RowEqCol (entries grid) n i j) : ℤ)) := by
  sorry

/-- equal_pairs(grid) returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∃ r, Aegis.EqualPairs.equal_pairs grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∃ r, Aegis.EqualPairs.equal_pairs grid = ok r) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, 0 <= r <= n * n.
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      0 ≤ r.val ∧ r.val ≤ (n : ℤ) * (n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      0 ≤ r.val ∧ r.val ≤ (n : ℤ) * (n : ℤ)) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r > 0 if and only if there exist indices i, j with 0 <= i < n and 0 <= j < n such that row i of grid equals column j of grid (i.e. for every k with 0 <= k < n, grid[i][k] = grid[k][j]).
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      (0 < r.val ↔ ∃ i j, i < n ∧ j < n ∧ RowEqCol (entries grid) n i j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      (0 < r.val ↔ ∃ i j, i < n ∧ j < n ∧ RowEqCol (entries grid) n i j)) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r = n * n if and only if all entries of grid are equal, i.e. for every i, j, i', j' with 0 <= i < n, 0 <= j < n, 0 <= i' < n, and 0 <= j' < n, grid[i][j] = grid[i'][j'].
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      (r.val = (n : ℤ) * (n : ℤ) ↔
        ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          entryAt (entries grid) i j = entryAt (entries grid) i' j') := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      (r.val = (n : ℤ) * (n : ℤ) ↔
        ∀ i j i' j', i < n → j < n → i' < n → j' < n →
          entryAt (entries grid) i j = entryAt (entries grid) i' j')) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r >= d, where d is the number of indices i with 0 <= i < n such that row i of grid equals column i of grid (i.e. for every k with 0 <= k < n, grid[i][k] = grid[k][i]).
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      (countIdx n (fun i => RowEqCol (entries grid) n i i) : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      (countIdx n (fun i => RowEqCol (entries grid) n i i) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r equals the number of ordered pairs (i, j) with 0 <= i < n and 0 <= j < n such that row i of grid equals row j of grid (i.e. for every k with 0 <= k < n, grid[i][k] = grid[j][k]).
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume grid is symmetric: for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = grid[j][i]. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hsymm : ∀ i j, i < n → j < n → entryAt (entries grid) i j = entryAt (entries grid) j i) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (countPairs n (fun i j => RowEqRow (entries grid) n i j) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hsymm : ∀ i j, i < n → j < n → entryAt (entries grid) i j = entryAt (entries grid) j i), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (countPairs n (fun i j => RowEqRow (entries grid) n i j) : ℤ)) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r also equals the number of ordered pairs (i, j) with 0 <= i < n and 0 <= j < n such that column i of grid equals row j of grid (i.e. for every k with 0 <= k < n, grid[k][i] = grid[j][k]).
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (countPairs n (fun i j => ColEqRow (entries grid) n i j) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (countPairs n (fun i j => ColEqRow (entries grid) n i j) : ℤ)) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r equals the sum, over all length-n sequences v of 64-bit integers, of R(v) * C(v), where R(v) is the number of indices i with 0 <= i < n such that row i of grid equals v, and C(v) is the number of indices j with 0 <= j < n such that column j of grid equals v. Only finitely many v have R(v) or C(v) nonzero.
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (rowImage (entries grid) n ∪ colImage (entries grid) n).sum
        (fun v => (rowMult (entries grid) n v : ℤ) * (colMult (entries grid) n v : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = (rowImage (entries grid) n ∪ colImage (entries grid) n).sum
        (fun v => (rowMult (entries grid) n v : ℤ) * (colMult (entries grid) n v : ℤ))) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r equals the number of length-n sequences v of 64-bit integers that occur both as a row of grid and as a column of grid; that is, the number of v for which there exists i with 0 <= i < n and row i = v and there exists j with 0 <= j < n and column j = v.
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume all rows are pairwise distinct: for every i, j with 0 <= i < n and 0 <= j < n, if row i equals row j then i = j. Assume all columns are pairwise distinct: for every i, j with 0 <= i < n and 0 <= j < n, if column i equals column j then i = j. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hrowDistinct : ∀ i j, i < n → j < n →
      RowEqRow (entries grid) n i j → i = j)
    (hcolDistinct : ∀ i j, i < n → j < n →
      ColEqCol (entries grid) n i j → i = j) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = ((rowImage (entries grid) n ∩ colImage (entries grid) n).card : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hrowDistinct : ∀ i j, i < n → j < n →
      RowEqRow (entries grid) n i j → i = j)
    (hcolDistinct : ∀ i j, i < n → j < n →
      ColEqCol (entries grid) n i j → i = j), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r →
      r.val = ((rowImage (entries grid) n ∩ colImage (entries grid) n).card : ℤ)) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r = 0.
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume all rows of grid are equal to the first row: for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = grid[0][j]. Assume the first row is not constant: there exist j, k with 0 <= j < n and 0 <= k < n such that grid[0][j] != grid[0][k]. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hrowsEq : ∀ i j, i < n → j < n →
      entryAt (entries grid) i j = entryAt (entries grid) 0 j)
    (hnotConst : ∃ j k, j < n ∧ k < n ∧
      entryAt (entries grid) 0 j ≠ entryAt (entries grid) 0 k) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r → r.val = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hrowsEq : ∀ i j, i < n → j < n →
      entryAt (entries grid) i j = entryAt (entries grid) 0 j)
    (hnotConst : ∃ j k, j < n ∧ k < n ∧
      entryAt (entries grid) 0 j ≠ entryAt (entries grid) 0 k), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r → r.val = 0) := by
  sorry

/-- Whenever equal_pairs(grid) returns a result r, r = n.
  Preconditions: Let n = len(grid). Assume 1 <= n <= 200. Assume for every i with 0 <= i < n, len(grid[i]) = n. Assume for every i, j with 0 <= i < n and 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume there exist values a and b with a != b such that for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = a if i = j, and grid[i][j] = b if i != j. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hdia : ∃ a b : ℤ, a ≠ b ∧ ∀ i j, i < n → j < n →
      (i = j → entryAt (entries grid) i j = a) ∧
      (i ≠ j → entryAt (entries grid) i j = b)) :
    ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r → r.val = (n : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = (entries grid).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrow : ∀ i, i < n → ((entries grid).getD i []).length = n)
    (hentry : ∀ i j, i < n → j < n →
      1 ≤ entryAt (entries grid) i j ∧ entryAt (entries grid) i j ≤ 100000)
    (hdia : ∃ a b : ℤ, a ≠ b ∧ ∀ i j, i < n → j < n →
      (i = j → entryAt (entries grid) i j = a) ∧
      (i ≠ j → entryAt (entries grid) i j = b)), ∀ r, Aegis.EqualPairs.equal_pairs grid = ok r → r.val = (n : ℤ)) := by
  sorry

end AegisSpec.EqualPairs
