import Aegis.LuckyNumbers.Code.Funs

/-!
# Specifications of `Aegis.LuckyNumbers.lucky_numbers`

LeetCode problem `lucky-numbers-in-a-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LuckyNumbers

namespace AegisSpec.LuckyNumbers

def numRows (matrix : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  matrix.val.length

def rowLen (matrix : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  match matrix.val[i]? with
  | none => 0
  | some row => row.val.length

def numCols (matrix : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  rowLen matrix 0

def entry (matrix : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match matrix.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def outVal (r : alloc.vec.Vec Std.I64) (p : Nat) : Int :=
  match r.val[p]? with
  | none => 0
  | some x => x.val

def Occurs (r : alloc.vec.Vec Std.I64) (v : Int) : Prop :=
  ∃ p, p < r.val.length ∧ outVal r p = v

def IsLucky (matrix : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  (∀ k, k < numCols matrix → entry matrix i k ≥ entry matrix i j) ∧
    (∀ k, k < numRows matrix → entry matrix k j ≤ entry matrix i j)

/-- Whenever the function returns a result r, len(r) <= 1 and for every integer v: (there exists an index p with 0 <= p < len(r) and r[p] = v) if and only if there exist i and j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = v, for every k with 0 <= k < n we have matrix[i][k] >= matrix[i][j], and for every k with 0 <= k < m we have matrix[k][j] <= matrix[i][j].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, for every i,j with 0 <= i < m and 0 <= j < n we have 1 <= matrix[i][j] <= 100000, and all entries of matrix are pairwise distinct (for (i,j) != (i',j'), matrix[i][j] != matrix[i'][j']). -/
theorem spec_1 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r →
      r.val.length ≤ 1 ∧
        (∀ v : Int, Occurs r v ↔
          ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
            entry matrix i j = v ∧ IsLucky matrix i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r →
      r.val.length ≤ 1 ∧
        (∀ v : Int, Occurs r v ↔
          ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
            entry matrix i j = v ∧ IsLucky matrix i j)) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 1.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_2 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r → r.val.length ≤ 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r → r.val.length ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, for every index p with 0 <= p < len(r), 1 <= r[p] <= 100000.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, for every i,j with 0 <= i < m and 0 <= j < n we have 1 <= matrix[i][j] <= 100000, and all entries are pairwise distinct. -/
theorem spec_3 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r →
      ∀ p, p < r.val.length → 1 ≤ outVal r p ∧ outVal r p ≤ 100000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r →
      ∀ p, p < r.val.length → 1 ≤ outVal r p ∧ outVal r p ≤ 100000) := by
  sorry

/-- Whenever the function returns a result r, for every index p with 0 <= p < len(r), there exist i and j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = r[p].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_4 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r →
      ∀ p, p < r.val.length →
        ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r p := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r →
      ∀ p, p < r.val.length →
        ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r p) := by
  sorry

/-- Whenever the function returns a result r and len(r) == 1, there exist i and j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = r[0] and for every k with 0 <= k < n, matrix[i][k] >= r[0].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_5 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        (∀ k, k < numCols matrix → entry matrix i k ≥ outVal r 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        (∀ k, k < numCols matrix → entry matrix i k ≥ outVal r 0)) := by
  sorry

/-- Whenever the function returns a result r and len(r) == 1, there exist i and j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = r[0] and for every k with 0 <= k < m, matrix[k][j] <= r[0].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_6 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        (∀ k, k < numRows matrix → entry matrix k j ≤ outVal r 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        (∀ k, k < numRows matrix → entry matrix k j ≤ outVal r 0)) := by
  sorry

/-- Whenever the function returns a result r and len(r) == 1, r[0] is a lucky number: there exist i and j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = r[0], for every k with 0 <= k < n we have matrix[i][k] >= r[0], and for every k with 0 <= k < m we have matrix[k][j] <= r[0].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_7 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        IsLucky matrix i j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        IsLucky matrix i j) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < m and 0 <= j < n, if matrix[i][j] is lucky — meaning for every k with 0 <= k < n, matrix[i][k] >= matrix[i][j], and for every k with 0 <= k < m, matrix[k][j] <= matrix[i][j] — then len(r) == 1 and r[0] == matrix[i][j].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, for every i,j with 0 <= i < m and 0 <= j < n we have 1 <= matrix[i][j] <= 100000, and all entries of matrix are pairwise distinct (for (i,j) != (i',j'), matrix[i][j] != matrix[i'][j']). -/
theorem spec_8 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r →
      ∀ i j, i < numRows matrix → j < numCols matrix → IsLucky matrix i j →
        r.val.length = 1 ∧ outVal r 0 = entry matrix i j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r →
      ∀ i j, i < numRows matrix → j < numCols matrix → IsLucky matrix i j →
        r.val.length = 1 ∧ outVal r 0 = entry matrix i j) := by
  sorry

/-- The function returns a result r and does not fail (no integer overflow, panic, or out-of-bounds access).
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_9 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∃ r, lucky_numbers matrix = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∃ r, lucky_numbers matrix = ok r) := by
  sorry

/-- Whenever the function returns a result r and len(r) == 1, there exist i and j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = r[0], for every k with 0 <= k < n and k != j we have matrix[i][k] > r[0], and for every k with 0 <= k < m and k != i we have matrix[k][j] < r[0].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_10 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j') :
    ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        (∀ k, k < numCols matrix → k ≠ j → entry matrix i k > outVal r 0) ∧
        (∀ k, k < numRows matrix → k ≠ i → entry matrix k j < outVal r 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j'), ∀ r, lucky_numbers matrix = ok r → r.val.length = 1 →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧ entry matrix i j = outVal r 0 ∧
        (∀ k, k < numCols matrix → k ≠ j → entry matrix i k > outVal r 0) ∧
        (∀ k, k < numRows matrix → k ≠ i → entry matrix k j < outVal r 0)) := by
  sorry

/-- If m == 1, then whenever the function returns a result r, len(r) == 1 and r[0] is the minimum of the single row: there exists j with 0 <= j < n and matrix[0][j] = r[0], and for every j with 0 <= j < n, matrix[0][j] >= r[0].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_11 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j')
    (hm : numRows matrix = 1) :
    ∀ r, lucky_numbers matrix = ok r →
      r.val.length = 1 ∧
        (∃ j, j < numCols matrix ∧ entry matrix 0 j = outVal r 0) ∧
          (∀ j, j < numCols matrix → entry matrix 0 j ≥ outVal r 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j')
    (hm : numRows matrix = 1), ∀ r, lucky_numbers matrix = ok r →
      r.val.length = 1 ∧
        (∃ j, j < numCols matrix ∧ entry matrix 0 j = outVal r 0) ∧
          (∀ j, j < numCols matrix → entry matrix 0 j ≥ outVal r 0)) := by
  sorry

/-- If n == 1, then whenever the function returns a result r, len(r) == 1 and r[0] is the maximum of the single column: there exists i with 0 <= i < m and matrix[i][0] = r[0], and for every i with 0 <= i < m, matrix[i][0] <= r[0].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Then 1 <= m <= 50, 1 <= n <= 50, for every i with 0 <= i < m we have len(matrix[i]) = n, all entries are in [1,100000], and all entries are pairwise distinct. -/
theorem spec_12 (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j')
    (hn : numCols matrix = 1) :
    ∀ r, lucky_numbers matrix = ok r →
      r.val.length = 1 ∧
        (∃ i, i < numRows matrix ∧ entry matrix i 0 = outVal r 0) ∧
          (∀ i, i < numRows matrix → entry matrix i 0 ≤ outVal r 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 50)
    (hn_pos : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 50)
    (h_rows : ∀ i, i < numRows matrix → rowLen matrix i = numCols matrix)
    (h_range : ∀ i j, i < numRows matrix → j < numCols matrix →
      1 ≤ entry matrix i j ∧ entry matrix i j ≤ 100000)
    (h_distinct : ∀ i j i' j', i < numRows matrix → j < numCols matrix →
      i' < numRows matrix → j' < numCols matrix → (i, j) ≠ (i', j') →
      entry matrix i j ≠ entry matrix i' j')
    (hn : numCols matrix = 1), ∀ r, lucky_numbers matrix = ok r →
      r.val.length = 1 ∧
        (∃ i, i < numRows matrix ∧ entry matrix i 0 = outVal r 0) ∧
          (∀ i, i < numRows matrix → entry matrix i 0 ≤ outVal r 0)) := by
  sorry

end AegisSpec.LuckyNumbers
