import Aegis.SpiralOrder.Code.Funs

/-!
# Specifications of `Aegis.SpiralOrder.spiral_order`

LeetCode problem `spiral-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SpiralOrder

def rows (matrix : Slice (alloc.vec.Vec I64)) : Nat := matrix.val.length

def cols (matrix : Slice (alloc.vec.Vec I64)) : Nat :=
  match matrix.val with
  | [] => 0
  | row :: _ => row.val.length

def WellFormed (matrix : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ rows matrix ∧ rows matrix ≤ 10 ∧ 1 ≤ cols matrix ∧ cols matrix ≤ 10 ∧
  (∀ (i : Nat) (row : alloc.vec.Vec I64), matrix.val[i]? = some row → row.val.length = cols matrix) ∧
  (∀ (i j : Nat) (row : alloc.vec.Vec I64) (x : I64),
      matrix.val[i]? = some row → row.val[j]? = some x → -100 ≤ x.val ∧ x.val ≤ 100)

def layers (m n : Nat) : Nat := (min m n + 1) / 2

def rowSpan (i l r : Nat) : List (Nat × Nat) :=
  (List.range (r + 1 - l)).map (fun k => (i, l + k))

def colSpan (j t b : Nat) : List (Nat × Nat) :=
  (List.range (b + 1 - t)).map (fun k => (t + k, j))

def rowSpanRev (i l r : Nat) : List (Nat × Nat) :=
  (List.range (r + 1 - l)).map (fun k => (i, r - k))

def colSpanRev (j t b : Nat) : List (Nat × Nat) :=
  (List.range (b + 1 - t)).map (fun k => (b - k, j))

def block (m n l : Nat) : List (Nat × Nat) :=
  let top := l
  let bottom := m - 1 - l
  let left := l
  let right := n - 1 - l
  if top = bottom then
    rowSpan top left right
  else if left = right then
    colSpan left top bottom
  else
    rowSpan top left right ++
    colSpan right (top + 1) bottom ++
    rowSpanRev bottom left (right - 1) ++
    colSpanRev left (top + 1) (bottom - 1)

def spiralPos (m n : Nat) : List (Nat × Nat) :=
  ((List.range (layers m n)).map (fun l => block m n l)).flatten

def entry (matrix : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  match matrix.val[i]? with
  | none => 0
  | some row => (row.val[j]?).map (fun x => x.val) |>.getD 0

def outVal (r : alloc.vec.Vec I64) (k : Nat) : Int := (r.val[k]?).map (fun x => x.val) |>.getD 0

def countOut (r : alloc.vec.Vec I64) (v : Int) : Nat :=
  (r.val.filter (fun x => x.val = v)).length

def countMatrix (matrix : Slice (alloc.vec.Vec I64)) (v : Int) : Nat :=
  (matrix.val.map (fun row => (row.val.filter (fun x => x.val = v)).length)).sum

/-- Let layers = (min(m,n) + 1) / 2 (integer division). For each l with 0 <= l < layers, put top_l = l, bottom_l = m - 1 - l, left_l = l, right_l = n - 1 - l, and define block(l) as follows: if top_l = bottom_l, block(l) is the list [(top_l, j) for j = left_l, left_l+1, ..., right_l]; else if left_l = right_l, block(l) is the list [(i, left_l) for i = top_l, top_l+1, ..., bottom_l]; otherwise block(l) is the concatenation of (a) [(top_l, j) for j = left_l, ..., right_l], then (b) [(i, right_l) for i = top_l+1, ..., bottom_l], then (c) [(bottom_l, j) for j = right_l-1, right_l-2, ..., left_l], then (d) [(i, left_l) for i = bottom_l-1, bottom_l-2, ..., top_l+1]. Let P be the concatenation block(0), block(1), ..., block(layers-1). Then the function returns a vector r such that len(r) = m*n and for every k with 0 <= k < m*n, if P[k] = (i,j) then r[k] = matrix[i][j].
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume 1 <= m <= 10, 1 <= n <= 10, every row matrix[i] for 0 <= i < m has length n, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.SpiralOrder.spiral_order matrix = ok r ∧
        r.val.length = rows matrix * cols matrix ∧
        ∀ (k i j : Nat), k < rows matrix * cols matrix →
          (spiralPos (rows matrix) (cols matrix))[k]? = some (i, j) → outVal r k = entry matrix i j := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix), ∃ r : alloc.vec.Vec I64,
      Aegis.SpiralOrder.spiral_order matrix = ok r ∧
        r.val.length = rows matrix * cols matrix ∧
        ∀ (k i j : Nat), k < rows matrix * cols matrix →
          (spiralPos (rows matrix) (cols matrix))[k]? = some (i, j) → outVal r k = entry matrix i j) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, overflow, or out-of-bounds).
  Preconditions: Same as spec_1. -/
theorem spec_2 (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix) :
    ∃ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix), ∃ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r) := by
  sorry

/-- Whenever the function returns r, for every integer v, the number of indices k with 0 <= k < len(r) and r[k] = v equals the number of pairs (i,j) with 0 <= i < m, 0 <= j < n and matrix[i][j] = v. Equivalently, r is a permutation (multiset) of the flattened matrix.
  Preconditions: Same as spec_1. -/
theorem spec_3 (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix) :
    ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ v : Int, countOut r v = countMatrix matrix v := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix), ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ v : Int, countOut r v = countMatrix matrix v) := by
  sorry

/-- Whenever the function returns r, for every j with 0 <= j < n, r[j] = matrix[0][j]. Thus the first n entries of r are exactly the first row of matrix in left-to-right order.
  Preconditions: Same as spec_1. -/
theorem spec_4 (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix) :
    ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ j : Nat, j < cols matrix → outVal r j = entry matrix 0 j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix), ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ j : Nat, j < cols matrix → outVal r j = entry matrix 0 j) := by
  sorry

/-- Whenever the function returns r, for every k with 0 <= k <= m-2, r[n + k] = matrix[k+1][n-1]. After the first row, the next m-1 entries are the rightmost column from row 1 to row m-1.
  Preconditions: Same as spec_1. -/
theorem spec_5 (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix) :
    ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ k : Nat, k + 2 ≤ rows matrix →
        outVal r (cols matrix + k) = entry matrix (k + 1) (cols matrix - 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix), ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ k : Nat, k + 2 ≤ rows matrix →
        outVal r (cols matrix + k) = entry matrix (k + 1) (cols matrix - 1)) := by
  sorry

/-- Whenever the function returns r, for every k with 0 <= k <= n-2, r[n + (m-1) + k] = matrix[m-1][n-2-k]. After the top row and the right column, the next n-1 entries are the bottom row from column n-2 down to 0.
  Preconditions: Same as spec_1, and m >= 2 and n >= 2. -/
theorem spec_6 (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix)
    (hm : 2 ≤ rows matrix) (hn : 2 ≤ cols matrix) :
    ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ k : Nat, k + 2 ≤ cols matrix →
        outVal r (cols matrix + (rows matrix - 1) + k) =
          entry matrix (rows matrix - 1) (cols matrix - 2 - k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix)
    (hm : 2 ≤ rows matrix) (hn : 2 ≤ cols matrix), ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ k : Nat, k + 2 ≤ cols matrix →
        outVal r (cols matrix + (rows matrix - 1) + k) =
          entry matrix (rows matrix - 1) (cols matrix - 2 - k)) := by
  sorry

/-- Whenever the function returns r, for every k with 0 <= k <= m-3, r[n + (m-1) + (n-1) + k] = matrix[m-2-k][0]. After the top row, right column and bottom row, the next m-2 entries are the leftmost column from row m-2 up to row 1.
  Preconditions: Same as spec_1, and m >= 3 and n >= 2. -/
theorem spec_7 (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix)
    (hm : 3 ≤ rows matrix) (hn : 2 ≤ cols matrix) :
    ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ k : Nat, k + 3 ≤ rows matrix →
        outVal r (cols matrix + (rows matrix - 1) + (cols matrix - 1) + k) =
          entry matrix (rows matrix - 2 - k) 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (h : WellFormed matrix)
    (hm : 3 ≤ rows matrix) (hn : 2 ≤ cols matrix), ∀ r : alloc.vec.Vec I64, Aegis.SpiralOrder.spiral_order matrix = ok r →
      ∀ k : Nat, k + 3 ≤ rows matrix →
        outVal r (cols matrix + (rows matrix - 1) + (cols matrix - 1) + k) =
          entry matrix (rows matrix - 2 - k) 0) := by
  sorry

end AegisSpec.SpiralOrder
