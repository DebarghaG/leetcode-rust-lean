import Aegis.SpiralMatrixIii.Code.Funs

/-!
# Specifications of `Aegis.SpiralMatrixIii.spiral_matrix_iii`

LeetCode problem `spiral-matrix-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SpiralMatrixIii

def IsInBox (rows cols : ℤ) (p : ℤ × ℤ) : Prop :=
  0 ≤ p.1 ∧ p.1 < rows ∧ 0 ≤ p.2 ∧ p.2 < cols

def pairToList (p : ℤ × ℤ) : List ℤ := [p.1, p.2]

def Enumerates (p : ℕ → Prop) (idx : List ℕ) : Prop :=
  idx.Pairwise (· < ·) ∧ ∀ n, n ∈ idx ↔ p n

def entry (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (List ℤ) :=
  (r.val[i]?).map (fun v => v.val.map (fun x => x.val))

def contents (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  r.val.map (fun v => v.val.map (fun x => x.val))

structure WalkState where
  row : ℤ
  col : ℤ
  dir : ℕ
  left : ℕ
  segLen : ℕ
  deriving Repr, DecidableEq

def moveUnit (dir : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  match dir with
  | 0 => (p.1, p.2 + 1)
  | 1 => (p.1 + 1, p.2)
  | 2 => (p.1, p.2 - 1)
  | _ => (p.1 - 1, p.2)

def WalkState.step (s : WalkState) : WalkState :=
  let turn := s.left = 0
  let dir := if turn then (s.dir + 1) % 4 else s.dir
  let segLen := if turn then (if s.dir % 2 = 0 then s.segLen else s.segLen + 1) else s.segLen
  let left := if turn then segLen - 1 else s.left - 1
  let p := moveUnit dir (s.row, s.col)
  { row := p.1, col := p.2, dir := dir, left := left, segLen := segLen }

def initialWalkState (rStart cStart : ℤ) : WalkState :=
  { row := rStart, col := cStart, dir := 3, left := 0, segLen := 0 }

def WalkState.iterate (n : ℕ) (s : WalkState) : WalkState :=
  Nat.rec s (fun _ ih => ih.step) n

def walk (rStart cStart : ℤ) (n : ℕ) : ℤ × ℤ :=
  let s := WalkState.iterate n (initialWalkState rStart cStart)
  (s.row, s.col)

def zigzag (start : ℤ) : ℕ → ℤ
  | 0 => start
  | (k + 1) =>
    if k % 2 = 0 then start + ((k / 2 : ℕ) + 1 : ℤ) else start - ((k / 2 : ℕ) + 1 : ℤ)

/-- Let W be the infinite sequence of integer coordinate pairs (row, column) defined as follows. W[0] = (rStart, cStart). For j = 1, 2, 3, ..., let L_j = floor((j+1)/2), so L_1, L_2, L_3, ... = 1, 1, 2, 2, 3, 3, ...; and let the direction of segment j be east if j mod 4 = 1, south if j mod 4 = 2, west if j mod 4 = 3, and north if j mod 4 = 0, where east = (0,+1), south = (+1,0), west = (0,-1), north = (-1,0). Starting from the end of W after the previous segments, append L_j new positions by repeatedly adding the unit vector of that direction. Then, whenever the function returns a result r, r is exactly the finite list of all W[n] with n >= 0 and 0 <= first(W[n]) < rows and 0 <= second(W[n]) < cols, in increasing order of n; each r[i] is the two-element vector [row, column] for the corresponding pair.
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_1 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    ∃ idx : List ℕ,
      Enumerates (fun n => IsInBox rows.val cols.val (walk rStart.val cStart.val n)) idx ∧
        contents r = idx.map (fun n => pairToList (walk rStart.val cStart.val n)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), ∃ idx : List ℕ,
      Enumerates (fun n => IsInBox rows.val cols.val (walk rStart.val cStart.val n)) idx ∧
        contents r = idx.map (fun n => pairToList (walk rStart.val cStart.val n))) := by
  sorry

/-- The function returns a result r; in particular it does not fail because of arithmetic overflow, out-of-bounds indexing, or a panic.
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_2 (rows cols rStart cStart : Std.I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = rows * cols (the mathematical product) and, for every i with 0 <= i < len(r), len(r[i]) = 2.
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_3 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    (r.val.length : ℤ) = rows.val * cols.val ∧
      ∀ i, i < r.val.length → (entry r i).map (fun l => l.length) = some 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), (r.val.length : ℤ) = rows.val * cols.val ∧
      ∀ i, i < r.val.length → (entry r i).map (fun l => l.length) = some 2) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), writing r[i] = [a, b], we have 0 <= a < rows and 0 <= b < cols.
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_4 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    ∀ i, i < r.val.length →
      ∃ a b : ℤ, entry r i = some [a, b] ∧ 0 ≤ a ∧ a < rows.val ∧ 0 ≤ b ∧ b < cols.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), ∀ i, i < r.val.length →
      ∃ a b : ℤ, entry r i = some [a, b] ∧ 0 ≤ a ∧ a < rows.val ∧ 0 ≤ b ∧ b < cols.val) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and r[0] = [rStart, cStart].
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_5 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    1 ≤ r.val.length ∧ entry r 0 = some [rStart.val, cStart.val] := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), 1 ≤ r.val.length ∧ entry r 0 = some [rStart.val, cStart.val]) := by
  sorry

/-- Whenever the function returns a result r, for all indices i and j with 0 <= i < j < len(r), r[i] != r[j] (the two coordinate pairs are different).
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_6 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    ∀ i j, i < j → j < r.val.length → entry r i ≠ entry r j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), ∀ i j, i < j → j < r.val.length → entry r i ≠ entry r j) := by
  sorry

/-- Whenever the function returns a result r, for every row a and column b with 0 <= a < rows and 0 <= b < cols, there is exactly one index i with 0 <= i < len(r) such that r[i] = [a, b].
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_7 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    ∀ a b : ℤ, 0 ≤ a → a < rows.val → 0 ≤ b → b < cols.val →
      ∃ i, i < r.val.length ∧ entry r i = some [a, b] ∧
        ∀ j, j < r.val.length → entry r j = some [a, b] → j = i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), ∀ a b : ℤ, 0 ≤ a → a < rows.val → 0 ≤ b → b < cols.val →
      ∃ i, i < r.val.length ∧ entry r i = some [a, b] ∧
        ∀ j, j < r.val.length → entry r j = some [a, b] → j = i) := by
  sorry

/-- Whenever the function returns a result r, if cStart + 1 < cols, then len(r) >= 2 and r[1] = [rStart, cStart + 1].
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_8 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    cStart.val + 1 < cols.val →
      2 ≤ r.val.length ∧ entry r 1 = some [rStart.val, cStart.val + 1] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), cStart.val + 1 < cols.val →
      2 ≤ r.val.length ∧ entry r 1 = some [rStart.val, cStart.val + 1]) := by
  sorry

/-- Whenever the function returns a result r, if cStart + 1 < cols and rStart + 1 < rows, then len(r) >= 3 and r[2] = [rStart + 1, cStart + 1].
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_9 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    cStart.val + 1 < cols.val → rStart.val + 1 < rows.val →
      3 ≤ r.val.length ∧ entry r 2 = some [rStart.val + 1, cStart.val + 1] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), cStart.val + 1 < cols.val → rStart.val + 1 < rows.val →
      3 ≤ r.val.length ∧ entry r 2 = some [rStart.val + 1, cStart.val + 1]) := by
  sorry

/-- Whenever the function returns a result r, if rows = 1, then len(r) = cols and, for every i with 0 <= i < cols, r[i] = [0, x_i], where x_0, x_1, ..., x_{cols-1} is the list obtained from the infinite sequence cStart, cStart+1, cStart-1, cStart+2, cStart-2, cStart+3, cStart-3, ... by deleting every term that is not in the range 0 <= x < cols, keeping the remaining terms in their original order.
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_10 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    rows.val = 1 →
      (r.val.length : ℤ) = cols.val ∧
        ∃ idx : List ℕ,
          Enumerates (fun k => 0 ≤ zigzag cStart.val k ∧ zigzag cStart.val k < cols.val) idx ∧
            contents r = idx.map (fun k => [0, zigzag cStart.val k]) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), rows.val = 1 →
      (r.val.length : ℤ) = cols.val ∧
        ∃ idx : List ℕ,
          Enumerates (fun k => 0 ≤ zigzag cStart.val k ∧ zigzag cStart.val k < cols.val) idx ∧
            contents r = idx.map (fun k => [0, zigzag cStart.val k])) := by
  sorry

/-- Whenever the function returns a result r, if cols = 1, then len(r) = rows and, for every i with 0 <= i < rows, r[i] = [x_i, 0], where x_0, x_1, ..., x_{rows-1} is the list obtained from the infinite sequence rStart, rStart+1, rStart-1, rStart+2, rStart-2, rStart+3, rStart-3, ... by deleting every term that is not in the range 0 <= x < rows, keeping the remaining terms in their original order.
  Preconditions: rows, cols, rStart, cStart are the values of the four I64 parameters, and 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rStart < rows, 0 <= cStart < cols. -/
theorem spec_11 (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r) :
    cols.val = 1 →
      (r.val.length : ℤ) = rows.val ∧
        ∃ idx : List ℕ,
          Enumerates (fun k => 0 ≤ zigzag rStart.val k ∧ zigzag rStart.val k < rows.val) idx ∧
            contents r = idx.map (fun k => [zigzag rStart.val k, 0]) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rows cols rStart cStart : Std.I64)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrStart_lo : 0 ≤ rStart.val) (hrStart_hi : rStart.val < rows.val)
    (hcStart_lo : 0 ≤ cStart.val) (hcStart_hi : cStart.val < cols.val)
    (h : Aegis.SpiralMatrixIii.spiral_matrix_iii rows cols rStart cStart = ok r), cols.val = 1 →
      (r.val.length : ℤ) = rows.val ∧
        ∃ idx : List ℕ,
          Enumerates (fun k => 0 ≤ zigzag rStart.val k ∧ zigzag rStart.val k < rows.val) idx ∧
            contents r = idx.map (fun k => [zigzag rStart.val k, 0])) := by
  sorry

end AegisSpec.SpiralMatrixIii
