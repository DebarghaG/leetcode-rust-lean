import Aegis.GenerateMatrix.Code.Funs

/-!
# Specifications of `Aegis.GenerateMatrix.generate_matrix`

LeetCode problem `spiral-matrix-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GenerateMatrix

def entry (M : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  match M.val[i]? with
  | none => 0
  | some row => ((row.val[j]?).map fun x => x.val).getD 0

def rowLen (M : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
  ((M.val[i]?).map fun row => row.val.length).getD 0

def spiralOffset (m a b : ℤ) : ℤ :=
  if a = 0 then b
  else if b = m - 1 then (m - 1) + a
  else if a = m - 1 then 2 * (m - 1) + (m - 1 - b)
  else 3 * (m - 1) + (m - 1 - a)

def spiralVal (n i j : ℤ) : ℤ :=
  let l := min (min i j) (min (n - 1 - i) (n - 1 - j))
  let m := n - 2 * l
  n ^ 2 - m ^ 2 + 1 + spiralOffset m (i - l) (j - l)

/-- generate_matrix n returns a result r (it does not fail). Let M = r. Then len(M) = n, and for every i with 0 <= i < n, len(M[i]) = n. Moreover, for every i,j with 0 <= i < n and 0 <= j < n, M[i][j] = n^2 - m^2 + 1 + o, where l = min(i, j, n-1-i, n-1-j), m = n - 2*l, a = i - l, b = j - l, and o is determined as follows: if a = 0 then o = b; else if b = m-1 then o = (m-1) + a; else if a = m-1 then o = 2*(m-1) + (m-1-b); else (so b = 0) o = 3*(m-1) + (m-1-a). This formula defines the complete n x n spiral matrix.
  Preconditions: 1 <= n <= 20. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) :
    ∃ r, Aegis.GenerateMatrix.generate_matrix n = ok r ∧
      (r.val.length : ℤ) = n.val ∧
      (∀ i : ℤ, 0 ≤ i → i < n.val → (rowLen r i.toNat : ℤ) = n.val) ∧
      (∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
        entry r i.toNat j.toNat = spiralVal n.val i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20), ∃ r, Aegis.GenerateMatrix.generate_matrix n = ok r ∧
      (r.val.length : ℤ) = n.val ∧
      (∀ i : ℤ, 0 ≤ i → i < n.val → (rowLen r i.toNat : ℤ) = n.val) ∧
      (∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
        entry r i.toNat j.toNat = spiralVal n.val i j)) := by
  sorry

/-- For every n satisfying the precondition, generate_matrix n returns a result r and does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= n <= 20. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) :
    ∃ r, Aegis.GenerateMatrix.generate_matrix n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20), ∃ r, Aegis.GenerateMatrix.generate_matrix n = ok r) := by
  sorry

/-- Whenever generate_matrix n returns a result r, len(r) = n.
  Preconditions: 1 <= n <= 20. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    (r.val.length : ℤ) = n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), (r.val.length : ℤ) = n.val) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every i with 0 <= i < n, len(r[i]) = n.
  Preconditions: 1 <= n <= 20. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ i : ℤ, 0 ≤ i → i < n.val → (rowLen r i.toNat : ℤ) = n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ i : ℤ, 0 ≤ i → i < n.val → (rowLen r i.toNat : ℤ) = n.val) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every i,j with 0 <= i < n and 0 <= j < n, 1 <= r[i][j] <= n^2.
  Preconditions: 1 <= n <= 20. -/
theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
      1 ≤ entry r i.toNat j.toNat ∧ entry r i.toNat j.toNat ≤ n.val ^ 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ i j : ℤ, 0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
      1 ≤ entry r i.toNat j.toNat ∧ entry r i.toNat j.toNat ≤ n.val ^ 2) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for all i1,j1,i2,j2 with 0 <= i1,i2 < n and 0 <= j1,j2 < n, if (i1,j1) != (i2,j2) then r[i1][j1] != r[i2][j2].
  Preconditions: 1 <= n <= 20. -/
theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ i1 j1 i2 j2 : ℤ,
      0 ≤ i1 → i1 < n.val → 0 ≤ j1 → j1 < n.val →
      0 ≤ i2 → i2 < n.val → 0 ≤ j2 → j2 < n.val →
      (i1, j1) ≠ (i2, j2) →
      entry r i1.toNat j1.toNat ≠ entry r i2.toNat j2.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ i1 j1 i2 j2 : ℤ,
      0 ≤ i1 → i1 < n.val → 0 ≤ j1 → j1 < n.val →
      0 ≤ i2 → i2 < n.val → 0 ≤ j2 → j2 < n.val →
      (i1, j1) ≠ (i2, j2) →
      entry r i1.toNat j1.toNat ≠ entry r i2.toNat j2.toNat) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every k with 1 <= k <= n^2 there exist i,j with 0 <= i < n and 0 <= j < n such that r[i][j] = k.
  Preconditions: 1 <= n <= 20. -/
theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ k : ℤ, 1 ≤ k → k ≤ n.val ^ 2 →
      ∃ i j : ℤ, 0 ≤ i ∧ i < n.val ∧ 0 ≤ j ∧ j < n.val ∧
        entry r i.toNat j.toNat = k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ k : ℤ, 1 ≤ k → k ≤ n.val ^ 2 →
      ∃ i j : ℤ, 0 ≤ i ∧ i < n.val ∧ 0 ≤ j ∧ j < n.val ∧
        entry r i.toNat j.toNat = k) := by
  sorry

/-- Whenever generate_matrix n returns a result r, r[0][0] = 1.
  Preconditions: 1 <= n <= 20. -/
theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    entry r 0 0 = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), entry r 0 0 = 1) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every j with 0 <= j < n-1, r[0][j+1] = r[0][j] + 1.
  Preconditions: 1 <= n <= 20. -/
theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ j : ℤ, 0 ≤ j → j < n.val - 1 →
      entry r 0 (j + 1).toNat = entry r 0 j.toNat + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ j : ℤ, 0 ≤ j → j < n.val - 1 →
      entry r 0 (j + 1).toNat = entry r 0 j.toNat + 1) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every i with 0 <= i < n-1, r[i+1][n-1] = r[i][n-1] + 1.
  Preconditions: 1 <= n <= 20 and n >= 2. -/
theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 2 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ i : ℤ, 0 ≤ i → i < n.val - 1 →
      entry r (i + 1).toNat (n.val - 1).toNat = entry r i.toNat (n.val - 1).toNat + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 2 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ i : ℤ, 0 ≤ i → i < n.val - 1 →
      entry r (i + 1).toNat (n.val - 1).toNat = entry r i.toNat (n.val - 1).toNat + 1) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every j with 0 <= j < n-1, r[n-1][j] = r[n-1][j+1] + 1.
  Preconditions: 1 <= n <= 20 and n >= 2. -/
theorem spec_11 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 2 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ j : ℤ, 0 ≤ j → j < n.val - 1 →
      entry r (n.val - 1).toNat j.toNat = entry r (n.val - 1).toNat (j + 1).toNat + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 2 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ j : ℤ, 0 ≤ j → j < n.val - 1 →
      entry r (n.val - 1).toNat j.toNat = entry r (n.val - 1).toNat (j + 1).toNat + 1) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every i with 1 <= i < n-1, r[i+1][0] = r[i][0] - 1.
  Preconditions: 1 <= n <= 20 and n >= 3. -/
theorem spec_12 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 3 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ i : ℤ, 1 ≤ i → i < n.val - 1 →
      entry r (i + 1).toNat 0 = entry r i.toNat 0 - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 3 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ i : ℤ, 1 ≤ i → i < n.val - 1 →
      entry r (i + 1).toNat 0 = entry r i.toNat 0 - 1) := by
  sorry

/-- Whenever generate_matrix n returns a result r, the set of values { r[i][j] : 0 <= i < n, 0 <= j < n, and (i = 0 or i = n-1 or j = 0 or j = n-1) } is exactly {1, 2, ..., 4*n - 4}.
  Preconditions: 1 <= n <= 20 and n >= 2. -/
theorem spec_13 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 2 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    {v : ℤ | ∃ i j : ℤ, 0 ≤ i ∧ i < n.val ∧ 0 ≤ j ∧ j < n.val ∧
        (i = 0 ∨ i = n.val - 1 ∨ j = 0 ∨ j = n.val - 1) ∧
        entry r i.toNat j.toNat = v}
      = {v : ℤ | 1 ≤ v ∧ v ≤ 4 * n.val - 4} := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 2 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), {v : ℤ | ∃ i j : ℤ, 0 ≤ i ∧ i < n.val ∧ 0 ≤ j ∧ j < n.val ∧
        (i = 0 ∨ i = n.val - 1 ∨ j = 0 ∨ j = n.val - 1) ∧
        entry r i.toNat j.toNat = v}
      = {v : ℤ | 1 ≤ v ∧ v ≤ 4 * n.val - 4}) := by
  sorry

/-- Whenever generate_matrix n returns a result r, for every k with 1 <= k < n^2 and all i,j,i',j' with 0 <= i,i' < n and 0 <= j,j' < n, if r[i][j] = k and r[i'][j'] = k+1 then |i - i'| + |j - j'| = 1.
  Preconditions: 1 <= n <= 20. -/
theorem spec_14 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ k : ℤ, 1 ≤ k → k < n.val ^ 2 →
      ∀ i j i' j' : ℤ,
        0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
        0 ≤ i' → i' < n.val → 0 ≤ j' → j' < n.val →
        entry r i.toNat j.toNat = k →
        entry r i'.toNat j'.toNat = k + 1 →
        |i - i'| + |j - j'| = 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ k : ℤ, 1 ≤ k → k < n.val ^ 2 →
      ∀ i j i' j' : ℤ,
        0 ≤ i → i < n.val → 0 ≤ j → j < n.val →
        0 ≤ i' → i' < n.val → 0 ≤ j' → j' < n.val →
        entry r i.toNat j.toNat = k →
        entry r i'.toNat j'.toNat = k + 1 →
        |i - i'| + |j - j'| = 1) := by
  sorry

/-- Whenever generate_matrix n returns a result r, if n is odd then r[(n-1)/2][(n-1)/2] = n^2, and if n is even then r[n/2][n/2 - 1] = n^2.
  Preconditions: 1 <= n <= 20. -/
theorem spec_15 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    (n.val % 2 = 1 →
        entry r ((n.val - 1) / 2).toNat ((n.val - 1) / 2).toNat = n.val ^ 2) ∧
      (n.val % 2 = 0 →
        entry r (n.val / 2).toNat (n.val / 2 - 1).toNat = n.val ^ 2) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), (n.val % 2 = 1 →
        entry r ((n.val - 1) / 2).toNat ((n.val - 1) / 2).toNat = n.val ^ 2) ∧
      (n.val % 2 = 0 →
        entry r (n.val / 2).toNat (n.val / 2 - 1).toNat = n.val ^ 2)) := by
  sorry

/-- Whenever generate_matrix n returns a result r, let s be the (n-2) x (n-2) matrix whose entries are 1,2,...,(n-2)^2 in clockwise inward spiral order starting at its top-left corner and moving right (the spiral matrix of side n-2). Then for every i,j with 0 <= i < n-2 and 0 <= j < n-2, r[i+1][j+1] = (4*n - 4) + s[i][j].
  Preconditions: 1 <= n <= 20 and n >= 3. -/
theorem spec_16 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 3 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r) :
    ∀ i j : ℤ, 0 ≤ i → i < n.val - 2 → 0 ≤ j → j < n.val - 2 →
      entry r (i + 1).toNat (j + 1).toNat = (4 * n.val - 4) + spiralVal (n.val - 2) i j := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hn3 : 3 ≤ n.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.GenerateMatrix.generate_matrix n = ok r), ∀ i j : ℤ, 0 ≤ i → i < n.val - 2 → 0 ≤ j → j < n.val - 2 →
      entry r (i + 1).toNat (j + 1).toNat = (4 * n.val - 4) + spiralVal (n.val - 2) i j) := by
  sorry

end AegisSpec.GenerateMatrix
