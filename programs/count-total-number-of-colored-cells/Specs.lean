import Aegis.ColoredCells.Code.Funs

/-!
# Specifications of `Aegis.ColoredCells.colored_cells`

LeetCode problem `count-total-number-of-colored-cells`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ColoredCells

  open Aegis.ColoredCells (colored_cells)

  def i64Succ (n : Std.I64) : Std.I64 := Aeneas.Std.I64.wrapping_add n 1#i64

  def sumOneTo (m : ℤ) : ℤ :=
    ((List.range m.toNat).map (fun i : ℕ => (i : ℤ) + 1)).sum

  /-- The function returns a result r, i.e. `colored_cells n = Result.ok r`, and, treating n and r as mathematical integers, r = 2*n*n - 2*n + 1.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
      ∃ r, colored_cells n = Result.ok r ∧
        r.val = 2 * n.val * n.val - 2 * n.val + 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∃ r, colored_cells n = Result.ok r ∧
          r.val = 2 * n.val * n.val - 2 * n.val + 1) := by
    sorry

  /-- For every such n, `colored_cells n` does not fail: there exists an i64 value r with `colored_cells n = Result.ok r`.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
      ∃ r, colored_cells n = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∃ r, colored_cells n = Result.ok r) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, the mathematical integer r satisfies 1 <= r <= 19999800001.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      1 ≤ r.val ∧ r.val ≤ 19999800001 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), 1 ≤ r.val ∧ r.val ≤ 19999800001) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, r >= n*n.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      n.val * n.val ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), n.val * n.val ≤ r.val) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, r < 2*n*n.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      r.val < 2 * n.val * n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), r.val < 2 * n.val * n.val) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, r is odd; equivalently, there exists an integer k with r = 2*k + 1.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      ∃ k : ℤ, r.val = 2 * k + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), ∃ k : ℤ, r.val = 2 * k + 1) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, r is congruent to 1 modulo 4; equivalently, there exists an integer q with r = 4*q + 1.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      ∃ q : ℤ, r.val = 4 * q + 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), ∃ q : ℤ, r.val = 4 * q + 1) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, r = n*n + (n-1)*(n-1).
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      r.val = n.val * n.val + (n.val - 1) * (n.val - 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), r.val = n.val * n.val + (n.val - 1) * (n.val - 1)) := by
    sorry

  /-- Evaluating at n and n+1 gives `colored_cells n = Result.ok r` and `colored_cells (n+1) = Result.ok s`, and the mathematical integers satisfy s - r = 4*n.
    Preconditions: n is an integer with 1 <= n < 100000. -/
  theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val < 100000) :
      ∃ r s, colored_cells n = Result.ok r ∧
        colored_cells (i64Succ n) = Result.ok s ∧
        s.val - r.val = 4 * n.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val < 100000), ∃ r s, colored_cells n = Result.ok r ∧
          colored_cells (i64Succ n) = Result.ok s ∧
          s.val - r.val = 4 * n.val) := by
    sorry

  /-- With `colored_cells n = Result.ok r`, `colored_cells (n+1) = Result.ok s`, and `colored_cells (n+2) = Result.ok t`, the mathematical integers satisfy t - 2*s + r = 4.
    Preconditions: n is an integer with 1 <= n <= 99998. -/
  theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 99998) :
      ∃ r s t, colored_cells n = Result.ok r ∧
        colored_cells (i64Succ n) = Result.ok s ∧
        colored_cells (i64Succ (i64Succ n)) = Result.ok t ∧
        t.val - 2 * s.val + r.val = 4 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 99998), ∃ r s t, colored_cells n = Result.ok r ∧
          colored_cells (i64Succ n) = Result.ok s ∧
          colored_cells (i64Succ (i64Succ n)) = Result.ok t ∧
          t.val - 2 * s.val + r.val = 4) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, r = 1 + 4 * (sum of all integers k with 1 <= k <= n-1), where the sum is 0 when n = 1.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_11 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      r.val = 1 + 4 * sumOneTo (n.val - 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), r.val = 1 + 4 * sumOneTo (n.val - 1)) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, r = 1 if and only if n = 1.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_12 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      r.val = 1 ↔ n.val = 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), r.val = 1 ↔ n.val = 1) := by
    sorry

  /-- If `colored_cells m = Result.ok r` and `colored_cells n = Result.ok s`, then s > r.
    Preconditions: m and n are integers with 1 <= m < n <= 100000. -/
  theorem spec_13 (m n : Std.I64) (hm1 : 1 ≤ m.val) (hmn : m.val < n.val)
      (hn2 : n.val ≤ 100000) (r s : Std.I64)
      (hr : colored_cells m = Result.ok r) (hs : colored_cells n = Result.ok s) :
      r.val < s.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (m n : Std.I64) (hm1 : 1 ≤ m.val) (hmn : m.val < n.val)
        (hn2 : n.val ≤ 100000) (r s : Std.I64)
        (hr : colored_cells m = Result.ok r) (hs : colored_cells n = Result.ok s), r.val < s.val) := by
    sorry

  /-- Whenever `colored_cells n = Result.ok r`, there exists an integer q such that r = 4*q + 1 and q = n*(n-1)/2.
    Preconditions: n is an integer with 1 <= n <= 100000. -/
  theorem spec_14 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
      (r : Std.I64) (hr : colored_cells n = Result.ok r) :
      ∃ q : ℤ, r.val = 4 * q + 1 ∧ q = n.val * (n.val - 1) / 2 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
        (r : Std.I64) (hr : colored_cells n = Result.ok r), ∃ q : ℤ, r.val = 4 * q + 1 ∧ q = n.val * (n.val - 1) / 2) := by
    sorry

  end AegisSpec.ColoredCells
