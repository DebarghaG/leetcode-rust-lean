import Aegis.TrailingZeroes.Code.Funs

/-!
# Specifications of `Aegis.TrailingZeroes.trailing_zeroes`

LeetCode problem `factorial-trailing-zeroes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TrailingZeroes

def legendreSum5 (n : Nat) : Nat := (Finset.range (n + 1)).sum (fun k => n / 5 ^ (k + 1))

def digitSum5 (n : Nat) : Nat :=
  (Finset.range (Nat.log 5 n + 1)).sum (fun i => (n / 5 ^ i) % 5)

def v5 (i : Nat) : Nat := Nat.findGreatest (fun k => 5 ^ k ∣ i) i

def factN (n : Nat) : Nat := n.factorial

/-- The function returns a result r, and r = Σ_{k=1}^{∞} ⌊n / 5^k⌋, where the sum has finitely many nonzero terms (equivalently, r is the exponent of 5 in the prime factorization of n!).
  Preconditions: 0 <= n <= 10000 -/
theorem spec_1 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = (legendreSum5 n.val.toNat : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = (legendreSum5 n.val.toNat : Int)) := by
  sorry

/-- For every n with 0 <= n <= 10000, the function returns a result r with 0 <= r, and 10^r divides n! and 10^(r+1) does not divide n!, where n! = ∏_{i=1}^{n} i with 0! = 1.
  Preconditions: 0 <= n <= 10000 -/
theorem spec_2 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      0 ≤ r.val ∧
      (10 ^ r.val.toNat ∣ factN n.val.toNat ∧ ¬ (10 ^ (r.val.toNat + 1) ∣ factN n.val.toNat)) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      0 ≤ r.val ∧
      (10 ^ r.val.toNat ∣ factN n.val.toNat ∧ ¬ (10 ^ (r.val.toNat + 1) ∣ factN n.val.toNat))) := by
  sorry

/-- For every n with 0 <= n <= 10000, the function returns a result r with 0 <= r, and there exists an integer m such that n! = 5^r * m and m is not divisible by 5, where n! = ∏_{i=1}^{n} i with 0! = 1.
  Preconditions: 0 <= n <= 10000 -/
theorem spec_3 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      0 ≤ r.val ∧
      ∃ m : Int, (factN n.val.toNat : Int) = 5 ^ r.val.toNat * m ∧ ¬ ((5 : Int) ∣ m) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      0 ≤ r.val ∧
      ∃ m : Int, (factN n.val.toNat : Int) = 5 ^ r.val.toNat * m ∧ ¬ ((5 : Int) ∣ m)) := by
  sorry

/-- The function returns a result r, and r <= ⌊n/4⌋.
  Preconditions: 0 <= n <= 10000 -/
theorem spec_4 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val ≤ n.val / 4 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val ≤ n.val / 4) := by
  sorry

/-- The function returns a result r, and (r = 0 ⇔ n < 5).
  Preconditions: 0 <= n <= 10000 -/
theorem spec_5 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      (r.val = 0 ↔ n.val < 5) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      (r.val = 0 ↔ n.val < 5)) := by
  sorry

/-- The function returns a result r, and r >= ⌊n/5⌋.
  Preconditions: 0 <= n <= 10000 -/
theorem spec_6 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      n.val / 5 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      n.val / 5 ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = ⌊n/5⌋ + ⌊n/25⌋ + ⌊n/125⌋ + ⌊n/625⌋ + ⌊n/3125⌋.
  Preconditions: 0 <= n <= 10000 -/
theorem spec_7 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = n.val / 5 + n.val / 25 + n.val / 125 + n.val / 625 + n.val / 3125 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = n.val / 5 + n.val / 25 + n.val / 125 + n.val / 625 + n.val / 3125) := by
  sorry

/-- The function returns a result r, and r = (n - s_5(n)) / 4, where s_5(n) is the sum of the base-5 digits of n (if n = Σ_{i=0}^{m} d_i 5^i with 0 <= d_i <= 4, then s_5(n) = Σ_{i=0}^{m} d_i).
  Preconditions: 0 <= n <= 10000 -/
theorem spec_8 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = (n.val - (digitSum5 n.val.toNat : Int)) / 4 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = (n.val - (digitSum5 n.val.toNat : Int)) / 4) := by
  sorry

/-- The function returns a result r, and r = Σ_{i=1}^{n} v_5(i), where v_5(i) is the largest integer k >= 0 such that 5^k divides i (with v_5(1) = 0).
  Preconditions: 0 <= n <= 10000 -/
theorem spec_9 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = ((Finset.range (n.val.toNat + 1)).sum (fun i => v5 i) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r ∧
      r.val = ((Finset.range (n.val.toNat + 1)).sum (fun i => v5 i) : Int)) := by
  sorry

/-- For every n with 0 <= n <= 10000, the function returns a result r; that is, it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: 0 <= n <= 10000 -/
theorem spec_10 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r) := by
  sorry

/-- Whenever the function returns r1 on input n1 and r2 on input n2, we have r1 <= r2.
  Preconditions: 0 <= n1 <= n2 <= 10000 -/
theorem spec_11 (n1 n2 : Std.I64) (hn10 : 0 ≤ n1.val) (hn12 : n1.val ≤ n2.val)
    (hn20 : n2.val ≤ 10000) :
    ∀ r1 r2 : Std.I64,
      Aegis.TrailingZeroes.trailing_zeroes n1 = Result.ok r1 →
      Aegis.TrailingZeroes.trailing_zeroes n2 = Result.ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n1 n2 : Std.I64) (hn10 : 0 ≤ n1.val) (hn12 : n1.val ≤ n2.val)
    (hn20 : n2.val ≤ 10000), ∀ r1 r2 : Std.I64,
      Aegis.TrailingZeroes.trailing_zeroes n1 = Result.ok r1 →
      Aegis.TrailingZeroes.trailing_zeroes n2 = Result.ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r on input n and returns r' on input ⌊n/5⌋, then r = ⌊n/5⌋ + r'.
  Preconditions: 0 <= n <= 10000 -/
theorem spec_12 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000) :
    ∀ n' : Std.I64, n'.val = n.val / 5 → ∀ r r' : Std.I64,
      Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r →
      Aegis.TrailingZeroes.trailing_zeroes n' = Result.ok r' →
      r.val = n.val / 5 + r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 10000), ∀ n' : Std.I64, n'.val = n.val / 5 → ∀ r r' : Std.I64,
      Aegis.TrailingZeroes.trailing_zeroes n = Result.ok r →
      Aegis.TrailingZeroes.trailing_zeroes n' = Result.ok r' →
      r.val = n.val / 5 + r'.val) := by
  sorry

end AegisSpec.TrailingZeroes
