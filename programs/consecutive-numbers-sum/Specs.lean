import Aegis.ConsecutiveNumbersSum.Code.Funs

/-!
# Specifications of `Aegis.ConsecutiveNumbersSum.consecutive_numbers_sum`

LeetCode problem `consecutive-numbers-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ConsecutiveNumbersSum (consecutive_numbers_sum)

namespace AegisSpec.ConsecutiveNumbersSum

def reprCount (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
      (fun p : ℕ × ℕ =>
        1 ≤ p.1 ∧ 1 ≤ p.2 ∧
          2 * (n : ℤ) = (p.2 : ℤ) * (2 * (p.1 : ℤ) + (p.2 : ℤ) - 1))).card

def oddDivisorCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun d : ℕ => d % 2 = 1 ∧ n % d = 0)).card

def floorSqrt (n : ℕ) : ℕ := Nat.sqrt n

def oddPart (n : ℕ) : ℕ := n / 2 ^ (Nat.findGreatest (fun k : ℕ => 2 ^ k ∣ n) n)

def IsPerfectSquare (q : ℕ) : Prop := ∃ m : ℕ, q = m * m

def IsOddPrime (p : ℕ) : Prop := Nat.Prime p ∧ p % 2 = 1

/-- The function returns a result r, and r is exactly the number of pairs of integers (a, k) such that a >= 1, k >= 1, and 2*n = k*(2*a + k - 1). Equivalently, r is the number of nonempty sequences of consecutive positive integers whose sum is n; the length-1 sequence consisting only of n is included.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_1 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ r.val = (reprCount n.val.toNat : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ r.val = (reprCount n.val.toNat : ℤ)) := by
  sorry

/-- For every n with 1 <= n <= 10^9, the function returns a result (it does not fail, overflow, or panic).
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_2 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, consecutive_numbers_sum n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64, consecutive_numbers_sum n = ok r) := by
  sorry

/-- The returned value r satisfies r >= 1.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_3 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, consecutive_numbers_sum n = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64, consecutive_numbers_sum n = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The returned value r satisfies r <= 2*s.
  Preconditions: n is an integer with 1 <= n <= 10^9. Let s be the largest integer such that s*s <= n, so s = floor(sqrt(n)). -/
theorem spec_4 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ r.val ≤ 2 * (floorSqrt n.val.toNat : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ r.val ≤ 2 * (floorSqrt n.val.toNat : ℤ)) := by
  sorry

/-- The returned value r equals the number of positive odd integers d such that d divides n.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_5 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ r.val = (oddDivisorCount n.val.toNat : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ r.val = (oddDivisorCount n.val.toNat : ℤ)) := by
  sorry

/-- Let r be the result returned for n and let r' be the result returned for n*(2^t). The function returns both results and r' = r.
  Preconditions: n and t are integers with 1 <= n, t >= 0, and n*(2^t) <= 10^9. -/
theorem spec_6 (n m : Std.I64) (t : ℕ)
    (h_lo : 1 ≤ n.val) (h_m : m.val = n.val * 2 ^ t)
    (h_hi : n.val * 2 ^ t ≤ 1000000000) :
    ∃ r r' : Std.I64,
      consecutive_numbers_sum n = ok r ∧ consecutive_numbers_sum m = ok r' ∧ r' = r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n m : Std.I64) (t : ℕ)
    (h_lo : 1 ≤ n.val) (h_m : m.val = n.val * 2 ^ t)
    (h_hi : n.val * 2 ^ t ≤ 1000000000), ∃ r r' : Std.I64,
      consecutive_numbers_sum n = ok r ∧ consecutive_numbers_sum m = ok r' ∧ r' = r) := by
  sorry

/-- The returned value r satisfies r = 1.
  Preconditions: n is an integer with 1 <= n <= 10^9 and n = 2^t for some integer t >= 0. -/
theorem spec_7 (n : Std.I64) (t : ℕ)
    (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) (h_pow : n.val = 2 ^ t) :
    ∃ r : Std.I64, consecutive_numbers_sum n = ok r ∧ r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (t : ℕ)
    (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) (h_pow : n.val = 2 ^ t), ∃ r : Std.I64, consecutive_numbers_sum n = ok r ∧ r.val = 1) := by
  sorry

/-- The returned value r satisfies r >= 2.
  Preconditions: n is an even integer with 1 <= n <= 10^9 and n is not a power of two. -/
theorem spec_8 (n : Std.I64)
    (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000)
    (h_even : n.val % 2 = 0) (h_not_pow : ∀ t : ℕ, n.val ≠ 2 ^ t) :
    ∃ r : Std.I64, consecutive_numbers_sum n = ok r ∧ 2 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64)
    (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000)
    (h_even : n.val % 2 = 0) (h_not_pow : ∀ t : ℕ, n.val ≠ 2 ^ t), ∃ r : Std.I64, consecutive_numbers_sum n = ok r ∧ 2 ≤ r.val) := by
  sorry

/-- The returned value r is at least 2, and the pair (a, k) with a = (n-1)/2 and k = 2 satisfies a >= 1 and 2*n = k*(2*a + k - 1). Thus the two consecutive positive integers (n-1)/2 and (n+1)/2 are one of the representations counted by r.
  Preconditions: n is an odd integer with 3 <= n <= 10^9. -/
theorem spec_9 (n : Std.I64)
    (h_odd : n.val % 2 = 1) (h_lo : 3 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ 2 ≤ r.val ∧
        1 ≤ (n.val - 1) / 2 ∧
          2 * n.val = 2 * (2 * ((n.val - 1) / 2) + 2 - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64)
    (h_odd : n.val % 2 = 1) (h_lo : 3 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ 2 ≤ r.val ∧
        1 ≤ (n.val - 1) / 2 ∧
          2 * n.val = 2 * (2 * ((n.val - 1) / 2) + 2 - 1)) := by
  sorry

/-- The returned value r is at least 2, and the three consecutive positive integers n/3 - 1, n/3, and n/3 + 1 sum to n; hence they are one of the representations counted by r.
  Preconditions: n is an integer with 1 <= n <= 10^9, n is divisible by 3, and n >= 6. -/
theorem spec_10 (n : Std.I64)
    (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000)
    (h_dvd : (3 : ℤ) ∣ n.val) (h_ge : 6 ≤ n.val) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ 2 ≤ r.val ∧
        1 ≤ n.val / 3 - 1 ∧
          (n.val / 3 - 1) + n.val / 3 + (n.val / 3 + 1) = n.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64)
    (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000)
    (h_dvd : (3 : ℤ) ∣ n.val) (h_ge : 6 ≤ n.val), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧ 2 ≤ r.val ∧
        1 ≤ n.val / 3 - 1 ∧
          (n.val / 3 - 1) + n.val / 3 + (n.val / 3 + 1) = n.val) := by
  sorry

/-- For every pair of integers (a, k) that is counted by the returned value r (that is, a >= 1, k >= 1, and 2*n = k*(2*a + k - 1)), the length k satisfies k*(k+1)/2 <= n.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_11 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        ∀ a k : ℤ, 1 ≤ a → 1 ≤ k → 2 * n.val = k * (2 * a + k - 1) →
          k * (k + 1) / 2 ≤ n.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        ∀ a k : ℤ, 1 ≤ a → 1 ≤ k → 2 * n.val = k * (2 * a + k - 1) →
          k * (k + 1) / 2 ≤ n.val) := by
  sorry

/-- For every pair of integers (a, k) that is counted by the returned value r, the start a and the last term a+k-1 satisfy 1 <= a <= n and a+k-1 <= n.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_12 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        ∀ a k : ℤ, 1 ≤ a → 1 ≤ k → 2 * n.val = k * (2 * a + k - 1) →
          1 ≤ a ∧ a ≤ n.val ∧ a + k - 1 ≤ n.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        ∀ a k : ℤ, 1 ≤ a → 1 ≤ k → 2 * n.val = k * (2 * a + k - 1) →
          1 ≤ a ∧ a ≤ n.val ∧ a + k - 1 ≤ n.val) := by
  sorry

/-- The returned value r is odd if and only if q is a perfect square. Equivalently, r is odd if and only if n = 2^t * m^2 for some integers t >= 0 and m >= 1.
  Preconditions: n is an integer with 1 <= n <= 10^9. Let q be the odd part of n, i.e. n divided by the largest power of 2 dividing n. -/
theorem spec_13 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        (r.val % 2 = 1 ↔ IsPerfectSquare (oddPart n.val.toNat)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        (r.val % 2 = 1 ↔ IsPerfectSquare (oddPart n.val.toNat))) := by
  sorry

/-- The returned value r equals 2 if and only if q is an odd prime. Equivalently, r = 2 if and only if n = 2^t * p for some integer t >= 0 and odd prime p.
  Preconditions: n is an integer with 1 <= n <= 10^9. Let q be the odd part of n. -/
theorem spec_14 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        (r.val = 2 ↔ IsOddPrime (oddPart n.val.toNat)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 1000000000), ∃ r : Std.I64,
      consecutive_numbers_sum n = ok r ∧
        (r.val = 2 ↔ IsOddPrime (oddPart n.val.toNat))) := by
  sorry

end AegisSpec.ConsecutiveNumbersSum
