import Aegis.FindMaximumNumber.Code.Funs

/-!
# Specifications of `Aegis.FindMaximumNumber.find_maximum_number`

LeetCode problem `maximum-number-that-sum-of-the-prices-is-less-than-or-equal-to-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindMaximumNumber

  abbrev bitCounted (x i : ℕ) : Prop := x ∣ i + 1

  def price (x n : ℕ) : ℕ :=
    ((Finset.range (n + 1)).filter (fun i => n.testBit i = true ∧ bitCounted x i)).card

  def A (x n : ℕ) : ℕ := (Finset.range (n + 1)).sum (fun i => price x i)

  def AZ (x : ℕ) (n : ℤ) : ℤ := if 0 ≤ n then (A x n.toNat : ℤ) else 0

  /-- Let price_x(n) be the number of 1-bits of n at 1-based bit positions x, 2x, 3x, ... from the least significant bit, and let A_x(n) = sum_{i=1}^n price_x(i), with A_x(0) = 0. The function returns a result r such that r >= 0, A_x(r) <= k, and A_x(m) > k for every integer m > r. Equivalently, r is the greatest cheap number, i.e. the greatest nonnegative n with A_x(n) <= k.
    Preconditions: k and x are Std.I64 values with 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_1 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8) :
      ∃ r : Std.I64,
        Aegis.FindMaximumNumber.find_maximum_number k x = ok r ∧
        0 ≤ r.val ∧
        AZ x.val.toNat r.val ≤ k.val ∧
        ∀ m : ℤ, r.val < m → k.val < AZ x.val.toNat m := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8), ∃ r : Std.I64,
          Aegis.FindMaximumNumber.find_maximum_number k x = ok r ∧
          0 ≤ r.val ∧
          AZ x.val.toNat r.val ≤ k.val ∧
          ∀ m : ℤ, r.val < m → k.val < AZ x.val.toNat m) := by
    sorry

  /-- For every k and x satisfying the preconditions, the call find_maximum_number(k, x) returns a result r; it does not fail, panic, or report signed 64-bit overflow.
    Preconditions: k and x are Std.I64 values with 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_2 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8) :
      ∃ r : Std.I64, Aegis.FindMaximumNumber.find_maximum_number k x = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8), ∃ r : Std.I64, Aegis.FindMaximumNumber.find_maximum_number k x = ok r) := by
    sorry

  /-- Whenever the function returns r, with A_x defined as the accumulated price using bit positions x, 2x, 3x, ..., the next integer is not cheap: A_x(r+1) > k.
    Preconditions: k and x satisfy 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_3 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
      (r : Std.I64)
      (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r) :
      k.val < AZ x.val.toNat (r.val + 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
        (r : Std.I64)
        (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r), k.val < AZ x.val.toNat (r.val + 1)) := by
    sorry

  /-- Whenever the function returns r, every integer n with 0 <= n <= r is cheap: A_x(n) <= k.
    Preconditions: k and x satisfy 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_4 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
      (r : Std.I64)
      (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r) :
      ∀ n : ℤ, 0 ≤ n → n ≤ r.val → AZ x.val.toNat n ≤ k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
        (r : Std.I64)
        (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r), ∀ n : ℤ, 0 ≤ n → n ≤ r.val → AZ x.val.toNat n ≤ k.val) := by
    sorry

  /-- Whenever the function returns r, every cheap integer is at most r: for every integer n >= 0, if A_x(n) <= k then n <= r.
    Preconditions: k and x satisfy 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_5 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
      (r : Std.I64)
      (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r) :
      ∀ n : ℤ, 0 ≤ n → AZ x.val.toNat n ≤ k.val → n ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
        (r : Std.I64)
        (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r), ∀ n : ℤ, 0 ≤ n → AZ x.val.toNat n ≤ k.val → n ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, r >= 2^(x-1).
    Preconditions: k and x satisfy 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_6 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
      (r : Std.I64)
      (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r) :
      (2 : ℤ) ^ (x.val.toNat - 1) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
        (r : Std.I64)
        (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r), (2 : ℤ) ^ (x.val.toNat - 1) ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, r <= floor(k / 2^(x-1)) * 2^x + (2^x - 1).
    Preconditions: k and x satisfy 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_7 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
      (r : Std.I64)
      (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r) :
      r.val ≤ (k.val / (2 : ℤ) ^ (x.val.toNat - 1)) * (2 : ℤ) ^ x.val.toNat
        + ((2 : ℤ) ^ x.val.toNat - 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
        (r : Std.I64)
        (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r), r.val ≤ (k.val / (2 : ℤ) ^ (x.val.toNat - 1)) * (2 : ℤ) ^ x.val.toNat
          + ((2 : ℤ) ^ x.val.toNat - 1)) := by
    sorry

  /-- Under these preconditions, the function returns r = 2^(x-1).
    Preconditions: k = 1 and 1 <= x <= 8. -/
  theorem spec_8 (k x : Std.I64)
      (hk : k.val = 1)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8) :
      ∃ r : Std.I64,
        Aegis.FindMaximumNumber.find_maximum_number k x = ok r ∧
        r.val = (2 : ℤ) ^ (x.val.toNat - 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (k x : Std.I64)
        (hk : k.val = 1)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8), ∃ r : Std.I64,
          Aegis.FindMaximumNumber.find_maximum_number k x = ok r ∧
          r.val = (2 : ℤ) ^ (x.val.toNat - 1)) := by
    sorry

  /-- Whenever find_maximum_number(k1, x) returns r1 and find_maximum_number(k2, x) returns r2, we have r1 <= r2.
    Preconditions: x satisfies 1 <= x <= 8, and k1, k2 satisfy 1 <= k1 <= k2 <= 10^15. -/
  theorem spec_9 (k1 k2 x : Std.I64)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
      (r1 r2 : Std.I64)
      (hr1 : Aegis.FindMaximumNumber.find_maximum_number k1 x = ok r1)
      (hr2 : Aegis.FindMaximumNumber.find_maximum_number k2 x = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (k1 k2 x : Std.I64)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
        (r1 r2 : Std.I64)
        (hr1 : Aegis.FindMaximumNumber.find_maximum_number k1 x = ok r1)
        (hr2 : Aegis.FindMaximumNumber.find_maximum_number k2 x = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns r, r+1 is the least nonnegative integer n such that A_x(n) > k.
    Preconditions: k and x satisfy 1 <= k <= 10^15 and 1 <= x <= 8. -/
  theorem spec_10 (k x : Std.I64)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
      (r : Std.I64)
      (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r) :
      k.val < AZ x.val.toNat (r.val + 1) ∧
        ∀ n : ℤ, 0 ≤ n → n < r.val + 1 → AZ x.val.toNat n ≤ k.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (k x : Std.I64)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 15)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 8)
        (r : Std.I64)
        (hr : Aegis.FindMaximumNumber.find_maximum_number k x = ok r), k.val < AZ x.val.toNat (r.val + 1) ∧
          ∀ n : ℤ, 0 ≤ n → n < r.val + 1 → AZ x.val.toNat n ≤ k.val) := by
    sorry

  end AegisSpec.FindMaximumNumber
