import Aegis.CountDigitOne.Code.Funs

/-!
# Specifications of `Aegis.CountDigitOne.count_digit_one`

LeetCode problem `number-of-digit-one`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.CountDigitOne

namespace AegisSpec.CountDigitOne

noncomputable def ones (y : ℕ) : ℕ := {k : ℕ | y / 10 ^ k % 10 = 1}.ncard

noncomputable def prefixOnes (n : ℕ) : ℕ := (Finset.range (n + 1)).sum ones

def i64 (x : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

/-- Whenever count_digit_one returns a result r, r = sum from x=0 to n of ones(x), where for any integer y >= 0, ones(y) is the number of nonnegative integers k such that floor(y / 10^k) mod 10 = 1. Equivalently, ones(y) is the number of occurrences of the digit 1 in the ordinary decimal representation of y, with ones(0)=0.
  Preconditions: 0 <= n <= 1000000000, where n is the mathematical value of the Std.I64 parameter. -/
theorem spec_1 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    r.val = (prefixOnes n.val.toNat : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r), r.val = (prefixOnes n.val.toNat : ℤ)) := by
  sorry

/-- For every integer n with 0 <= n <= 1000000000, count_digit_one returns a result r; it does not fail, overflow, or panic.
  Preconditions: 0 <= n <= 1000000000, where n is the mathematical value of the Std.I64 parameter. -/
theorem spec_2 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000) :
    ∃ r : Std.I64, count_digit_one n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000), ∃ r : Std.I64, count_digit_one n = ok r) := by
  sorry

/-- Whenever count_digit_one returns a result r, r >= 0.
  Preconditions: 0 <= n <= 1000000000, where n is the mathematical value of the Std.I64 parameter. -/
theorem spec_3 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever count_digit_one returns a result r, r <= 900000001.
  Preconditions: 0 <= n <= 1000000000, where n is the mathematical value of the Std.I64 parameter. -/
theorem spec_4 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    r.val ≤ 900000001 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r), r.val ≤ 900000001) := by
  sorry

/-- Whenever count_digit_one returns a result r, r = 0 if and only if n = 0.
  Preconditions: 0 <= n <= 1000000000, where n is the mathematical value of the Std.I64 parameter. -/
theorem spec_5 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    r.val = 0 ↔ n.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r), r.val = 0 ↔ n.val = 0) := by
  sorry

/-- Whenever count_digit_one returns a result r, r = 0 when n = 0, and r = 1 when 1 <= n <= 9.
  Preconditions: 0 <= n <= 9. -/
theorem spec_6 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 9)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    (n.val = 0 → r.val = 0) ∧ (1 ≤ n.val → n.val ≤ 9 → r.val = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 9)
    (r : Std.I64) (hr : count_digit_one n = ok r), (n.val = 0 → r.val = 0) ∧ (1 ≤ n.val → n.val ≤ 9 → r.val = 1)) := by
  sorry

/-- Whenever count_digit_one returns a result r, r = k * 10^(k-1).
  Preconditions: 1 <= k <= 9 and n = 10^k - 1, so 0 <= n <= 1000000000. -/
theorem spec_7 (k : ℕ) (hk1 : 1 ≤ k) (hk9 : k ≤ 9)
    (n : Std.I64) (hn : n.val = (10 : ℤ) ^ k - 1)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    r.val = (k : ℤ) * (10 : ℤ) ^ (k - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (k : ℕ) (hk1 : 1 ≤ k) (hk9 : k ≤ 9)
    (n : Std.I64) (hn : n.val = (10 : ℤ) ^ k - 1)
    (r : Std.I64) (hr : count_digit_one n = ok r), r.val = (k : ℤ) * (10 : ℤ) ^ (k - 1)) := by
  sorry

/-- Whenever count_digit_one(a) returns ra and count_digit_one(b) returns rb, ra <= rb.
  Preconditions: 0 <= a <= b <= 1000000000. -/
theorem spec_8 (a b : Std.I64) (h0 : 0 ≤ a.val) (hab : a.val ≤ b.val)
    (hb : b.val ≤ 1000000000)
    (ra rb : Std.I64) (hra : count_digit_one a = ok ra) (hrb : count_digit_one b = ok rb) :
    ra.val ≤ rb.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b : Std.I64) (h0 : 0 ≤ a.val) (hab : a.val ≤ b.val)
    (hb : b.val ≤ 1000000000)
    (ra rb : Std.I64) (hra : count_digit_one a = ok ra) (hrb : count_digit_one b = ok rb), ra.val ≤ rb.val) := by
  sorry

/-- Whenever count_digit_one(n) returns rn and count_digit_one(n+1) returns rn1, rn1 = rn + ones(n+1), where ones(y) is the number of nonnegative integers k with floor(y / 10^k) mod 10 = 1.
  Preconditions: 0 <= n < 1000000000. -/
theorem spec_9 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val < 1000000000)
    (rn rn1 : Std.I64) (hrn : count_digit_one n = ok rn)
    (hrn1 : count_digit_one (i64 (n.val + 1)) = ok rn1) :
    rn1.val = rn.val + (ones (n.val + 1).toNat : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val < 1000000000)
    (rn rn1 : Std.I64) (hrn : count_digit_one n = ok rn)
    (hrn1 : count_digit_one (i64 (n.val + 1)) = ok rn1), rn1.val = rn.val + (ones (n.val + 1).toNat : ℤ)) := by
  sorry

/-- Whenever count_digit_one(10^k + m) returns r and count_digit_one(m) returns rm, r = k * 10^(k-1) + (m + 1) + rm.
  Preconditions: 1 <= k <= 9, 0 <= m < 10^k, and 10^k + m <= 1000000000. -/
theorem spec_10 (k : ℕ) (hk1 : 1 ≤ k) (hk9 : k ≤ 9)
    (m : Std.I64) (hm0 : 0 ≤ m.val) (hm : m.val < (10 : ℤ) ^ k)
    (hbound : (10 : ℤ) ^ k + m.val ≤ 1000000000)
    (r rm : Std.I64) (hr : count_digit_one (i64 ((10 : ℤ) ^ k + m.val)) = ok r)
    (hrm : count_digit_one m = ok rm) :
    r.val = (k : ℤ) * (10 : ℤ) ^ (k - 1) + (m.val + 1) + rm.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (k : ℕ) (hk1 : 1 ≤ k) (hk9 : k ≤ 9)
    (m : Std.I64) (hm0 : 0 ≤ m.val) (hm : m.val < (10 : ℤ) ^ k)
    (hbound : (10 : ℤ) ^ k + m.val ≤ 1000000000)
    (r rm : Std.I64) (hr : count_digit_one (i64 ((10 : ℤ) ^ k + m.val)) = ok r)
    (hrm : count_digit_one m = ok rm), r.val = (k : ℤ) * (10 : ℤ) ^ (k - 1) + (m.val + 1) + rm.val) := by
  sorry

/-- Whenever count_digit_one(n) returns rn and count_digit_one(10*n) returns r10n, r10n = 10 * rn + n - 9 * ones(n), where ones(y) is the number of nonnegative integers k with floor(y / 10^k) mod 10 = 1.
  Preconditions: 0 <= n <= 100000000. -/
theorem spec_11 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 100000000)
    (rn r10n : Std.I64) (hrn : count_digit_one n = ok rn)
    (hr10n : count_digit_one (i64 (10 * n.val)) = ok r10n) :
    r10n.val = 10 * rn.val + n.val - 9 * (ones n.val.toNat : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 100000000)
    (rn r10n : Std.I64) (hrn : count_digit_one n = ok rn)
    (hr10n : count_digit_one (i64 (10 * n.val)) = ok r10n), r10n.val = 10 * rn.val + n.val - 9 * (ones n.val.toNat : ℤ)) := by
  sorry

/-- Whenever count_digit_one returns a result r, r <= k * 10^(k-1).
  Preconditions: 1 <= k <= 9 and 0 <= n < 10^k. -/
theorem spec_12 (k : ℕ) (hk1 : 1 ≤ k) (hk9 : k ≤ 9)
    (n : Std.I64) (h0 : 0 ≤ n.val) (hn : n.val < (10 : ℤ) ^ k)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    r.val ≤ (k : ℤ) * (10 : ℤ) ^ (k - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (k : ℕ) (hk1 : 1 ≤ k) (hk9 : k ≤ 9)
    (n : Std.I64) (h0 : 0 ≤ n.val) (hn : n.val < (10 : ℤ) ^ k)
    (r : Std.I64) (hr : count_digit_one n = ok r), r.val ≤ (k : ℤ) * (10 : ℤ) ^ (k - 1)) := by
  sorry

/-- Whenever count_digit_one returns a result r, r is at least the number of integers x with 0 <= x <= n such that ones(x) >= 1, where ones(y) is the number of nonnegative integers k with floor(y / 10^k) mod 10 = 1.
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_13 (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r) :
    (((Finset.range (n.val.toNat + 1)).filter (fun x => 1 ≤ ones x)).card : ℤ) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 1000000000)
    (r : Std.I64) (hr : count_digit_one n = ok r), (((Finset.range (n.val.toNat + 1)).filter (fun x => 1 ≤ ones x)).card : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.CountDigitOne
