import Aegis.CountBalls.Code.Funs

/-!
# Specifications of `Aegis.CountBalls.count_balls`

LeetCode problem `maximum-number-of-balls-in-a-box`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountBalls

namespace AegisSpec.CountBalls

def digitsRev (n : ℕ) : List ℕ :=
  if h : n = 0 then [] else n % 10 :: digitsRev (n / 10)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def digitSum (n : ℕ) : ℕ := (digitsRev n).sum

def numDigits (n : ℕ) : ℕ := (digitsRev n).length

def intRange (low high : ℤ) : List ℤ :=
  (List.range (high - low + 1).toNat).map (fun k => low + (k : ℤ))

def count (low high : ℤ) (b : ℤ) : ℕ :=
  (intRange low high).countP (fun x => decide ((digitSum x.toNat : ℤ) = b))

def IsMaxCount (low high : ℤ) (r : ℕ) : Prop :=
  (∀ b : ℤ, 1 ≤ b → count low high b ≤ r) ∧ ∃ b : ℤ, 1 ≤ b ∧ count low high b = r

def i64OfInt (n : ℤ) : Std.I64 :=
  if h : Std.IScalar.cMin Std.IScalarTy.I64 ≤ n ∧ n ≤ Std.IScalar.cMax Std.IScalarTy.I64 then
    Std.IScalar.ofInt n h
  else 0#i64

/-- Whenever the function returns a result r, r = max { count(b) | b is an integer with b >= 1 }.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000. For a positive integer n, let digit_sum(n) be the sum of the decimal digits of n written without leading zeros. For each integer b >= 1, let count(b) be the number of integers x such that lowLimit <= x <= highLimit and digit_sum(x) = b. -/
theorem spec_1 (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r) :
    IsMaxCount lowLimit.val highLimit.val r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r), IsMaxCount lowLimit.val highLimit.val r.val.toNat) := by
  sorry

/-- The function returns a result r; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000. -/
theorem spec_2 (lowLimit highLimit : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000) :
    ∃ r : Std.I64, count_balls lowLimit highLimit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (lowLimit highLimit : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000), ∃ r : Std.I64, count_balls lowLimit highLimit = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000. -/
theorem spec_3 (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= highLimit - lowLimit + 1.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000. -/
theorem spec_4 (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r) :
    r.val ≤ highLimit.val - lowLimit.val + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r), r.val ≤ highLimit.val - lowLimit.val + 1) := by
  sorry

/-- Whenever the function returns a result r, for every integer b >= 1, count(b) <= r.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000. For a positive integer n, let digit_sum(n) be the sum of the decimal digits of n. For each integer b >= 1, let count(b) be the number of integers x such that lowLimit <= x <= highLimit and digit_sum(x) = b. -/
theorem spec_5 (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r) :
    ∀ b : ℤ, 1 ≤ b → (count lowLimit.val highLimit.val b : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r), ∀ b : ℤ, 1 ≤ b → (count lowLimit.val highLimit.val b : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer b >= 1 such that count(b) = r; equivalently, there exists an integer x with lowLimit <= x <= highLimit such that count(digit_sum(x)) = r.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000. For a positive integer n, let digit_sum(n) be the sum of the decimal digits of n. For each integer b >= 1, let count(b) be the number of integers x such that lowLimit <= x <= highLimit and digit_sum(x) = b. -/
theorem spec_6 (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r) :
    (∃ b : ℤ, 1 ≤ b ∧ count lowLimit.val highLimit.val b = r.val.toNat) ∧
      (∃ x : ℤ, lowLimit.val ≤ x ∧ x ≤ highLimit.val ∧
        count lowLimit.val highLimit.val ((digitSum x.toNat : ℕ) : ℤ) = r.val.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r), (∃ b : ℤ, 1 ≤ b ∧ count lowLimit.val highLimit.val b = r.val.toNat) ∧
      (∃ x : ℤ, lowLimit.val ≤ x ∧ x ≤ highLimit.val ∧
        count lowLimit.val highLimit.val ((digitSum x.toNat : ℕ) : ℤ) = r.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer b such that 1 <= b <= 9*d and count(b) = r.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000. Let d be the number of decimal digits of highLimit. For a positive integer n, let digit_sum(n) be the sum of the decimal digits of n. For each integer b >= 1, let count(b) be the number of integers x such that lowLimit <= x <= highLimit and digit_sum(x) = b. -/
theorem spec_7 (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r) :
    ∃ b : ℤ, 1 ≤ b ∧ b ≤ 9 * ((numDigits highLimit.val.toNat : ℕ) : ℤ) ∧
      count lowLimit.val highLimit.val b = r.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r), ∃ b : ℤ, 1 ≤ b ∧ b ≤ 9 * ((numDigits highLimit.val.toNat : ℕ) : ℤ) ∧
      count lowLimit.val highLimit.val b = r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit <= 100000, and lowLimit = highLimit. -/
theorem spec_8 (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000) (heq : lowLimit.val = highLimit.val)
    (hr : count_balls lowLimit highLimit = ok r) :
    r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (lowLimit highLimit r : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val ≤ 100000) (heq : lowLimit.val = highLimit.val)
    (hr : count_balls lowLimit highLimit = ok r), r.val = 1) := by
  sorry

/-- Whenever count_balls(lowLimit, highLimit) returns r1 and count_balls(lowLimit, highLimit + 1) returns r2, we have r1 <= r2.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit <= highLimit < 100000. -/
theorem spec_9 (lowLimit highLimit r1 r2 : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val < 100000)
    (hr1 : count_balls lowLimit highLimit = ok r1)
    (hr2 : count_balls lowLimit (i64OfInt (highLimit.val + 1)) = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (lowLimit highLimit r1 r2 : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hle : lowLimit.val ≤ highLimit.val)
    (hhigh : highLimit.val < 100000)
    (hr1 : count_balls lowLimit highLimit = ok r1)
    (hr2 : count_balls lowLimit (i64OfInt (highLimit.val + 1)) = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever count_balls(lowLimit, highLimit) returns r1 and count_balls(lowLimit + 1, highLimit) returns r2, we have r2 <= r1.
  Preconditions: Interpreting lowLimit and highLimit as integers, 1 <= lowLimit < highLimit <= 100000. -/
theorem spec_10 (lowLimit highLimit r1 r2 : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hlt : lowLimit.val < highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr1 : count_balls lowLimit highLimit = ok r1)
    (hr2 : count_balls (i64OfInt (lowLimit.val + 1)) highLimit = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (lowLimit highLimit r1 r2 : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hlt : lowLimit.val < highLimit.val)
    (hhigh : highLimit.val ≤ 100000)
    (hr1 : count_balls lowLimit highLimit = ok r1)
    (hr2 : count_balls (i64OfInt (lowLimit.val + 1)) highLimit = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever count_balls(lowLimit, highLimit) returns r, count_balls(lowLimit, mid) returns r1, and count_balls(mid + 1, highLimit) returns r2, we have r <= r1 + r2.
  Preconditions: Interpreting lowLimit, mid, and highLimit as integers, 1 <= lowLimit <= mid < highLimit <= 100000. -/
theorem spec_11 (lowLimit mid highLimit r r1 r2 : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hmid1 : lowLimit.val ≤ mid.val)
    (hmid2 : mid.val < highLimit.val) (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r)
    (hr1 : count_balls lowLimit mid = ok r1)
    (hr2 : count_balls (i64OfInt (mid.val + 1)) highLimit = ok r2) :
    r.val ≤ r1.val + r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (lowLimit mid highLimit r r1 r2 : Std.I64)
    (hlow : 1 ≤ lowLimit.val) (hmid1 : lowLimit.val ≤ mid.val)
    (hmid2 : mid.val < highLimit.val) (hhigh : highLimit.val ≤ 100000)
    (hr : count_balls lowLimit highLimit = ok r)
    (hr1 : count_balls lowLimit mid = ok r1)
    (hr2 : count_balls (i64OfInt (mid.val + 1)) highLimit = ok r2), r.val ≤ r1.val + r2.val) := by
  sorry

end AegisSpec.CountBalls
