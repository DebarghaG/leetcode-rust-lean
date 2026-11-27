import Aegis.MakeIntegerBeautiful.Code.Funs

/-!
# Specifications of `Aegis.MakeIntegerBeautiful.make_integer_beautiful`

LeetCode problem `minimum-addition-to-make-integer-beautiful`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MakeIntegerBeautiful

  namespace AegisSpec.MakeIntegerBeautiful

  def dsNat (m : Nat) : Nat :=
    if m = 0 then 0 else m % 10 + dsNat (m / 10)
  termination_by m
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by decide)

  def ds (m : Int) : Int := (dsNat m.natAbs : Int)

  def IsLeastPow10 (n p : Int) : Prop :=
    ∃ k : Nat, p = (10 : Int) ^ k ∧ n ≤ p ∧ ∀ j : Nat, n ≤ (10 : Int) ^ j → p ≤ (10 : Int) ^ j

  /-- The function returns a result r such that r >= 0, ds(n + r) <= target, and for every integer y with 0 <= y < r, ds(n + y) > target, where ds(m) denotes the sum of the decimal digits of the nonnegative integer m.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_1
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150) :
    ∃ r : Std.I64,
      make_integer_beautiful n target = ok r ∧
        0 ≤ r.val ∧
          ds (n.val + r.val) ≤ target.val ∧
            ∀ y : Int, 0 ≤ y → y < r.val → target.val < ds (n.val + y) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150), ∃ r : Std.I64,
        make_integer_beautiful n target = ok r ∧
          0 ≤ r.val ∧
            ds (n.val + r.val) ≤ target.val ∧
              ∀ y : Int, 0 ≤ y → y < r.val → target.val < ds (n.val + y)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every n and target satisfying the preconditions.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_2
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150) :
    ∃ r : Std.I64, make_integer_beautiful n target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150), ∃ r : Std.I64, make_integer_beautiful n target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have n + r <= 10^12 (equivalently, r <= 10^12 - n).
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_3
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) :
    n.val + r.val ≤ 10 ^ 12 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r), n.val + r.val ≤ 10 ^ 12) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if ds(n) <= target, where ds(m) denotes the sum of the decimal digits of the nonnegative integer m.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_4
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) :
    r.val = 0 ↔ ds n.val ≤ target.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r), r.val = 0 ↔ ds n.val ≤ target.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, the integer n + r is divisible by 10.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_5
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) (hr_pos : 0 < r.val) :
    (10 : Int) ∣ n.val + r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r) (hr_pos : 0 < r.val), (10 : Int) ∣ n.val + r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = p - n, where p is the least power of 10 with p >= n (i.e., the least integer of the form 10^k, k >= 0, such that p >= n).
    Preconditions: 1 <= n <= 10^12 and target = 1. -/
  theorem spec_6
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht : target.val = 1)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r)
    (p : Int) (hp : IsLeastPow10 n.val p) :
    r.val = p - n.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht : target.val = 1)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r)
      (p : Int) (hp : IsLeastPow10 n.val p), r.val = p - n.val) := by
    sorry

  /-- Whenever the function returns a result r: if n <= target then r = 0; otherwise r = 10 - n.
    Preconditions: 1 <= n <= 9 and 1 <= target <= 150. -/
  theorem spec_7
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) :
    r.val = if n.val ≤ target.val then 0 else 10 - n.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r), r.val = if n.val ≤ target.val then 0 else 10 - n.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: 1 <= n <= 10^12 and 108 <= target <= 150. -/
  theorem spec_8
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 108 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) :
    r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 108 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k >= 0, if 10^k divides n then 10^k divides r.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_9
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) :
    ∀ k : Nat, (10 : Int) ^ k ∣ n.val → (10 : Int) ^ k ∣ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r), ∀ k : Nat, (10 : Int) ^ k ∣ n.val → (10 : Int) ^ k ∣ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, let k be the largest nonnegative integer such that 10^k divides n + r. Then r < 10^k.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_10
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) (hr_pos : 0 < r.val)
    (k : Nat) (hk_dvd : (10 : Int) ^ k ∣ n.val + r.val)
    (hk_max : ∀ j : Nat, (10 : Int) ^ j ∣ n.val + r.val → j ≤ k) :
    r.val < (10 : Int) ^ k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r) (hr_pos : 0 < r.val)
      (k : Nat) (hk_dvd : (10 : Int) ^ k ∣ n.val + r.val)
      (hk_max : ∀ j : Nat, (10 : Int) ^ j ∣ n.val + r.val → j ≤ k), r.val < (10 : Int) ^ k) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, ds(n + r) < ds(n), where ds(m) denotes the sum of the decimal digits of the nonnegative integer m.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_11
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) (hr_pos : 0 < r.val) :
    ds (n.val + r.val) < ds n.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r) (hr_pos : 0 < r.val), ds (n.val + r.val) < ds n.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= p - n, where p is the least power of 10 with p >= n (i.e., the least integer of the form 10^k, k >= 0, such that p >= n).
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_12
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r)
    (p : Int) (hp : IsLeastPow10 n.val p) :
    r.val ≤ p - n.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r)
      (p : Int) (hp : IsLeastPow10 n.val p), r.val ≤ p - n.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k >= 1, if ds(n) > target and 10^k divides n, then r >= 10^k, where ds(m) denotes the sum of the decimal digits of the nonnegative integer m.
    Preconditions: 1 <= n <= 10^12 and 1 <= target <= 150. -/
  theorem spec_13
    (n target : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
    (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
    (r : Std.I64) (hr : make_integer_beautiful n target = ok r) :
    ∀ k : Nat, 1 ≤ k → target.val < ds n.val → (10 : Int) ^ k ∣ n.val →
      (10 : Int) ^ k ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n target : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 12)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 150)
      (r : Std.I64) (hr : make_integer_beautiful n target = ok r), ∀ k : Nat, 1 ≤ k → target.val < ds n.val → (10 : Int) ^ k ∣ n.val →
        (10 : Int) ^ k ≤ r.val) := by
    sorry

  end AegisSpec.MakeIntegerBeautiful
