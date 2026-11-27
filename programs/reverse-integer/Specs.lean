import Aegis.Reverse.Code.Funs

/-!
# Specifications of `Aegis.Reverse.reverse`

LeetCode problem `reverse-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Reverse

def InI32 (n : ℤ) : Prop := -2147483648 ≤ n ∧ n ≤ 2147483647

instance inI32_decidable (n : ℤ) : Decidable (InI32 n) := by
  unfold InI32
  infer_instance

def natDigits : ℕ → List ℕ
  | 0 => []
  | m + 1 => natDigits ((m + 1) / 10) ++ [(m + 1) % 10]
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos m) (by decide)

def digitsOfAbs (x : ℤ) : List ℕ :=
  if x = 0 then [0] else natDigits x.natAbs

def ofDigits (l : List ℕ) : ℕ := l.foldl (fun acc d => acc * 10 + d) 0

def rev (x : ℤ) : ℤ :=
  let r : ℤ := ↑(ofDigits (digitsOfAbs x).reverse)
  if x < 0 then -r else r

def toI64 (n : ℤ) (h : -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807) :
    Std.I64 :=
  Std.I64.ofInt n (by
    simp only [Aeneas.Std.IScalar.cMin_I64_eq]
    exact h)

def pow10I64 (k : ℕ) (hk : k ≤ 9) : Std.I64 :=
  toI64 ((10 : ℤ) ^ k) (by
    have h1 : (10 : ℤ) ^ k ≤ (10 : ℤ) ^ 9 := pow_le_pow_right₀ (by norm_num) hk
    have h0 : (0 : ℤ) ≤ (10 : ℤ) ^ k := by positivity
    norm_num at h1
    omega)

def negPow10I64 (k : ℕ) (hk : k ≤ 9) : Std.I64 :=
  toI64 (-((10 : ℤ) ^ k)) (by
    have h1 : (10 : ℤ) ^ k ≤ (10 : ℤ) ^ 9 := pow_le_pow_right₀ (by norm_num) hk
    have h0 : (0 : ℤ) ≤ (10 : ℤ) ^ k := by positivity
    norm_num at h1
    omega)

/-- Let rev(x) be the signed decimal digit reversal of x: rev(0)=0; for x != 0, write |x| in decimal without leading zeros, reverse that digit string, interpret the result as a decimal integer with leading zeros ignored, and give it the sign of x. The function returns a result r, and r = rev(x) if -2^31 <= rev(x) <= 2^31 - 1, while r = 0 if rev(x) < -2^31 or rev(x) > 2^31 - 1.
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1 (the problem's signed 32-bit input range). -/
theorem spec_1 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647) :
    ∃ r : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧ r.val = if InI32 (rev x.val) then rev x.val else 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647), ∃ r : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧ r.val = if InI32 (rev x.val) then rev x.val else 0) := by
  sorry

/-- For every x with -2^31 <= x <= 2^31 - 1, the function returns a result r (it does not fail by overflow, panic, or out-of-bounds).
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1. -/
theorem spec_2 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647) :
    ∃ r : Std.I64, Aegis.Reverse.reverse x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647), ∃ r : Std.I64, Aegis.Reverse.reverse x = ok r) := by
  sorry

/-- For every x with -2^31 <= x <= 2^31 - 1, the function returns a result r satisfying -2^31 <= r <= 2^31 - 1.
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1. -/
theorem spec_3 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647) :
    ∃ r : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧ -2147483648 ≤ r.val ∧ r.val ≤ 2147483647 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647), ∃ r : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧ -2147483648 ≤ r.val ∧ r.val ≤ 2147483647) := by
  sorry

/-- Let rev(x) be the signed decimal digit reversal of x (as defined in spec_1). For every x with -2^31 <= x <= 2^31 - 1, the function returns a result r, and r = 0 if and only if x = 0 or rev(x) < -2^31 or rev(x) > 2^31 - 1.
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1. -/
theorem spec_4 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647) :
    ∃ r : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧
        (r.val = 0 ↔ x.val = 0 ∨ rev x.val < -2147483648 ∨ 2147483647 < rev x.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647), ∃ r : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧
        (r.val = 0 ↔ x.val = 0 ∨ rev x.val < -2147483648 ∨ 2147483647 < rev x.val)) := by
  sorry

/-- For every x with -2^31 <= x <= 2^31 - 1, if the function returns a nonzero result r, then x is nonzero and r has the same sign as x: r > 0 exactly when x > 0, and r < 0 exactly when x < 0.
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1. -/
theorem spec_5 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (r : Std.I64) (hr : Aegis.Reverse.reverse x = ok r) (hrnz : r.val ≠ 0) :
    x.val ≠ 0 ∧ (0 < r.val ↔ 0 < x.val) ∧ (r.val < 0 ↔ x.val < 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (r : Std.I64) (hr : Aegis.Reverse.reverse x = ok r) (hrnz : r.val ≠ 0), x.val ≠ 0 ∧ (0 < r.val ↔ 0 < x.val) ∧ (r.val < 0 ↔ x.val < 0)) := by
  sorry

/-- For every such x, reverse(x) returns the same value as reverse(x/10).
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1 and x is divisible by 10. -/
theorem spec_6 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hx10 : 10 ∣ x.val) :
    ∃ r r' : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧
        Aegis.Reverse.reverse (toI64 (x.val / 10) (by omega)) = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hx10 : 10 ∣ x.val), ∃ r r' : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧
        Aegis.Reverse.reverse (toI64 (x.val / 10) (by omega)) = ok r' ∧ r'.val = r.val) := by
  sorry

/-- For every such k, the function returns 1 on input 10^k and returns -1 on input -10^k.
  Preconditions: k is an integer with 0 <= k <= 9. -/
theorem spec_7 (k : ℕ) (hk : k ≤ 9) :
    Aegis.Reverse.reverse (pow10I64 k hk) = ok 1#i64 ∧
      Aegis.Reverse.reverse (negPow10I64 k hk) = ok ((-1)#i64) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (k : ℕ) (hk : k ≤ 9), Aegis.Reverse.reverse (pow10I64 k hk) = ok 1#i64 ∧
      Aegis.Reverse.reverse (negPow10I64 k hk) = ok ((-1)#i64)) := by
  sorry

/-- Let s be the decimal representation of |x| without leading zeros (for x = 0, s = '0'). If s is equal to its reversal, then the function returns x.
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1. -/
theorem spec_8 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hpal : (digitsOfAbs x.val).reverse = digitsOfAbs x.val) :
    ∃ r : Std.I64, Aegis.Reverse.reverse x = ok r ∧ r.val = x.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hpal : (digitsOfAbs x.val).reverse = digitsOfAbs x.val), ∃ r : Std.I64, Aegis.Reverse.reverse x = ok r ∧ r.val = x.val) := by
  sorry

/-- Let rev(x) be the signed decimal digit reversal of x (as defined in spec_1). For every such x, the function returns rev(x).
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1 and |x| <= 999,999,999. -/
theorem spec_9 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (habs : Int.natAbs x.val ≤ 999999999) :
    ∃ r : Std.I64, Aegis.Reverse.reverse x = ok r ∧ r.val = rev x.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (habs : Int.natAbs x.val ≤ 999999999), ∃ r : Std.I64, Aegis.Reverse.reverse x = ok r ∧ r.val = rev x.val) := by
  sorry

/-- For every such x, let r be the value returned by reverse(x). Then r lies in [-2^31, 2^31 - 1] and reverse(r) returns x.
  Preconditions: x is an integer with -2^31 <= x <= 2^31 - 1, x is either 0 or not divisible by 10, and rev(x) lies in [-2^31, 2^31 - 1], where rev(x) is the signed decimal digit reversal of x (write |x| in decimal without leading zeros, reverse the digits, drop leading zeros, keep the sign of x; rev(0)=0). -/
theorem spec_10 (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hx0 : x.val = 0 ∨ ¬ 10 ∣ x.val)
    (hrev : -2147483648 ≤ rev x.val ∧ rev x.val ≤ 2147483647)
    (r : Std.I64) (hr : Aegis.Reverse.reverse x = ok r) :
    (-2147483648 ≤ r.val ∧ r.val ≤ 2147483647) ∧
      ∃ r' : Std.I64, Aegis.Reverse.reverse r = ok r' ∧ r'.val = x.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hx0 : x.val = 0 ∨ ¬ 10 ∣ x.val)
    (hrev : -2147483648 ≤ rev x.val ∧ rev x.val ≤ 2147483647)
    (r : Std.I64) (hr : Aegis.Reverse.reverse x = ok r), (-2147483648 ≤ r.val ∧ r.val ≤ 2147483647) ∧
      ∃ r' : Std.I64, Aegis.Reverse.reverse r = ok r' ∧ r'.val = x.val) := by
  sorry

/-- For every such x, the result of reverse(-x) equals the negative of the result of reverse(x); equivalently, reverse(-x) = -reverse(x).
  Preconditions: x is an integer with -2^31 < x <= 2^31 - 1 (so -x is also in the signed 32-bit range). -/
theorem spec_11 (x : Std.I64) (hx : -2147483648 < x.val ∧ x.val ≤ 2147483647) :
    ∃ r r' : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧
        Aegis.Reverse.reverse (toI64 (-x.val) (by omega)) = ok r' ∧ r'.val = -r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (x : Std.I64) (hx : -2147483648 < x.val ∧ x.val ≤ 2147483647), ∃ r r' : Std.I64,
      Aegis.Reverse.reverse x = ok r ∧
        Aegis.Reverse.reverse (toI64 (-x.val) (by omega)) = ok r' ∧ r'.val = -r.val) := by
  sorry

/-- reverse(120) returns 21.
  Preconditions: None (the concrete input is 120). -/
theorem spec_12 : Aegis.Reverse.reverse 120#i64 = ok 21#i64 := by
  sorry

theorem spec_12_neg :
    ¬ (Aegis.Reverse.reverse 120#i64 = ok 21#i64) := by
  sorry

/-- reverse(1534236469) returns 0.
  Preconditions: None (the concrete input is 1534236469). -/
theorem spec_13 : Aegis.Reverse.reverse 1534236469#i64 = ok 0#i64 := by
  sorry

theorem spec_13_neg :
    ¬ (Aegis.Reverse.reverse 1534236469#i64 = ok 0#i64) := by
  sorry

/-- reverse(-2147483412) returns -2143847412.
  Preconditions: None (the concrete input is -2147483412). -/
theorem spec_14 : Aegis.Reverse.reverse ((-2147483412)#i64) = ok ((-2143847412)#i64) := by
  sorry

theorem spec_14_neg :
    ¬ (Aegis.Reverse.reverse ((-2147483412)#i64) = ok ((-2143847412)#i64)) := by
  sorry

/-- reverse(2147483647) returns 0.
  Preconditions: None (the concrete input is 2147483647). -/
theorem spec_15 : Aegis.Reverse.reverse 2147483647#i64 = ok 0#i64 := by
  sorry

theorem spec_15_neg :
    ¬ (Aegis.Reverse.reverse 2147483647#i64 = ok 0#i64) := by
  sorry

/-- reverse(-2147483648) returns 0.
  Preconditions: None (the concrete input is -2147483648). -/
theorem spec_16 : Aegis.Reverse.reverse ((-2147483648)#i64) = ok 0#i64 := by
  sorry

theorem spec_16_neg :
    ¬ (Aegis.Reverse.reverse ((-2147483648)#i64) = ok 0#i64) := by
  sorry

end AegisSpec.Reverse
