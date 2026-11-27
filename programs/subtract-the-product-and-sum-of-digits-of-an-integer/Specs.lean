import Aegis.SubtractProductAndSum.Code.Funs

/-!
# Specifications of `Aegis.SubtractProductAndSum.subtract_product_and_sum`

LeetCode problem `subtract-the-product-and-sum-of-digits-of-an-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubtractProductAndSum

def digitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => if n = 0 then [] else n % 10 :: digitsAux k (n / 10)

def decimalDigits (n : Nat) : List Nat := (digitsAux n n).reverse

def digitSum (n : Nat) : Nat := (decimalDigits n).sum

def digitProduct (n : Nat) : Nat := (decimalDigits n).prod

def digitLength (n : Nat) : Nat := (decimalDigits n).length

def digitSumInt (n : Int) : Int := (digitSum n.toNat : Int)

def digitProductInt (n : Int) : Int := (digitProduct n.toNat : Int)

def sameDigits (n m : Nat) : Prop := (decimalDigits n).Perm (decimalDigits m)

def oneZeroFourNines (n : Nat) : Prop :=
  digitLength n = 5 ∧ (decimalDigits n).Perm [0, 9, 9, 9, 9]

/-- Let P(n) be the product and S(n) the sum of the decimal digits of n (written in base 10 in canonical form without leading zeros; for n = 100000 the digits are 1,0,0,0,0,0). Whenever the function returns a result r, r = P(n) - S(n).
  Preconditions: 1 <= n <= 100000. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    r.val = digitProductInt n.val - digitSumInt n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), r.val = digitProductInt n.val - digitSumInt n.val) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= n <= 100000. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∃ r : Std.I64, Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∃ r : Std.I64, Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) := by
  sorry

/-- Whenever the function returns a result r, -36 <= r <= 59004.
  Preconditions: 1 <= n <= 100000. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    -36 ≤ r.val ∧ r.val ≤ 59004 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), -36 ≤ r.val ∧ r.val ≤ 59004) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 1 <= n <= 9. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 9)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 9)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), r.val = 0) := by
  sorry

/-- Let S(n) be the sum of the decimal digits of n. Whenever the function returns a result r, r = -S(n).
  Preconditions: 1 <= n <= 100000 and the canonical decimal representation of n contains at least one digit 0. -/
theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (h0 : 0 ∈ decimalDigits n.val.toNat)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    r.val = -digitSumInt n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (h0 : 0 ∈ decimalDigits n.val.toNat)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), r.val = -digitSumInt n.val) := by
  sorry

/-- Whenever the function returns r for input n and r' for input m, r = r'.
  Preconditions: 1 <= n <= 100000, 1 <= m <= 100000, and the canonical decimal representations of n and m have the same multiset of digits. -/
theorem spec_6 (n m : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hd : sameDigits n.val.toNat m.val.toNat)
    (r r' : Std.I64)
    (hr : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r)
    (hr' : Aegis.SubtractProductAndSum.subtract_product_and_sum m = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n m : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hd : sameDigits n.val.toNat m.val.toNat)
    (r r' : Std.I64)
    (hr : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r)
    (hr' : Aegis.SubtractProductAndSum.subtract_product_and_sum m = ok r'), r.val = r'.val) := by
  sorry

/-- Let P(q) and S(q) be the product and sum of the decimal digits of q. Whenever the function returns a result r for n, r = d * P(q) - S(q) - d.
  Preconditions: 10 <= n <= 100000. Let q = n div 10 and d = n mod 10, so q >= 1 and 0 <= d <= 9. -/
theorem spec_7 (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 100000)
    (q d : Int) (hq : q = n.val / 10) (hd : d = n.val % 10)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    r.val = d * digitProductInt q - digitSumInt q - d := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 100000)
    (q d : Int) (hq : q = n.val / 10) (hd : d = n.val % 10)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), r.val = d * digitProductInt q - digitSumInt q - d) := by
  sorry

/-- Whenever the function returns a result r for n, r = d^k - k*d.
  Preconditions: 1 <= k <= 5, 1 <= d <= 9, and n = d * (10^k - 1) / 9. -/
theorem spec_8 (k d : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 5) (hd1 : 1 ≤ d) (hd2 : d ≤ 9)
    (n : Std.I64) (hn : n.val = (d : Int) * ((10 : Int) ^ k - 1) / 9)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    r.val = (d : Int) ^ k - (k : Int) * (d : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (k d : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 5) (hd1 : 1 ≤ d) (hd2 : d ≤ 9)
    (n : Std.I64) (hn : n.val = (d : Int) * ((10 : Int) ^ k - 1) / 9)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), r.val = (d : Int) ^ k - (k : Int) * (d : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = -36 if and only if the canonical decimal representation of n has length 5 and consists of one digit 0 and four digits 9.
  Preconditions: 1 <= n <= 100000. -/
theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    r.val = -36 ↔ oneZeroFourNines n.val.toNat := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), r.val = -36 ↔ oneZeroFourNines n.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, r = 59004 if and only if n = 99999.
  Preconditions: 1 <= n <= 100000. -/
theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r) :
    r.val = 59004 ↔ n.val = 99999 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (r : Std.I64)
    (h : Aegis.SubtractProductAndSum.subtract_product_and_sum n = ok r), r.val = 59004 ↔ n.val = 99999) := by
  sorry

end AegisSpec.SubtractProductAndSum
