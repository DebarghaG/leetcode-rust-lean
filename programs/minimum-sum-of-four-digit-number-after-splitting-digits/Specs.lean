import Aegis.MinimumSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumSum.minimum_sum`

LeetCode problem `minimum-sum-of-four-digit-number-after-splitting-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumSum

def digits (n : Int) : List Int :=
  [n / 1000 % 10, n / 100 % 10, n / 10 % 10, n % 10]

def SortedDigits (n : Int) (a b c d : Int) : Prop :=
  a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ ([a, b, c, d] : List Int).Perm (digits n)

def twoDigitDigits (x : Int) : List Int :=
  [x / 10, x % 10]

def ofDigits (l : List Int) : Int :=
  l.foldl (fun acc d => acc * 10 + d) 0

/-- Let a,b,c,d be the four decimal digits of num ordered so that a <= b <= c <= d (as a multiset, these are exactly the digits of num). Whenever minimum_sum(num) returns a result r, r = 10*(a + b) + (c + d).
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_1 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
        r.val = 10 * (a + b) + (c + d) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
        r.val = 10 * (a + b) + (c + d)) := by
  sorry

/-- For every integer num with 1000 <= num <= 9999, minimum_sum(num) returns a result r; it does not fail, overflow, panic, or access an out-of-range index.
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_2 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∃ r, Aegis.MinimumSum.minimum_sum num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∃ r, Aegis.MinimumSum.minimum_sum num = ok r) := by
  sorry

/-- Let a,b,c,d be the four decimal digits of num ordered nondecreasingly. Whenever minimum_sum(num) returns r, r >= 1.
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_3 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → 1 ≤ r.val) := by
  sorry

/-- Let a,b,c,d be the four decimal digits of num ordered nondecreasingly. Whenever minimum_sum(num) returns r, r <= 198.
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_4 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → r.val ≤ 198 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → r.val ≤ 198) := by
  sorry

/-- Let a,b,c,d be the four decimal digits of num ordered nondecreasingly. Whenever minimum_sum(num) returns r, r >= a + b + c + d.
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_5 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
        a + b + c + d ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
        a + b + c + d ≤ r.val) := by
  sorry

/-- Whenever minimum_sum(num) returns r, r is congruent to num modulo 9.
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_6 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → r.val ≡ num.val [ZMOD 9] := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → r.val ≡ num.val [ZMOD 9]) := by
  sorry

/-- Whenever minimum_sum(num) returns r, there exist integers x and y with 0 <= x <= 99 and 0 <= y <= 99 such that r = x + y and the multiset of the four digits in the two-digit zero-padded decimal representations of x and y (for example 4 is written 04) is exactly the multiset of the four decimal digits of num.
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_7 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
      ∃ x y : Int, 0 ≤ x ∧ x ≤ 99 ∧ 0 ≤ y ∧ y ≤ 99 ∧ r.val = x + y ∧
        (twoDigitDigits x ++ twoDigitDigits y).Perm (digits num.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
      ∃ x y : Int, 0 ≤ x ∧ x ≤ 99 ∧ 0 ≤ y ∧ y ≤ 99 ∧ r.val = x + y ∧
        (twoDigitDigits x ++ twoDigitDigits y).Perm (digits num.val)) := by
  sorry

/-- Whenever minimum_sum(num) returns r, for every pair (x,y) of nonnegative integers that can be obtained by partitioning the multiset of the four decimal digits of num into two multisets A and B and writing the digits of A in some order, possibly with leading zeros, as x and the digits of B in some order, possibly with leading zeros, as y (with an empty multiset representing 0), we have r <= x + y.
  Preconditions: num is an integer with 1000 <= num <= 9999. -/
theorem spec_8 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999) :
    ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
      ∀ (A B : List Int), (A ++ B).Perm (digits num.val) →
        r.val ≤ ofDigits A + ofDigits B := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999), ∀ r, Aegis.MinimumSum.minimum_sum num = ok r →
      ∀ (A B : List Int), (A ++ B).Perm (digits num.val) →
        r.val ≤ ofDigits A + ofDigits B) := by
  sorry

/-- Whenever minimum_sum(num1) returns r1 and minimum_sum(num2) returns r2, r1 = r2.
  Preconditions: num1 and num2 are integers with 1000 <= num1 <= 9999 and 1000 <= num2 <= 9999, and the multiset of the four decimal digits of num1 equals the multiset of the four decimal digits of num2. -/
theorem spec_9 (num1 num2 : Std.I64)
    (hlo1 : 1000 ≤ num1.val) (hhi1 : num1.val ≤ 9999)
    (hlo2 : 1000 ≤ num2.val) (hhi2 : num2.val ≤ 9999)
    (hperm : (digits num1.val).Perm (digits num2.val)) :
    ∀ r1 r2, Aegis.MinimumSum.minimum_sum num1 = ok r1 →
      Aegis.MinimumSum.minimum_sum num2 = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (hlo1 : 1000 ≤ num1.val) (hhi1 : num1.val ≤ 9999)
    (hlo2 : 1000 ≤ num2.val) (hhi2 : num2.val ≤ 9999)
    (hperm : (digits num1.val).Perm (digits num2.val)), ∀ r1 r2, Aegis.MinimumSum.minimum_sum num1 = ok r1 →
      Aegis.MinimumSum.minimum_sum num2 = ok r2 → r1.val = r2.val) := by
  sorry

/-- Whenever minimum_sum(num1) returns r1 and minimum_sum(num2) returns r2, r1 <= r2.
  Preconditions: num1 and num2 are integers with 1000 <= num1 <= 9999 and 1000 <= num2 <= 9999. Let a1 <= b1 <= c1 <= d1 be the sorted digits of num1 and a2 <= b2 <= c2 <= d2 be the sorted digits of num2, and assume a1 <= a2, b1 <= b2, c1 <= c2, d1 <= d2. -/
theorem spec_10 (num1 num2 : Std.I64)
    (hlo1 : 1000 ≤ num1.val) (hhi1 : num1.val ≤ 9999)
    (hlo2 : 1000 ≤ num2.val) (hhi2 : num2.val ≤ 9999) :
    ∀ (a1 b1 c1 d1 a2 b2 c2 d2 : Int),
      SortedDigits num1.val a1 b1 c1 d1 → SortedDigits num2.val a2 b2 c2 d2 →
      a1 ≤ a2 → b1 ≤ b2 → c1 ≤ c2 → d1 ≤ d2 →
      ∀ r1 r2, Aegis.MinimumSum.minimum_sum num1 = ok r1 →
        Aegis.MinimumSum.minimum_sum num2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (hlo1 : 1000 ≤ num1.val) (hhi1 : num1.val ≤ 9999)
    (hlo2 : 1000 ≤ num2.val) (hhi2 : num2.val ≤ 9999), ∀ (a1 b1 c1 d1 a2 b2 c2 d2 : Int),
      SortedDigits num1.val a1 b1 c1 d1 → SortedDigits num2.val a2 b2 c2 d2 →
      a1 ≤ a2 → b1 ≤ b2 → c1 ≤ c2 → d1 ≤ d2 →
      ∀ r1 r2, Aegis.MinimumSum.minimum_sum num1 = ok r1 →
        Aegis.MinimumSum.minimum_sum num2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Let a,b,c,d be the four decimal digits of num ordered nondecreasingly. Whenever minimum_sum(num) returns r, r >= 22.
  Preconditions: num is an integer with 1000 <= num <= 9999, and none of its four decimal digits is 0. -/
theorem spec_11 (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999)
    (hnozero : ∀ k ∈ digits num.val, k ≠ 0) :
    ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → 22 ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num : Std.I64) (hlo : 1000 ≤ num.val) (hhi : num.val ≤ 9999)
    (hnozero : ∀ k ∈ digits num.val, k ≠ 0), ∀ (a b c d : Int), SortedDigits num.val a b c d →
      ∀ r, Aegis.MinimumSum.minimum_sum num = ok r → 22 ≤ r.val) := by
  sorry

end AegisSpec.MinimumSum
