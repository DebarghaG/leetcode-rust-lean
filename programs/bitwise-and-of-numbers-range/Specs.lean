import Aegis.RangeBitwiseAnd.Code.Funs
import Mathlib.Data.Int.Bitwise

/-!
# Specifications of `Aegis.RangeBitwiseAnd.range_bitwise_and`

LeetCode problem `bitwise-and-of-numbers-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RangeBitwiseAnd

open Aegis.RangeBitwiseAnd (range_bitwise_and)

def bit (b : Nat) (y : Int) : Int := (y / (2 : Int) ^ b) % 2

def IsBitwiseAndOfRange (l r v : Int) : Prop :=
  ∀ b : Nat, bit b v = 1 ↔ ∀ x : Int, l ≤ x → x ≤ r → bit b x = 1

/-- Whenever the function returns a result r, r is the unique non-negative integer such that, for every integer b >= 0, bit_b(r) = 1 if and only if bit_b(x) = 1 for every integer x with left <= x <= right, where bit_b(y) = (y div 2^b) mod 2 for y >= 0. Equivalently, r is the bitwise AND of all integers in the inclusive range [left, right].
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_1 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) :
    0 ≤ r.val ∧ IsBitwiseAndOfRange left.val right.val r.val ∧
      ∀ v : Int, 0 ≤ v → IsBitwiseAndOfRange left.val right.val v → v = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r), 0 ≤ r.val ∧ IsBitwiseAndOfRange left.val right.val r.val ∧
      ∀ v : Int, 0 ≤ v → IsBitwiseAndOfRange left.val right.val v → v = r.val) := by
  sorry

/-- For every pair (left, right) satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_2 (left right : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647) :
    ∃ r : Std.I64, range_bitwise_and left right = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (left right : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647), ∃ r : Std.I64, range_bitwise_and left right = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= left, and therefore r <= right.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_3 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) :
    0 ≤ r.val ∧ r.val ≤ left.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r), 0 ≤ r.val ∧ r.val ≤ left.val) := by
  sorry

/-- Whenever the function returns a result r and left = right, r = left.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_4 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) (h_eq : left = right) :
    r = left := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) (h_eq : left = right), r = left) := by
  sorry

/-- Whenever the function returns a result r and there exists an integer k >= 0 such that left = 2^k and right < 2^(k+1), then r = left.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_5 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) (k : Nat)
    (h_pow : left.val = (2 : Int) ^ k) (h_lt : right.val < (2 : Int) ^ (k + 1)) :
    r = left := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) (k : Nat)
    (h_pow : left.val = (2 : Int) ^ k) (h_lt : right.val < (2 : Int) ^ (k + 1)), r = left) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k >= 0 such that r = (left div 2^k) * 2^k; that is, r is obtained from left by clearing all bits below some bit position.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_6 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) :
    ∃ k : Nat, r.val = (left.val / (2 : Int) ^ k) * (2 : Int) ^ k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r), ∃ k : Nat, r.val = (left.val / (2 : Int) ^ k) * (2 : Int) ^ k) := by
  sorry

/-- Whenever the function returns a result r, r is a bitwise subset of both endpoints: (r bitwise AND left) = r and (r bitwise AND right) = r.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_7 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) :
    Int.land r.val left.val = r.val ∧ Int.land r.val right.val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r), Int.land r.val left.val = r.val ∧ Int.land r.val right.val = r.val) := by
  sorry

/-- Whenever the function returns a result r and left < right, let h be the largest bit position at which left and right differ, i.e. bit_h(left) != bit_h(right) and bit_b(left) = bit_b(right) for every b > h, where bit_b(y) = (y div 2^b) mod 2. Then bit_b(r) = bit_b(left) for every b > h, and bit_b(r) = 0 for every b <= h.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_8 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) (h_lt : left.val < right.val) (h : Nat)
    (h_diff : bit h left.val ≠ bit h right.val)
    (h_max : ∀ b : Nat, h < b → bit b left.val = bit b right.val) :
    (∀ b : Nat, h < b → bit b r.val = bit b left.val) ∧
      ∀ b : Nat, b ≤ h → bit b r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) (h_lt : left.val < right.val) (h : Nat)
    (h_diff : bit h left.val ≠ bit h right.val)
    (h_max : ∀ b : Nat, h < b → bit b left.val = bit b right.val), (∀ b : Nat, h < b → bit b r.val = bit b left.val) ∧
      ∀ b : Nat, b ≤ h → bit b r.val = 0) := by
  sorry

/-- For every integer m with left <= m < right, whenever the function returns r on (left, right), r1 on (left, m), and r2 on (m+1, right), it holds that r = r1 bitwise AND r2.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_9 (left right m m1 r r1 r2 : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_m_left : left.val ≤ m.val) (h_m_right : m.val < right.val)
    (h_m1 : m1.val = m.val + 1)
    (h_res : range_bitwise_and left right = ok r)
    (h_res1 : range_bitwise_and left m = ok r1)
    (h_res2 : range_bitwise_and m1 right = ok r2) :
    r.val = Int.land r1.val r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (left right m m1 r r1 r2 : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_m_left : left.val ≤ m.val) (h_m_right : m.val < right.val)
    (h_m1 : m1.val = m.val + 1)
    (h_res : range_bitwise_and left right = ok r)
    (h_res1 : range_bitwise_and left m = ok r1)
    (h_res2 : range_bitwise_and m1 right = ok r2), r.val = Int.land r1.val r2.val) := by
  sorry

/-- For all integers a and b with left <= a <= b <= right, whenever the function returns r on (left, right) and s on (a, b), it holds that (r bitwise AND s) = r; in particular r <= s.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_10 (left right a b r s : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_a : left.val ≤ a.val) (h_ab : a.val ≤ b.val) (h_b : b.val ≤ right.val)
    (h_res : range_bitwise_and left right = ok r)
    (h_res' : range_bitwise_and a b = ok s) :
    Int.land r.val s.val = r.val ∧ r.val ≤ s.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (left right a b r s : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_a : left.val ≤ a.val) (h_ab : a.val ≤ b.val) (h_b : b.val ≤ right.val)
    (h_res : range_bitwise_and left right = ok r)
    (h_res' : range_bitwise_and a b = ok s), Int.land r.val s.val = r.val ∧ r.val ≤ s.val) := by
  sorry

/-- Whenever the function returns a result r, for every bit position b >= 0, if bit_b(r) = 0 then there exists an integer x with left <= x <= right such that bit_b(x) = 0, where bit_b(y) = (y div 2^b) mod 2.
  Preconditions: 0 <= left <= right <= 2147483647. -/
theorem spec_11 (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r) :
    ∀ b : Nat, bit b r.val = 0 → ∃ x : Int, left.val ≤ x ∧ x ≤ right.val ∧ bit b x = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (left right r : Std.I64)
    (h_left : 0 ≤ left.val) (h_order : left.val ≤ right.val) (h_right : right.val ≤ 2147483647)
    (h_res : range_bitwise_and left right = ok r), ∀ b : Nat, bit b r.val = 0 → ∃ x : Int, left.val ≤ x ∧ x ≤ right.val ∧ bit b x = 0) := by
  sorry

end AegisSpec.RangeBitwiseAnd
