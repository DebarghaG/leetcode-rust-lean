import Aegis.IsPalindrome.Code.Funs

/-!
# Specifications of `Aegis.IsPalindrome.is_palindrome`

LeetCode problem `palindrome-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsPalindrome

def digitsRev (n : Nat) : List Nat :=
  if h : n = 0 then [] else n % 10 :: digitsRev (n / 10)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def digitsNat (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | _ => (digitsRev n).reverse

def digits (n : Int) : List Nat := digitsNat n.toNat

def ofDigitsRev : List Nat → Nat
  | [] => 0
  | d :: l => d + 10 * ofDigitsRev l

def reverseValue (n : Int) : Nat := ofDigitsRev (digits n)

def PalindromicDigits (d : List Nat) : Prop :=
  ∀ i, i < d.length → d[i]? = d[d.length - 1 - i]?

/-- Let n be the integer value of x. The function returns a result r and does not fail. If n < 0, then r = false. If n >= 0, let d be the sequence of decimal digits of n in the usual order, most significant first, with no leading zeros, and let d = [0] when n = 0. Then r = true if and only if for every index i with 0 <= i < len(d), d[i] = d[len(d)-1-i]; otherwise r = false.
  Preconditions: x : Std.I64 with integer value n satisfying -2147483648 <= n <= 2147483647. -/
theorem spec_1 (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647) :
    ∃ r, Aegis.IsPalindrome.is_palindrome x = ok r ∧
      (x.val < 0 → r = false) ∧
      (0 ≤ x.val → (r = true ↔ PalindromicDigits (digits x.val))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647), ∃ r, Aegis.IsPalindrome.is_palindrome x = ok r ∧
      (x.val < 0 → r = false) ∧
      (0 ≤ x.val → (r = true ↔ PalindromicDigits (digits x.val)))) := by
  sorry

/-- For every x satisfying the preconditions, the function returns a result (a Bool) rather than failing; it does not overflow, panic, or get stuck.
  Preconditions: Let n be the integer value of x. The problem constraint is -2147483648 <= n <= 2147483647. -/
theorem spec_2 (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647) :
    ∃ r, Aegis.IsPalindrome.is_palindrome x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647), ∃ r, Aegis.IsPalindrome.is_palindrome x = ok r) := by
  sorry

/-- For every x satisfying the preconditions whose integer value n satisfies n >= 0, let d be the sequence of decimal digits of n, most significant first, with no leading zeros (and d = [0] if n = 0). Whenever the function returns a result r and r = true, it holds that for every index i with 0 <= i < len(d), d[i] = d[len(d)-1-i].
  Preconditions: Let n be the integer value of x. The problem constraint is -2147483648 <= n <= 2147483647. -/
theorem spec_3 (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : 0 ≤ x.val) :
    ∀ r, Aegis.IsPalindrome.is_palindrome x = ok r → r = true →
      PalindromicDigits (digits x.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : 0 ≤ x.val), ∀ r, Aegis.IsPalindrome.is_palindrome x = ok r → r = true →
      PalindromicDigits (digits x.val)) := by
  sorry

/-- For every x satisfying the preconditions whose integer value n satisfies n >= 0, let d be the sequence of decimal digits of n, most significant first, with no leading zeros (and d = [0] if n = 0). If for every index i with 0 <= i < len(d), d[i] = d[len(d)-1-i], then whenever the function returns a result r, we have r = true.
  Preconditions: Let n be the integer value of x. The problem constraint is -2147483648 <= n <= 2147483647. -/
theorem spec_4 (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : 0 ≤ x.val)
    (hpal : PalindromicDigits (digits x.val)) :
    ∀ r, Aegis.IsPalindrome.is_palindrome x = ok r → r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : 0 ≤ x.val)
    (hpal : PalindromicDigits (digits x.val)), ∀ r, Aegis.IsPalindrome.is_palindrome x = ok r → r = true) := by
  sorry

/-- For every x satisfying the preconditions whose integer value n satisfies n = 0 or (n > 0 and n mod 10 != 0), let d be the sequence of decimal digits of n, most significant first, with no leading zeros (and d = [0] if n = 0). Let m be the integer whose decimal representation (with no leading zeros) is d[len(d)-1], d[len(d)-2], ..., d[0]. Assume -2147483648 <= m <= 2147483647, and let y be the Std.I64 value representing m. Whenever the function returns a result r on x and a result r' on y, we have r = r'.
  Preconditions: Let n be the integer value of x. The problem constraint is -2147483648 <= n <= 2147483647. -/
theorem spec_5 (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : x.val = 0 ∨ (0 < x.val ∧ x.val % 10 ≠ 0))
    (hm_lo : (-2147483648 : Int) ≤ (reverseValue x.val : Int))
    (hm_hi : (reverseValue x.val : Int) ≤ 2147483647)
    (y : Std.I64) (hy : y.val = (reverseValue x.val : Int)) :
    ∀ r r', Aegis.IsPalindrome.is_palindrome x = ok r →
      Aegis.IsPalindrome.is_palindrome y = ok r' → r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : x.val = 0 ∨ (0 < x.val ∧ x.val % 10 ≠ 0))
    (hm_lo : (-2147483648 : Int) ≤ (reverseValue x.val : Int))
    (hm_hi : (reverseValue x.val : Int) ≤ 2147483647)
    (y : Std.I64) (hy : y.val = (reverseValue x.val : Int)), ∀ r r', Aegis.IsPalindrome.is_palindrome x = ok r →
      Aegis.IsPalindrome.is_palindrome y = ok r' → r = r') := by
  sorry

/-- For every x satisfying the preconditions whose integer value n satisfies n >= 0, let d be the sequence of decimal digits of n, most significant first, with no leading zeros (and d = [0] if n = 0). Let m be the integer obtained by reading the reversed sequence d[len(d)-1], d[len(d)-2], ..., d[0] in decimal and dropping any leading zeros (so m = 0 when n = 0). Whenever the function returns a result r and r = true, we have n = m.
  Preconditions: Let n be the integer value of x. The problem constraint is -2147483648 <= n <= 2147483647. -/
theorem spec_6 (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : 0 ≤ x.val) :
    ∀ r, Aegis.IsPalindrome.is_palindrome x = ok r → r = true →
      x.val = (reverseValue x.val : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (x : Std.I64)
    (hbound : (-2147483648 : Int) ≤ x.val ∧ x.val ≤ 2147483647)
    (hn : 0 ≤ x.val), ∀ r, Aegis.IsPalindrome.is_palindrome x = ok r → r = true →
      x.val = (reverseValue x.val : Int)) := by
  sorry

end AegisSpec.IsPalindrome
