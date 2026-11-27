import Aegis.LargestPalindrome.Code.Funs

/-!
# Specifications of `Aegis.LargestPalindrome.largest_palindrome`

LeetCode problem `largest-palindrome-product`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LargestPalindrome

def IsNDigit (k : ℤ) (d : ℤ) : Prop :=
  (10 : ℤ) ^ (k - 1).toNat ≤ d ∧ d ≤ (10 : ℤ) ^ k.toNat - 1

def decDigits (m : ℕ) : List ℕ :=
  match m with
  | 0 => []
  | k + 1 => (k + 1) % 10 :: decDigits ((k + 1) / 10)
termination_by m
decreasing_by omega

def decRepr (m : ℕ) : List ℕ := (decDigits m).reverse

def Palindromic (d : ℤ) : Prop :=
  0 < d ∧ ∃ m : ℕ, d = (m : ℤ) ∧ decRepr m = (decRepr m).reverse

def IsLeastNonnegRemainder (P r : ℤ) : Prop :=
  0 ≤ r ∧ r < 1337 ∧ (1337 : ℤ) ∣ P - r

def IsLargestPalindromicProduct (k : ℤ) (P : ℤ) : Prop :=
  (∃ a b : ℤ, IsNDigit k a ∧ IsNDigit k b ∧ P = a * b ∧ Palindromic P) ∧
    ∀ c d : ℤ, IsNDigit k c → IsNDigit k d → Palindromic (c * d) → c * d ≤ P

/-- The function returns a result r and there exists an integer P such that: (a) P = a*b for some n-digit integers a and b; (b) P is palindromic; (c) r is the least nonnegative remainder of P modulo 1337, so 0 <= r < 1337 and 1337 divides P - r; and (d) for every n-digit integers c and d, if Q = c*d is palindromic, then Q <= P.
  Preconditions: n is the integer value of the Lean Std.I64 parameter n, and 1 <= n <= 8. Call an integer d n-digit if 10^(n-1) <= d <= 10^n - 1. Call a positive integer palindromic if its usual decimal representation without leading zeros equals its reverse. -/
theorem spec_1 (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8) :
    ∃ r : Std.I64,
      Aegis.LargestPalindrome.largest_palindrome n = .ok r ∧
        ∃ P : ℤ,
          (∃ a b : ℤ, IsNDigit n.val a ∧ IsNDigit n.val b ∧ P = a * b) ∧
            Palindromic P ∧
              IsLeastNonnegRemainder P r.val ∧
                ∀ c d : ℤ,
                  IsNDigit n.val c → IsNDigit n.val d → Palindromic (c * d) → c * d ≤ P := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8), ∃ r : Std.I64,
      Aegis.LargestPalindrome.largest_palindrome n = Result.ok r ∧
        ∃ P : ℤ,
          (∃ a b : ℤ, IsNDigit n.val a ∧ IsNDigit n.val b ∧ P = a * b) ∧
            Palindromic P ∧
              IsLeastNonnegRemainder P r.val ∧
                ∀ c d : ℤ,
                  IsNDigit n.val c → IsNDigit n.val d → Palindromic (c * d) → c * d ≤ P) := by
  sorry

/-- For every integer n with 1 <= n <= 8, when the function is called on n it returns a result and does not fail, panic, or overflow.
  Preconditions: n is the integer value of the Lean Std.I64 parameter n, and 1 <= n <= 8. -/
theorem spec_2 (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8) :
    ∃ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = .ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8), ∃ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = Result.ok r) := by
  sorry

/-- Whenever the function returns r, r is an integer satisfying 0 <= r < 1337.
  Preconditions: n is the integer value of the Lean Std.I64 parameter n, and 1 <= n <= 8. -/
theorem spec_3 (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8) :
    ∀ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = .ok r →
      0 ≤ r.val ∧ r.val < 1337 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8), ∀ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = Result.ok r →
      0 ≤ r.val ∧ r.val < 1337) := by
  sorry

/-- Whenever the function returns r, there exist n-digit integers a and b such that a*b is palindromic and r is the least nonnegative remainder of a*b modulo 1337.
  Preconditions: n is the integer value of the Lean Std.I64 parameter n, and 1 <= n <= 8. An n-digit integer d means 10^(n-1) <= d <= 10^n - 1, and palindromic means its decimal representation without leading zeros equals its reverse. -/
theorem spec_4 (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8) :
    ∀ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = .ok r →
      ∃ a b : ℤ,
        IsNDigit n.val a ∧ IsNDigit n.val b ∧ Palindromic (a * b) ∧
          IsLeastNonnegRemainder (a * b) r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8), ∀ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = Result.ok r →
      ∃ a b : ℤ,
        IsNDigit n.val a ∧ IsNDigit n.val b ∧ Palindromic (a * b) ∧
          IsLeastNonnegRemainder (a * b) r.val) := by
  sorry

/-- Whenever the function returns r on input n and s on input m, we have r = M(n) mod 1337, s = M(m) mod 1337, and M(n) < M(m).
  Preconditions: n and m are integer values of Lean Std.I64 parameters with 1 <= n < m <= 8. For each k, let M(k) denote the largest palindromic product of two k-digit integers. -/
theorem spec_5 (n m : Std.I64) (h1 : 1 ≤ n.val) (hnm : n.val < m.val) (h8 : m.val ≤ 8) :
    ∀ r s : Std.I64,
      Aegis.LargestPalindrome.largest_palindrome n = .ok r →
        Aegis.LargestPalindrome.largest_palindrome m = .ok s →
          ∃ Mn Mm : ℤ,
            IsLargestPalindromicProduct n.val Mn ∧ IsLargestPalindromicProduct m.val Mm ∧
              IsLeastNonnegRemainder Mn r.val ∧ IsLeastNonnegRemainder Mm s.val ∧ Mn < Mm := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n m : Std.I64) (h1 : 1 ≤ n.val) (hnm : n.val < m.val) (h8 : m.val ≤ 8), ∀ r s : Std.I64,
      Aegis.LargestPalindrome.largest_palindrome n = Result.ok r →
        Aegis.LargestPalindrome.largest_palindrome m = Result.ok s →
          ∃ Mn Mm : ℤ,
            IsLargestPalindromicProduct n.val Mn ∧ IsLargestPalindromicProduct m.val Mm ∧
              IsLeastNonnegRemainder Mn r.val ∧ IsLeastNonnegRemainder Mm s.val ∧ Mn < Mm) := by
  sorry

/-- Whenever the function returns r, for every pair of n-digit integers a and b, if a*b is palindromic and every palindromic product of two n-digit integers is at most a*b, then r is the least nonnegative remainder of a*b modulo 1337.
  Preconditions: n is the integer value of the Lean Std.I64 parameter n, and 1 <= n <= 8. An n-digit integer d means 10^(n-1) <= d <= 10^n - 1. -/
theorem spec_6 (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8) :
    ∀ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = .ok r →
      ∀ a b : ℤ,
        IsNDigit n.val a → IsNDigit n.val b → Palindromic (a * b) →
          (∀ c d : ℤ, IsNDigit n.val c → IsNDigit n.val d → Palindromic (c * d) → c * d ≤ a * b) →
            IsLeastNonnegRemainder (a * b) r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h8 : n.val ≤ 8), ∀ r : Std.I64, Aegis.LargestPalindrome.largest_palindrome n = Result.ok r →
      ∀ a b : ℤ,
        IsNDigit n.val a → IsNDigit n.val b → Palindromic (a * b) →
          (∀ c d : ℤ, IsNDigit n.val c → IsNDigit n.val d → Palindromic (c * d) → c * d ≤ a * b) →
            IsLeastNonnegRemainder (a * b) r.val) := by
  sorry

end AegisSpec.LargestPalindrome
