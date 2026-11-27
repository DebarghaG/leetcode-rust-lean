import Aegis.CountSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountSubstrings.count_substrings`

LeetCode problem `count-substrings-divisible-by-last-digit`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountSubstrings

namespace AegisSpec.CountSubstrings

def byteAt (s : Slice U8) (k : Nat) : Nat :=
  ((s.val[k]? : Option U8).map (fun b => b.val)).getD 0

def digitAt (s : Slice U8) (k : Nat) : Nat := byteAt s k - 48

def allBytes (s : Slice U8) (p : Nat → Prop) : Prop :=
  ∀ i, i < s.val.length → p (byteAt s i)

def allDigits (s : Slice U8) (p : Nat → Prop) : Prop :=
  allBytes s (fun b => p (b - 48))

def isDigitString (s : Slice U8) : Prop :=
  allBytes s (fun b => 48 ≤ b ∧ b ≤ 57)

def valueAt (s : Slice U8) (i j : Nat) : Nat :=
  ((List.range (j + 1 - i)).map (fun t => digitAt s (i + t) * 10 ^ (j - (i + t)))).sum

def validPair (s : Slice U8) (n i j : Nat) : Prop :=
  i ≤ j ∧ j < n ∧ digitAt s j ≠ 0 ∧ valueAt s i j % digitAt s j = 0

instance decidableValidPair (s : Slice U8) (n i j : Nat) : Decidable (validPair s n i j) := by
  unfold validPair
  infer_instance

def countPairs (s : Slice U8) (n : Nat) : Nat :=
  ((List.range n).map (fun j =>
    ((List.range (j + 1)).filter (fun i => decide (validPair s n i j))).length)).sum

def answer (s : Slice U8) : Nat :=
  countPairs s s.val.length

def totalSubstrings (s : Slice U8) : Nat :=
  s.val.length * (s.val.length + 1) / 2

def sumWhere (s : Slice U8) (p : Nat → Prop) [DecidablePred p] (f : Nat → Nat) : Nat :=
  (((List.range s.val.length).filter (fun j => decide (p j))).map f).sum

def countWhere (s : Slice U8) (p : Nat → Prop) [DecidablePred p] : Nat :=
  ((List.range s.val.length).filter (fun j => decide (p j))).length

/-- Whenever count_substrings s returns a result r, r equals the number of pairs (i,j) with 0 <= i <= j < len(s) for which the following holds. Let digit(k) = s[k] - 48 for 0 <= k < len(s), and let value(i,j) = sum_{k=i}^{j} digit(k) * 10^(j-k). Then digit(j) != 0 and value(i,j) is divisible by digit(j), i.e. value(i,j) mod digit(j) = 0. Equivalently, r is exactly the number of nonempty contiguous substrings of s, with leading zeros allowed, whose last digit is nonzero and whose base-10 integer value is divisible by that last digit.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_1 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    r.val = (answer s : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), r.val = (answer s : ℤ)) := by
  sorry

/-- For every such s, count_substrings s returns a result: there exists an I64 value r such that count_substrings s = Result.ok r. In particular, for every permitted s the function does not fail, panic, overflow, or access out of bounds.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_2 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s) :
    ∃ r : I64, count_substrings s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s), ∃ r : I64, count_substrings s = ok r) := by
  sorry

/-- Whenever count_substrings s returns a result r, 0 <= r <= len(s) * (len(s) + 1) / 2. The upper bound is exactly the total number of nonempty contiguous substrings of s.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_3 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    0 ≤ r.val ∧ r.val ≤ (totalSubstrings s : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), 0 ≤ r.val ∧ r.val ≤ (totalSubstrings s : ℤ)) := by
  sorry

/-- Whenever count_substrings s returns a result r, r <= sum over j with 0 <= j < len(s) and s[j] != 48 of (j + 1). This sum is exactly the number of all nonempty substrings whose last digit is nonzero, since a substring ending at position j has j+1 possible starting positions.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_4 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    r.val ≤ (sumWhere s (fun j => byteAt s j ≠ 48) (fun j => j + 1) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), r.val ≤ (sumWhere s (fun j => byteAt s j ≠ 48) (fun j => j + 1) : ℤ)) := by
  sorry

/-- Whenever count_substrings s returns a result r, r >= the number of indices i with 0 <= i < len(s) and s[i] != 48. Indeed, for each such i the one-character substring s[i..i] has last digit s[i] - 48 != 0 and value equal to that digit, so that substring is counted.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_5 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    (countWhere s (fun i => byteAt s i ≠ 48) : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), (countWhere s (fun i => byteAt s i ≠ 48) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever count_substrings s returns a result r, r = 0 if and only if every byte of s is 48, i.e. every digit of s is '0'.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_6 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    (r.val = 0 ↔ allBytes s (fun b => b = 48)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), (r.val = 0 ↔ allBytes s (fun b => b = 48))) := by
  sorry

/-- Whenever count_substrings s returns a result r, if len(s) = 1, then r = 1 when s[0] != 48, and r = 0 when s[0] = 48.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_7 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    s.val.length = 1 →
      ((byteAt s 0 ≠ 48 → r.val = 1) ∧ (byteAt s 0 = 48 → r.val = 0)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), s.val.length = 1 →
      ((byteAt s 0 ≠ 48 → r.val = 1) ∧ (byteAt s 0 = 48 → r.val = 0))) := by
  sorry

/-- Whenever count_substrings s returns a result r, if for every i with 0 <= i < len(s) the digit s[i] - 48 is in {1,2,5}, then r = len(s) * (len(s) + 1) / 2. Every substring ends in 1, 2, or 5, and every integer ending in 1, 2, or 5 is divisible by that last digit.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_8 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    allDigits s (fun d => d = 1 ∨ d = 2 ∨ d = 5) →
      r.val = (totalSubstrings s : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), allDigits s (fun d => d = 1 ∨ d = 2 ∨ d = 5) →
      r.val = (totalSubstrings s : ℤ)) := by
  sorry

/-- Whenever count_substrings s returns a result r, if for every i with 0 <= i < len(s), s[i] - 48 is either 0 or 1, then r = sum over j with 0 <= j < len(s) and s[j] = 49 of (j + 1). Substrings ending in '0' are excluded, and every substring ending in '1' is divisible by 1.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_9 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    allDigits s (fun d => d = 0 ∨ d = 1) →
      r.val = (sumWhere s (fun j => byteAt s j = 49) (fun j => j + 1) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), allDigits s (fun d => d = 0 ∨ d = 1) →
      r.val = (sumWhere s (fun j => byteAt s j = 49) (fun j => j + 1) : ℤ)) := by
  sorry

/-- Whenever count_substrings s returns a result r, if for every i with 0 <= i < len(s), s[i] - 48 is either 0 or 5, then r = sum over j with 0 <= j < len(s) and s[j] = 53 of (j + 1). Substrings ending in '0' are excluded, and every substring ending in '5' is divisible by 5.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_10 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    allDigits s (fun d => d = 0 ∨ d = 5) →
      r.val = (sumWhere s (fun j => byteAt s j = 53) (fun j => j + 1) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), allDigits s (fun d => d = 0 ∨ d = 5) →
      r.val = (sumWhere s (fun j => byteAt s j = 53) (fun j => j + 1) : ℤ)) := by
  sorry

/-- Whenever count_substrings s returns a result r, if len(s) >= 2 and s[len(s)-1] = 48, then r equals the number of pairs (i,j) with 0 <= i <= j < len(s)-1 such that, with digit(k) = s[k] - 48 and value(i,j) = sum_{k=i}^{j} digit(k) * 10^(j-k), one has digit(j) != 0 and value(i,j) mod digit(j) = 0. Equivalently, deleting a trailing '0' does not change the answer.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_11 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    2 ≤ s.val.length → byteAt s (s.val.length - 1) = 48 →
      r.val = (countPairs s (s.val.length - 1) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), 2 ≤ s.val.length → byteAt s (s.val.length - 1) = 48 →
      r.val = (countPairs s (s.val.length - 1) : ℤ)) := by
  sorry

/-- Whenever count_substrings s returns a result r, if len(s) >= 2, then r is greater than or equal to the number of valid pairs (i,j) with 0 <= i <= j < len(s)-1, using digit(k) = s[k] - 48, value(i,j) = sum_{k=i}^{j} digit(k) * 10^(j-k), and the condition digit(j) != 0 and value(i,j) mod digit(j) = 0. In words, appending one more digit to a string cannot decrease the answer.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_12 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    2 ≤ s.val.length → (countPairs s (s.val.length - 1) : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), 2 ≤ s.val.length → (countPairs s (s.val.length - 1) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever count_substrings s returns a result r, r >= sum over j with 0 <= j < len(s) and (s[j] - 48) in {1,2,5} of (j + 1). For each such j, every substring ending at j has last digit 1, 2, or 5 and hence is divisible by its last digit, so all j+1 starting positions are counted.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
theorem spec_13 (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r) :
    (sumWhere s (fun j => digitAt s j = 1 ∨ digitAt s j = 2 ∨ digitAt s j = 5)
      (fun j => j + 1) : ℤ) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hdigits : isDigitString s)
    (hres : count_substrings s = ok r), (sumWhere s (fun j => digitAt s j = 1 ∨ digitAt s j = 2 ∨ digitAt s j = 5)
      (fun j => j + 1) : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.CountSubstrings
