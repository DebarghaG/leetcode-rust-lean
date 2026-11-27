import Aegis.IsBalanced.Code.Funs

/-!
# Specifications of `Aegis.IsBalanced.is_balanced`

LeetCode problem `check-balanced-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsBalanced

def byteAt (num : Slice Std.U8) (i : ℕ) : ℕ :=
  ((num.val[i]?).map (fun b => b.val)).getD 0

def digitAt (num : Slice Std.U8) (i : ℕ) : ℕ :=
  byteAt num i - 48

def AllDigits (num : Slice Std.U8) : Prop :=
  ∀ i, i < num.val.length → 48 ≤ byteAt num i ∧ byteAt num i ≤ 57

def evenDigitSum (num : Slice Std.U8) : ℕ :=
  ((Finset.range num.val.length).filter (fun i => i % 2 = 0)).sum (fun i => digitAt num i)

def oddDigitSum (num : Slice Std.U8) : ℕ :=
  ((Finset.range num.val.length).filter (fun i => i % 2 = 1)).sum (fun i => digitAt num i)

def digitSum (num : Slice Std.U8) : ℕ :=
  (Finset.range num.val.length).sum (fun i => digitAt num i)

def ReverseOf (num rev : Slice Std.U8) : Prop :=
  rev.val.length = num.val.length ∧
    ∀ i, i < num.val.length → byteAt rev i = byteAt num (num.val.length - 1 - i)

/-- Let digit(i) = num[i] - 48 for 0 <= i < len(num). Let E be the sum of digit(i) over even indices i (0, 2, 4, ...) and O be the sum of digit(i) over odd indices i (1, 3, 5, ...). Whenever the function returns a result r, r = true if and only if E = O; if E != O then r = false.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100, and for every i with 0 <= i < len(num), num[i] is an ASCII digit, i.e. 48 <= num[i] <= 57. -/
theorem spec_1 (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num) :
    ∀ r, Aegis.IsBalanced.is_balanced num = ok r →
      (r = true ↔ evenDigitSum num = oddDigitSum num) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num), ∀ r, Aegis.IsBalanced.is_balanced num = ok r →
      (r = true ↔ evenDigitSum num = oddDigitSum num)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a Boolean result; it does not fail because of overflow, out-of-bounds access, or panic.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100, and for every i with 0 <= i < len(num), num[i] is an ASCII digit, i.e. 48 <= num[i] <= 57. -/
theorem spec_2 (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num) :
    ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num), ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r) := by
  sorry

/-- Let digit(i) = num[i] - 48. Suppose there is a digit value d with 0 <= d <= 9 such that digit(i) = d for every i with 0 <= i < len(num). Then the function returns a result r and r = true if and only if len(num) is even or d = 0; otherwise r = false.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100, and for every i with 0 <= i < len(num), 48 <= num[i] <= 57. -/
theorem spec_3 (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (d : ℕ) (hd : d ≤ 9)
    (hconst : ∀ i, i < num.val.length → digitAt num i = d) :
    ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      (r = true ↔ (num.val.length % 2 = 0 ∨ d = 0)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (d : ℕ) (hd : d ≤ 9)
    (hconst : ∀ i, i < num.val.length → digitAt num i = d), ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      (r = true ↔ (num.val.length % 2 = 0 ∨ d = 0))) := by
  sorry

/-- Let digit(i) = num[i] - 48 and let T be the sum of digit(i) over all i with 0 <= i < len(num). If T is odd, then the function returns a result r and r = false.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100, and for every i with 0 <= i < len(num), 48 <= num[i] <= 57. -/
theorem spec_4 (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (hT : digitSum num % 2 = 1) :
    ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧ r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (hT : digitSum num % 2 = 1), ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧ r = false) := by
  sorry

/-- Let digit(i) = num[i] - 48. The function returns a result r and r = true if and only if num[j] = 48 for every odd j with 0 <= j < len(num); otherwise r = false.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100, and for every i with 0 <= i < len(num), 48 <= num[i] <= 57. Also, num[i] = 48 for every even i with 0 <= i < len(num). -/
theorem spec_5 (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (heven : ∀ i, i < num.val.length → i % 2 = 0 → byteAt num i = 48) :
    ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      (r = true ↔ ∀ j, j < num.val.length → j % 2 = 1 → byteAt num j = 48) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (heven : ∀ i, i < num.val.length → i % 2 = 0 → byteAt num i = 48), ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      (r = true ↔ ∀ j, j < num.val.length → j % 2 = 1 → byteAt num j = 48)) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100, for every i with 0 <= i < len(num), 48 <= num[i] <= 57, len(num) is even, and for every k with 0 <= k < len(num)/2, num[2k] = num[2k+1]. -/
theorem spec_6 (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (heven_len : num.val.length % 2 = 0)
    (hpair : ∀ k, k < num.val.length / 2 → byteAt num (2 * k) = byteAt num (2 * k + 1)) :
    ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧ r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (heven_len : num.val.length % 2 = 0)
    (hpair : ∀ k, k < num.val.length / 2 → byteAt num (2 * k) = byteAt num (2 * k + 1)), ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧ r = true) := by
  sorry

/-- Let digit(i) = num[i] - 48 for 0 <= i < len(num). The function returns a result r and r = true if and only if digit(2m) = 0; otherwise r = false.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100 and len(num) = 2*m + 1 for some integer m >= 1, and for every i with 0 <= i < len(num), 48 <= num[i] <= 57. Also, for every k with 0 <= k < m, num[2k] = num[2k+1]. -/
theorem spec_7 (num : Slice Std.U8) (m : ℕ)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hm : 1 ≤ m)
    (hlenm : num.val.length = 2 * m + 1)
    (hdig : AllDigits num)
    (hpair : ∀ k, k < m → byteAt num (2 * k) = byteAt num (2 * k + 1)) :
    ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      (r = true ↔ digitAt num (2 * m) = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Slice Std.U8) (m : ℕ)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hm : 1 ≤ m)
    (hlenm : num.val.length = 2 * m + 1)
    (hdig : AllDigits num)
    (hpair : ∀ k, k < m → byteAt num (2 * k) = byteAt num (2 * k + 1)), ∃ r : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      (r = true ↔ digitAt num (2 * m) = 0)) := by
  sorry

/-- Define rev(num) by len(rev(num)) = len(num) and rev(num)[i] = num[len(num)-1-i] for every i with 0 <= i < len(num). The call on num returns a result r, the call on rev(num) returns a result r_rev, and r = r_rev.
  Preconditions: num is a slice of bytes with 2 <= len(num) <= 100, and for every i with 0 <= i < len(num), 48 <= num[i] <= 57. -/
theorem spec_8 (num rev : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (hrev : ReverseOf num rev) :
    ∃ r r_rev : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      Aegis.IsBalanced.is_balanced rev = ok r_rev ∧ r = r_rev := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num rev : Slice Std.U8)
    (hlen : 2 ≤ num.val.length ∧ num.val.length ≤ 100)
    (hdig : AllDigits num)
    (hrev : ReverseOf num rev), ∃ r r_rev : Bool, Aegis.IsBalanced.is_balanced num = ok r ∧
      Aegis.IsBalanced.is_balanced rev = ok r_rev ∧ r = r_rev) := by
  sorry

end AegisSpec.IsBalanced
