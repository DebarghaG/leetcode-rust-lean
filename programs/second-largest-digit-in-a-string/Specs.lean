import Aegis.SecondHighest.Code.Funs

/-!
# Specifications of `Aegis.SecondHighest.second_highest`

LeetCode problem `second-largest-digit-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SecondHighest

  open Aegis.SecondHighest

  def IsDigitByte (b : U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  def IsLowerByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def ValidInput (s : Slice U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 500 ∧
      ∀ (i : Nat) (h : i < s.val.length),
        IsDigitByte (s.val[i]) ∨ IsLowerByte (s.val[i])

  def DigitAt (s : Slice U8) (i : Nat) (d : Int) : Prop :=
    ∃ _ : i < s.val.length, ((s.val[i]).val : Int) = 48 + d

  def DigitOccurs (s : Slice U8) (d : Nat) : Prop :=
    d ≤ 9 ∧ ∃ i : Nat, DigitAt s i (d : Int)

  def TwoDistinctDigits (s : Slice U8) : Prop :=
    ∃ d₁ d₂ : Nat, DigitOccurs s d₁ ∧ DigitOccurs s d₂ ∧ d₁ ≠ d₂

  def IsMaxDigit (s : Slice U8) (M : Nat) : Prop :=
    DigitOccurs s M ∧ ∀ d : Nat, DigitOccurs s d → d ≤ M

  def IsSecondLargestDigit (s : Slice U8) (r : Nat) : Prop :=
    DigitOccurs s r ∧
      ∃ M : Nat, IsMaxDigit s M ∧ r < M ∧ ∀ d : Nat, DigitOccurs s d → d < M → d ≤ r

  /-- Whenever the function returns a result r, define D = { d | 0 <= d <= 9 and there exists i with 0 <= i < len(s) and s[i] = 48 + d }, the set of distinct numerical digit values occurring in s. Then: if D has fewer than two elements, r = -1; if D has at least two elements, r = max { d | d in D and d < max D }, i.e. r is the largest digit value occurring in s that is strictly smaller than the largest digit value occurring in s. Equivalently, r is -1 when fewer than two distinct digit values occur, and otherwise r is the second largest distinct digit value occurring in s.
    Preconditions: Let len(s) be the number of bytes of s. Assume 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), the byte s[i] is either an ASCII digit byte (48 <= s[i] <= 57) or a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_1 (s : Slice U8) (hpre : ValidInput s) (r : I64)
      (hr : second_highest s = ok r) :
      (¬ TwoDistinctDigits s → r.val = -1) ∧
        (TwoDistinctDigits s → ∃ d : Nat, r.val = (d : Int) ∧ IsSecondLargestDigit s d) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (hpre : ValidInput s) (r : I64)
        (hr : second_highest s = ok r), (¬ TwoDistinctDigits s → r.val = -1) ∧
          (TwoDistinctDigits s → ∃ d : Nat, r.val = (d : Int) ∧ IsSecondLargestDigit s d)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: Let len(s) be the number of bytes of s. Assume 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), the byte s[i] is either an ASCII digit byte (48 <= s[i] <= 57) or a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_2 (s : Slice U8) (hpre : ValidInput s) :
      ∃ r : I64, second_highest s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (hpre : ValidInput s), ∃ r : I64, second_highest s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, -1 <= r <= 9.
    Preconditions: Let len(s) be the number of bytes of s. Assume 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), the byte s[i] is either an ASCII digit byte (48 <= s[i] <= 57) or a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_3 (s : Slice U8) (hpre : ValidInput s) (r : I64)
      (hr : second_highest s = ok r) : -1 ≤ r.val ∧ r.val ≤ 9 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (hpre : ValidInput s) (r : I64)
        (hr : second_highest s = ok r), -1 ≤ r.val ∧ r.val ≤ 9) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists an index i with 0 <= i < len(s) such that s[i] = 48 + r; in other words, the reported digit value r actually occurs in s.
    Preconditions: Let len(s) be the number of bytes of s. Assume 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), the byte s[i] is either an ASCII digit byte (48 <= s[i] <= 57) or a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_4 (s : Slice U8) (hpre : ValidInput s) (r : I64)
      (hr : second_highest s = ok r) (hrne : r.val ≠ -1) :
      ∃ i : Nat, DigitAt s i r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (hpre : ValidInput s) (r : I64)
        (hr : second_highest s = ok r) (hrne : r.val ≠ -1), ∃ i : Nat, DigitAt s i r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, the set of numerical digit values d occurring in s with d > r has exactly one element. A digit value d occurs in s iff there is an index i with 0 <= i < len(s) and s[i] = 48 + d.
    Preconditions: Let len(s) be the number of bytes of s. Assume 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), the byte s[i] is either an ASCII digit byte (48 <= s[i] <= 57) or a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_5 (s : Slice U8) (hpre : ValidInput s) (r : I64)
      (hr : second_highest s = ok r) (hrne : r.val ≠ -1) :
      ∃! d : Nat, DigitOccurs s d ∧ r.val < (d : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (hpre : ValidInput s) (r : I64)
        (hr : second_highest s = ok r) (hrne : r.val ≠ -1), ∃! d : Nat, DigitOccurs s d ∧ r.val < (d : Int)) := by
    sorry

  /-- For any such t, if the set of distinct numerical digit values occurring in s equals the set of distinct numerical digit values occurring in t (d occurs in s iff d occurs in t, where d occurs in a slice iff some byte equals 48 + d), then whenever second_highest(s) returns r and second_highest(t) returns r', we have r = r'.
    Preconditions: Let len(s) and len(t) be the numbers of bytes. Assume 1 <= len(s) <= 500, 1 <= len(t) <= 500, and for every i with 0 <= i < len(s), s[i] is an ASCII digit byte (48 <= s[i] <= 57) or a lowercase English letter byte (97 <= s[i] <= 122); and similarly for every i with 0 <= i < len(t). -/
  theorem spec_6 (s t : Slice U8) (hpre_s : ValidInput s) (hpre_t : ValidInput t)
      (hdigit : ∀ d : Nat, DigitOccurs s d ↔ DigitOccurs t d)
      (r r' : I64) (hr : second_highest s = ok r) (hr' : second_highest t = ok r') :
      r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice U8) (hpre_s : ValidInput s) (hpre_t : ValidInput t)
        (hdigit : ∀ d : Nat, DigitOccurs s d ↔ DigitOccurs t d)
        (r r' : I64) (hr : second_highest s = ok r) (hr' : second_highest t = ok r'), r = r') := by
    sorry

  end AegisSpec.SecondHighest
