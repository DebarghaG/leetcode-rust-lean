import Aegis.LengthOfLastWord.Code.Funs

/-!
# Specifications of `Aegis.LengthOfLastWord.length_of_last_word`

LeetCode problem `length-of-last-word`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LengthOfLastWord

def byteAt (s : Slice U8) (i : Nat) : Nat :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def isSpaceByte (b : Nat) : Prop := b = 32

def isUpperByte (b : Nat) : Prop := 65 ≤ b ∧ b ≤ 90

def isLowerByte (b : Nat) : Prop := 97 ≤ b ∧ b ≤ 122

def isLetterByte (b : Nat) : Prop := isUpperByte b ∨ isLowerByte b

def isWordByte (b : Nat) : Prop := isSpaceByte b ∨ isLetterByte b

def allWordBytes (s : Slice U8) : Prop := ∀ i, i < s.val.length → isWordByte (byteAt s i)

def hasNonSpaceByte (s : Slice U8) : Prop := ∃ i, i < s.val.length ∧ byteAt s i ≠ 32

def IsLastNonSpaceIndex (s : Slice U8) (e : Nat) : Prop :=
  e < s.val.length ∧ byteAt s e ≠ 32 ∧ ∀ j, e < j → j < s.val.length → byteAt s j = 32

def IsWordStartIndex (s : Slice U8) (e a : Nat) : Prop :=
  a ≤ e ∧ (∀ j, a ≤ j → j ≤ e → byteAt s j ≠ 32) ∧ (a = 0 ∨ byteAt s (a - 1) = 32)

def nonSpaceCount (s : Slice U8) : Nat :=
  s.val.countP (fun b => decide (b.val ≠ 32))

def wordStartCount (s : Slice U8) : Nat :=
  (List.range s.val.length).countP
    (fun a => decide (byteAt s a ≠ 32 ∧ (a = 0 ∨ byteAt s (a - 1) = 32)))

def IsLastSpaceIndexBefore (s : Slice U8) (e p : Nat) : Prop :=
  p < e ∧ byteAt s p = 32 ∧ ∀ j, p < j → j < e → byteAt s j ≠ 32

def IsSlicePrefix (s' s : Slice U8) (n : Nat) : Prop :=
  s'.val.length = n ∧ ∀ i, i < n → byteAt s' i = byteAt s i

def IsSpacePrepended (s' s : Slice U8) : Prop :=
  s'.val.length = s.val.length + 1 ∧ byteAt s' 0 = 32 ∧
    ∀ i, i < s.val.length → byteAt s' (i + 1) = byteAt s i

def IsByteAppended (s' s : Slice U8) (c : U8) : Prop :=
  s'.val.length = s.val.length + 1 ∧
    (∀ i, i < s.val.length → byteAt s' i = byteAt s i) ∧
    byteAt s' s.val.length = c.val

/-- Whenever the function returns a result r, r.val is the length of the last word of s. Formally, let e be the largest index with 0 <= e < len(s) and s[e] != 32. Let a be the smallest index with 0 <= a <= e, s[j] != 32 for every j with a <= j <= e, and (a = 0 or s[a-1] = 32). Then r.val = e - a + 1.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); and there exists i with 0 <= i < len(s) and s[i] != 32. -/
theorem spec_1 (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      ∀ (e a : Nat), IsLastNonSpaceIndex s e → IsWordStartIndex s e a →
        (∀ a', IsWordStartIndex s e a' → a ≤ a') →
        r.val = (e : Int) - (a : Int) + 1 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s), Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      ∀ (e a : Nat), IsLastNonSpaceIndex s e → IsWordStartIndex s e a →
        (∀ a', IsWordStartIndex s e a' → a ≤ a') →
        r.val = (e : Int) - (a : Int) + 1) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r; it does not fail, panic, access out of bounds, or overflow.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); and there exists i with 0 <= i < len(s) and s[i] != 32. -/
theorem spec_2 (s : Slice U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s) :
    ∃ r : I64, Aegis.LengthOfLastWord.length_of_last_word s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s), ∃ r : I64, Aegis.LengthOfLastWord.length_of_last_word s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r.val >= 1.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); and there exists i with 0 <= i < len(s) and s[i] != 32. -/
theorem spec_3 (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s), Aegis.LengthOfLastWord.length_of_last_word s = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r.val <= len(s).
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); and there exists i with 0 <= i < len(s) and s[i] != 32. -/
theorem spec_4 (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val ≤ (s.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s), Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val ≤ (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r.val <= N, where N is the number of indices i with 0 <= i < len(s) and s[i] != 32.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); and there exists i with 0 <= i < len(s) and s[i] != 32. -/
theorem spec_5 (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val ≤ (nonSpaceCount s : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s), Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val ≤ (nonSpaceCount s : Int)) := by
  sorry

/-- Whenever the function returns a result r, r.val = N, where N is the number of indices i with 0 <= i < len(s) and s[i] != 32.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); there exists i with 0 <= i < len(s) and s[i] != 32; and the number of indices a with 0 <= a < len(s), s[a] != 32, and (a = 0 or s[a-1] = 32) is exactly 1. -/
theorem spec_6 (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hwords : wordStartCount s = 1) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val = (nonSpaceCount s : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hwords : wordStartCount s = 1), Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val = (nonSpaceCount s : Int)) := by
  sorry

/-- Whenever the function returns a result r, r.val = k, where k is the unique integer with 1 <= k <= len(s), all bytes s[len(s)-k], ..., s[len(s)-1] are non-space, and either k = len(s) or s[len(s)-k-1] = 32.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); there exists i with 0 <= i < len(s) and s[i] != 32; and s[len(s)-1] != 32. -/
theorem spec_7 (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hlast : byteAt s (s.val.length - 1) ≠ 32) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      ∀ k : Nat, 1 ≤ k → k ≤ s.val.length →
        (∀ j, s.val.length - k ≤ j → j < s.val.length → byteAt s j ≠ 32) →
        (k = s.val.length ∨ byteAt s (s.val.length - k - 1) = 32) →
        r.val = (k : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hlast : byteAt s (s.val.length - 1) ≠ 32), Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      ∀ k : Nat, 1 ≤ k → k ≤ s.val.length →
        (∀ j, s.val.length - k ≤ j → j < s.val.length → byteAt s j ≠ 32) →
        (k = s.val.length ∨ byteAt s (s.val.length - k - 1) = 32) →
        r.val = (k : Int)) := by
  sorry

/-- Let s' be the slice of length len(s)-1 with s'[i] = s[i] for every i with 0 <= i < len(s)-1. Whenever the function returns r for s and r' for s', r.val = r'.val.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); there exists i with 0 <= i < len(s) and s[i] != 32; and s[len(s)-1] = 32. -/
theorem spec_8 (s s' : Slice U8) (r r' : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hlast : byteAt s (s.val.length - 1) = 32)
    (hprefix : IsSlicePrefix s' s (s.val.length - 1)) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      Aegis.LengthOfLastWord.length_of_last_word s' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s s' : Slice U8) (r r' : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hlast : byteAt s (s.val.length - 1) = 32)
    (hprefix : IsSlicePrefix s' s (s.val.length - 1)), Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      Aegis.LengthOfLastWord.length_of_last_word s' = ok r' → r.val = r'.val) := by
  sorry

/-- Let s' be the slice of length len(s)+1 with s'[0] = 32 and s'[i+1] = s[i] for every i with 0 <= i < len(s). Whenever the function returns r' for s' and r for s, r'.val = r.val.
  Preconditions: 1 <= len(s) <= 9999; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); and there exists i with 0 <= i < len(s) and s[i] != 32. -/
theorem spec_9 (s s' : Slice U8) (r r' : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 9999)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hprepend : IsSpacePrepended s' s) :
    Aegis.LengthOfLastWord.length_of_last_word s' = ok r' →
      Aegis.LengthOfLastWord.length_of_last_word s = ok r → r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s s' : Slice U8) (r r' : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 9999)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hprepend : IsSpacePrepended s' s), Aegis.LengthOfLastWord.length_of_last_word s' = ok r' →
      Aegis.LengthOfLastWord.length_of_last_word s = ok r → r'.val = r.val) := by
  sorry

/-- Let e be the largest index with 0 <= e < len(s) and s[e] != 32, and let p be the largest index with 0 <= p < e and s[p] = 32. Whenever the function returns a result r, r.val = e - p.
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); there exists i with 0 <= i < len(s) and s[i] != 32; and if e is the largest index with 0 <= e < len(s) and s[e] != 32, then there exists an index i with 0 <= i < e and s[i] = 32. -/
theorem spec_10 (s : Slice U8) (r : I64) (e p : Nat)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (helast : IsLastNonSpaceIndex s e) (hplast : IsLastSpaceIndexBefore s e p) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val = (e : Int) - (p : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (r : I64) (e p : Nat)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (helast : IsLastNonSpaceIndex s e) (hplast : IsLastSpaceIndexBefore s e p), Aegis.LengthOfLastWord.length_of_last_word s = ok r → r.val = (e : Int) - (p : Int)) := by
  sorry

/-- Let s' be the slice of length len(s)+1 with s'[i] = s[i] for every i with 0 <= i < len(s) and s'[len(s)] = c. Whenever the function returns r for s and r' for s', r'.val = r.val + 1.
  Preconditions: 1 <= len(s) <= 9999; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); there exists i with 0 <= i < len(s) and s[i] != 32; s[len(s)-1] != 32; and c is a byte with (65 <= c <= 90) or (97 <= c <= 122). -/
theorem spec_11 (s s' : Slice U8) (r r' : I64) (c : U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 9999)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hlast : byteAt s (s.val.length - 1) ≠ 32)
    (hc : isLetterByte c.val)
    (happend : IsByteAppended s' s c) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      Aegis.LengthOfLastWord.length_of_last_word s' = ok r' → r'.val = r.val + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s s' : Slice U8) (r r' : I64) (c : U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 9999)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s)
    (hlast : byteAt s (s.val.length - 1) ≠ 32)
    (hc : isLetterByte c.val)
    (happend : IsByteAppended s' s c), Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      Aegis.LengthOfLastWord.length_of_last_word s' = ok r' → r'.val = r.val + 1) := by
  sorry

/-- Whenever the function returns a result r, there exist indices a and b such that 0 <= a < b <= len(s), b - a = r.val, s[j] != 32 for every j with a <= j < b, (a = 0 or s[a-1] = 32), (b = len(s) or s[b] = 32), and s[j] = 32 for every j with b <= j < len(s).
  Preconditions: 1 <= len(s) <= 10000; for every i with 0 <= i < len(s), s[i] = 32 or (65 <= s[i] <= 90) or (97 <= s[i] <= 122); and there exists i with 0 <= i < len(s) and s[i] != 32. -/
theorem spec_12 (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s) :
    Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      ∃ a b : Nat, a < b ∧ b ≤ s.val.length ∧
        (b : Int) - (a : Int) = r.val ∧
        (∀ j, a ≤ j → j < b → byteAt s j ≠ 32) ∧
        (a = 0 ∨ byteAt s (a - 1) = 32) ∧
        (b = s.val.length ∨ byteAt s b = 32) ∧
        (∀ j, b ≤ j → j < s.val.length → byteAt s j = 32) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 10000)
    (hbytes : allWordBytes s) (hns : hasNonSpaceByte s), Aegis.LengthOfLastWord.length_of_last_word s = ok r →
      ∃ a b : Nat, a < b ∧ b ≤ s.val.length ∧
        (b : Int) - (a : Int) = r.val ∧
        (∀ j, a ≤ j → j < b → byteAt s j ≠ 32) ∧
        (a = 0 ∨ byteAt s (a - 1) = 32) ∧
        (b = s.val.length ∨ byteAt s b = 32) ∧
        (∀ j, b ≤ j → j < s.val.length → byteAt s j = 32)) := by
  sorry

end AegisSpec.LengthOfLastWord
