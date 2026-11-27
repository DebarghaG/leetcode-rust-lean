import Aegis.HalvesAreAlike.Code.Funs

/-!
# Specifications of `Aegis.HalvesAreAlike.halves_are_alike`

LeetCode problem `determine-if-string-halves-are-alike`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HalvesAreAlike

def IsVowelByte (x : Std.U8) : Prop :=
  x.val = 97 ∨ x.val = 101 ∨ x.val = 105 ∨ x.val = 111 ∨ x.val = 117 ∨
    x.val = 65 ∨ x.val = 69 ∨ x.val = 73 ∨ x.val = 79 ∨ x.val = 85

instance instDecidableIsVowelByte (x : Std.U8) : Decidable (IsVowelByte x) := by
  unfold IsVowelByte
  infer_instance

def IsLetterByte (x : Std.U8) : Prop :=
  (65 ≤ x.val ∧ x.val ≤ 90) ∨ (97 ≤ x.val ∧ x.val ≤ 122)

instance instDecidableIsLetterByte (x : Std.U8) : Decidable (IsLetterByte x) := by
  unfold IsLetterByte
  infer_instance

def countVowels (l : List Std.U8) : Nat :=
  l.countP (fun x => decide (IsVowelByte x))

def firstHalfVowelCount (s : Slice Std.U8) : Nat :=
  countVowels (s.val.take (s.val.length / 2))

def secondHalfVowelCount (s : Slice Std.U8) : Nat :=
  countVowels (s.val.drop (s.val.length / 2))

/-- Let V(x) mean that byte x is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. Whenever the function returns a result r, r is true if and only if the number of indices i with 0 <= i < n/2 and V(s[i]) equals the number of indices i with n/2 <= i < n and V(s[i]).
  Preconditions: Let n = len(s). The preconditions are: n is even; 2 <= n <= 1000; and for every i with 0 <= i < n, s[i] is the ASCII code of an uppercase or lowercase English letter. -/
theorem spec_1 (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]) :
    ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        (r = true ↔ firstHalfVowelCount s = secondHalfVowelCount s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]), ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        (r = true ↔ firstHalfVowelCount s = secondHalfVowelCount s)) := by
  sorry

/-- The function returns a result r and does not fail for every s satisfying the preconditions.
  Preconditions: Let n = len(s). The preconditions are: n is even; 2 <= n <= 1000; and for every i with 0 <= i < n, s[i] is the ASCII code of an uppercase or lowercase English letter. -/
theorem spec_2 (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]) :
    ∃ (r : Bool), Aegis.HalvesAreAlike.halves_are_alike s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]), ∃ (r : Bool), Aegis.HalvesAreAlike.halves_are_alike s = ok r) := by
  sorry

/-- Whenever the function returns a result r with r = true, the total number of indices i with 0 <= i < n and V(s[i]) is even.
  Preconditions: Let n = len(s). The preconditions are: n is even; 2 <= n <= 1000; and for every i with 0 <= i < n, s[i] is the ASCII code of an uppercase or lowercase English letter. Let V(x) mean that byte x is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. -/
theorem spec_3 (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]) :
    ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r → r = true →
        Even (countVowels s.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]), ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r → r = true →
        Even (countVowels s.val)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if V(s[0]) and V(s[1]) are either both true or both false; equivalently, V(s[0]) = V(s[1]).
  Preconditions: n = len(s) = 2, and s[0] and s[1] are ASCII codes of uppercase or lowercase English letters. Let V(x) mean that byte x is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. -/
theorem spec_4 (s : Slice Std.U8)
    (h_len : s.val.length = 2)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]) :
    ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        (r = true ↔ (IsVowelByte s.val[0] ↔ IsVowelByte s.val[1])) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len : s.val.length = 2)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i]), ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        (r = true ↔ (IsVowelByte s.val[0] ↔ IsVowelByte s.val[1]))) := by
  sorry

/-- Whenever the function returns a result r, r = true.
  Preconditions: Let n = len(s). The preconditions are: n is even; 2 <= n <= 1000; every s[i] is the ASCII code of an uppercase or lowercase English letter; and for every i with 0 <= i < n, s[i] is not a vowel. Let V(x) mean that byte x is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. -/
theorem spec_5 (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_no_vowel : ∀ (i : Nat) (hi : i < s.val.length), ¬ IsVowelByte s.val[i]) :
    ∀ (r : Bool), Aegis.HalvesAreAlike.halves_are_alike s = ok r → r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_no_vowel : ∀ (i : Nat) (hi : i < s.val.length), ¬ IsVowelByte s.val[i]), ∀ (r : Bool), Aegis.HalvesAreAlike.halves_are_alike s = ok r → r = true) := by
  sorry

/-- Whenever the function returns a result r, r = false.
  Preconditions: Let n = len(s). The preconditions are: n is even; 2 <= n <= 1000; every s[i] is the ASCII code of an uppercase or lowercase English letter; and the total number of vowel bytes in s is exactly 1. Let V(x) mean that byte x is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. -/
theorem spec_6 (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_one_vowel : countVowels s.val = 1) :
    ∀ (r : Bool), Aegis.HalvesAreAlike.halves_are_alike s = ok r → r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_one_vowel : countVowels s.val = 1), ∀ (r : Bool), Aegis.HalvesAreAlike.halves_are_alike s = ok r → r = false) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if the two vowel positions consist of one index in the range 0 <= i < n/2 and one index in the range n/2 <= i < n.
  Preconditions: Let n = len(s). The preconditions are: n is even; 2 <= n <= 1000; every s[i] is the ASCII code of an uppercase or lowercase English letter; and the total number of vowel bytes in s is exactly 2. Let V(x) mean that byte x is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. -/
theorem spec_7 (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_two_vowels : countVowels s.val = 2) :
    ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        (r = true ↔ (firstHalfVowelCount s = 1 ∧ secondHalfVowelCount s = 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_two_vowels : countVowels s.val = 2), ∀ (r : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        (r = true ↔ (firstHalfVowelCount s = 1 ∧ secondHalfVowelCount s = 1))) := by
  sorry

/-- If the function returns result r on input s and result q on input t, then r = q.
  Preconditions: Let V(x) mean that byte x is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. Let s and t be byte slices of the same length n. Both satisfy: n is even; 2 <= n <= 1000; and every byte of s or t is an uppercase or lowercase English letter. Moreover, for every i with 0 <= i < n, V(s[i]) if and only if V(t[i]). -/
theorem spec_8 (s t : Slice Std.U8)
    (h_len : s.val.length = t.val.length)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter_s : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_letter_t : ∀ (i : Nat) (hi : i < t.val.length), IsLetterByte t.val[i])
    (h_vowel : ∀ (i : Nat) (hi : i < s.val.length), IsVowelByte s.val[i] ↔ IsVowelByte t.val[i]) :
    ∀ (r q : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        Aegis.HalvesAreAlike.halves_are_alike t = ok q → r = q := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (h_len : s.val.length = t.val.length)
    (h_even : Even s.val.length)
    (h_lower : 2 ≤ s.val.length)
    (h_upper : s.val.length ≤ 1000)
    (h_letter_s : ∀ (i : Nat) (hi : i < s.val.length), IsLetterByte s.val[i])
    (h_letter_t : ∀ (i : Nat) (hi : i < t.val.length), IsLetterByte t.val[i])
    (h_vowel : ∀ (i : Nat) (hi : i < s.val.length), IsVowelByte s.val[i] ↔ IsVowelByte t.val[i]), ∀ (r q : Bool),
      Aegis.HalvesAreAlike.halves_are_alike s = ok r →
        Aegis.HalvesAreAlike.halves_are_alike t = ok q → r = q) := by
  sorry

end AegisSpec.HalvesAreAlike
