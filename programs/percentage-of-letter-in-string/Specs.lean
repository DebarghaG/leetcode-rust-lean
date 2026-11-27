import Aegis.PercentageLetter.Code.Funs

/-!
# Specifications of `Aegis.PercentageLetter.percentage_letter`

LeetCode problem `percentage-of-letter-in-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PercentageLetter

def isLowerAscii (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def letterByte (letter : Slice U8) : U8 := letter.val.headD 0#u8

def countOcc (s : Slice U8) (t : U8) : ℕ := (s.val.filter (fun b => b = t)).length

def occurs (s : Slice U8) (t : U8) : Prop := ∃ i : ℕ, ∃ (_ : i < Slice.length s), s.val[i] = t

/-- Let n = len(s), and let c be the number of indices i with 0 <= i < n such that s[i] = letter[0]. The function returns a result r and r = (100 * c) / n, where / denotes integer division rounding down (equivalently, r = floor(100*c/n)).
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_1 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)) :
    ∃ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r ∧
      r.val = ((100 * countOcc s (letterByte letter) / Slice.length s : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)), ∃ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r ∧
      r.val = ((100 * countOcc s (letterByte letter) / Slice.length s : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or go out of bounds) for every input satisfying the preconditions.
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_2 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)) :
    ∃ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)), ∃ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 100.
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_3 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)) :
    ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      0 ≤ r.val ∧ r.val ≤ 100 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)), ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      0 ≤ r.val ∧ r.val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no index i with 0 <= i < len(s) such that s[i] = letter[0].
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_4 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)) :
    ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      (r.val = 0 ↔ ¬ occurs s (letterByte letter)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)), ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      (r.val = 0 ↔ ¬ occurs s (letterByte letter))) := by
  sorry

/-- Whenever the function returns a result r, r = 100 if and only if for every index i with 0 <= i < len(s), s[i] = letter[0].
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_5 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)) :
    ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      (r.val = 100 ↔ ∀ (i : ℕ) (_ : i < Slice.length s), s.val[i] = letterByte letter) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)), ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      (r.val = 100 ↔ ∀ (i : ℕ) (_ : i < Slice.length s), s.val[i] = letterByte letter)) := by
  sorry

/-- Let n = len(s), and let c be the number of indices i with 0 <= i < n such that s[i] = letter[0]. Whenever the function returns a result r, r*n <= 100*c < (r+1)*n.
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_6 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)) :
    ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      r.val * (Slice.length s : ℤ) ≤ 100 * (countOcc s (letterByte letter) : ℤ) ∧
        100 * (countOcc s (letterByte letter) : ℤ) < (r.val + 1) * (Slice.length s : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)), ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      r.val * (Slice.length s : ℤ) ≤ 100 * (countOcc s (letterByte letter) : ℤ) ∧
        100 * (countOcc s (letterByte letter) : ℤ) < (r.val + 1) * (Slice.length s : ℤ)) := by
  sorry

/-- Let n = len(s1) = len(s2), let c1 be the number of indices i with 0 <= i < n such that s1[i] = letter1[0], and let c2 be the number of indices i with 0 <= i < n such that s2[i] = letter2[0]. If c1 <= c2, then whenever the two calls return results r1 and r2 respectively, r1 <= r2.
  Preconditions: For two inputs (s1, letter1) and (s2, letter2): len(s1)=len(s2); each s has length between 1 and 100 inclusive; every byte of each s is an ASCII lowercase English letter; each letter has length 1 and its only byte is an ASCII lowercase English letter. -/
theorem spec_7 (s1 letter1 s2 letter2 : Slice U8)
    (h_s_len_eq : Slice.length s1 = Slice.length s2)
    (h_s1_len_ge : 1 ≤ Slice.length s1) (h_s1_len_le : Slice.length s1 ≤ 100)
    (h_s2_len_ge : 1 ≤ Slice.length s2) (h_s2_len_le : Slice.length s2 ≤ 100)
    (h_s1_lower : ∀ b ∈ s1.val, isLowerAscii b)
    (h_s2_lower : ∀ b ∈ s2.val, isLowerAscii b)
    (h_letter1_len : Slice.length letter1 = 1)
    (h_letter1_lower : isLowerAscii (letterByte letter1))
    (h_letter2_len : Slice.length letter2 = 1)
    (h_letter2_lower : isLowerAscii (letterByte letter2))
    (h_count_le : countOcc s1 (letterByte letter1) ≤ countOcc s2 (letterByte letter2)) :
    ∀ r1 r2 : I64,
      Aegis.PercentageLetter.percentage_letter s1 letter1 = ok r1 →
      Aegis.PercentageLetter.percentage_letter s2 letter2 = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s1 letter1 s2 letter2 : Slice U8)
    (h_s_len_eq : Slice.length s1 = Slice.length s2)
    (h_s1_len_ge : 1 ≤ Slice.length s1) (h_s1_len_le : Slice.length s1 ≤ 100)
    (h_s2_len_ge : 1 ≤ Slice.length s2) (h_s2_len_le : Slice.length s2 ≤ 100)
    (h_s1_lower : ∀ b ∈ s1.val, isLowerAscii b)
    (h_s2_lower : ∀ b ∈ s2.val, isLowerAscii b)
    (h_letter1_len : Slice.length letter1 = 1)
    (h_letter1_lower : isLowerAscii (letterByte letter1))
    (h_letter2_len : Slice.length letter2 = 1)
    (h_letter2_lower : isLowerAscii (letterByte letter2))
    (h_count_le : countOcc s1 (letterByte letter1) ≤ countOcc s2 (letterByte letter2)), ∀ r1 r2 : I64,
      Aegis.PercentageLetter.percentage_letter s1 letter1 = ok r1 →
      Aegis.PercentageLetter.percentage_letter s2 letter2 = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- Let c1 be the number of indices i with 0 <= i < len(s1) such that s1[i] = letter1[0], and let c2 be the number of indices i with 0 <= i < len(s2) such that s2[i] = letter2[0]. If c1 = c2 and len(s1) <= len(s2), then whenever the two calls return results r1 and r2 respectively, r1 >= r2.
  Preconditions: For two inputs (s1, letter1) and (s2, letter2): each s has length between 1 and 100 inclusive; every byte of each s is an ASCII lowercase English letter; each letter has length 1 and its only byte is an ASCII lowercase English letter. -/
theorem spec_8 (s1 letter1 s2 letter2 : Slice U8)
    (h_s1_len_ge : 1 ≤ Slice.length s1) (h_s1_len_le : Slice.length s1 ≤ 100)
    (h_s2_len_ge : 1 ≤ Slice.length s2) (h_s2_len_le : Slice.length s2 ≤ 100)
    (h_s1_lower : ∀ b ∈ s1.val, isLowerAscii b)
    (h_s2_lower : ∀ b ∈ s2.val, isLowerAscii b)
    (h_letter1_len : Slice.length letter1 = 1)
    (h_letter1_lower : isLowerAscii (letterByte letter1))
    (h_letter2_len : Slice.length letter2 = 1)
    (h_letter2_lower : isLowerAscii (letterByte letter2))
    (h_count_eq : countOcc s1 (letterByte letter1) = countOcc s2 (letterByte letter2))
    (h_len_le : Slice.length s1 ≤ Slice.length s2) :
    ∀ r1 r2 : I64,
      Aegis.PercentageLetter.percentage_letter s1 letter1 = ok r1 →
      Aegis.PercentageLetter.percentage_letter s2 letter2 = ok r2 →
      r1.val ≥ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s1 letter1 s2 letter2 : Slice U8)
    (h_s1_len_ge : 1 ≤ Slice.length s1) (h_s1_len_le : Slice.length s1 ≤ 100)
    (h_s2_len_ge : 1 ≤ Slice.length s2) (h_s2_len_le : Slice.length s2 ≤ 100)
    (h_s1_lower : ∀ b ∈ s1.val, isLowerAscii b)
    (h_s2_lower : ∀ b ∈ s2.val, isLowerAscii b)
    (h_letter1_len : Slice.length letter1 = 1)
    (h_letter1_lower : isLowerAscii (letterByte letter1))
    (h_letter2_len : Slice.length letter2 = 1)
    (h_letter2_lower : isLowerAscii (letterByte letter2))
    (h_count_eq : countOcc s1 (letterByte letter1) = countOcc s2 (letterByte letter2))
    (h_len_le : Slice.length s1 ≤ Slice.length s2), ∀ r1 r2 : I64,
      Aegis.PercentageLetter.percentage_letter s1 letter1 = ok r1 →
      Aegis.PercentageLetter.percentage_letter s2 letter2 = ok r2 →
      r1.val ≥ r2.val) := by
  sorry

/-- Let c1 be the number of indices i with 0 <= i < len(s1) such that s1[i] = letter1[0], and let c2 be the number of indices i with 0 <= i < len(s2) such that s2[i] = letter2[0]. If len(s1) = len(s2) and c1 = c2, then whenever the two calls return results r1 and r2 respectively, r1 = r2.
  Preconditions: For two inputs (s1, letter1) and (s2, letter2): each s has length between 1 and 100 inclusive; every byte of each s is an ASCII lowercase English letter; each letter has length 1 and its only byte is an ASCII lowercase English letter. -/
theorem spec_9 (s1 letter1 s2 letter2 : Slice U8)
    (h_s1_len_ge : 1 ≤ Slice.length s1) (h_s1_len_le : Slice.length s1 ≤ 100)
    (h_s2_len_ge : 1 ≤ Slice.length s2) (h_s2_len_le : Slice.length s2 ≤ 100)
    (h_s1_lower : ∀ b ∈ s1.val, isLowerAscii b)
    (h_s2_lower : ∀ b ∈ s2.val, isLowerAscii b)
    (h_letter1_len : Slice.length letter1 = 1)
    (h_letter1_lower : isLowerAscii (letterByte letter1))
    (h_letter2_len : Slice.length letter2 = 1)
    (h_letter2_lower : isLowerAscii (letterByte letter2))
    (h_len_eq : Slice.length s1 = Slice.length s2)
    (h_count_eq : countOcc s1 (letterByte letter1) = countOcc s2 (letterByte letter2)) :
    ∀ r1 r2 : I64,
      Aegis.PercentageLetter.percentage_letter s1 letter1 = ok r1 →
      Aegis.PercentageLetter.percentage_letter s2 letter2 = ok r2 →
      r1.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s1 letter1 s2 letter2 : Slice U8)
    (h_s1_len_ge : 1 ≤ Slice.length s1) (h_s1_len_le : Slice.length s1 ≤ 100)
    (h_s2_len_ge : 1 ≤ Slice.length s2) (h_s2_len_le : Slice.length s2 ≤ 100)
    (h_s1_lower : ∀ b ∈ s1.val, isLowerAscii b)
    (h_s2_lower : ∀ b ∈ s2.val, isLowerAscii b)
    (h_letter1_len : Slice.length letter1 = 1)
    (h_letter1_lower : isLowerAscii (letterByte letter1))
    (h_letter2_len : Slice.length letter2 = 1)
    (h_letter2_lower : isLowerAscii (letterByte letter2))
    (h_len_eq : Slice.length s1 = Slice.length s2)
    (h_count_eq : countOcc s1 (letterByte letter1) = countOcc s2 (letterByte letter2)), ∀ r1 r2 : I64,
      Aegis.PercentageLetter.percentage_letter s1 letter1 = ok r1 →
      Aegis.PercentageLetter.percentage_letter s2 letter2 = ok r2 →
      r1.val = r2.val) := by
  sorry

/-- Let n = len(s). If there exists an index i with 0 <= i < n such that s[i] = letter[0], then whenever the function returns a result r, r >= floor(100/n), where floor is integer division rounding down (for positive n).
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_10 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter))
    (h_occurs : occurs s (letterByte letter)) :
    ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      ((100 / Slice.length s : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter))
    (h_occurs : occurs s (letterByte letter)), ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      ((100 / Slice.length s : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- Let c be the number of indices i with 0 <= i < len(s) such that s[i] = letter[0]. Whenever the function returns a result r, r >= c.
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_11 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)) :
    ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      (countOcc s (letterByte letter) : ℤ) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter)), ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      (countOcc s (letterByte letter) : ℤ) ≤ r.val) := by
  sorry

/-- Let n = len(s), and let c be the number of indices i with 0 <= i < n such that s[i] = letter[0]. If c < n (that is, at least one character differs from letter[0]), then whenever the function returns a result r, r <= floor(100*(n-1)/n), where floor is integer division rounding down.
  Preconditions: len(s) is between 1 and 100 inclusive; every byte of s is an ASCII lowercase English letter ('a' through 'z'); len(letter) = 1; letter[0] is an ASCII lowercase English letter. -/
theorem spec_12 (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter))
    (h_count_lt : countOcc s (letterByte letter) < Slice.length s) :
    ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      r.val ≤ ((100 * (Slice.length s - 1) / Slice.length s : ℕ) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s letter : Slice U8)
    (h_s_len_ge : 1 ≤ Slice.length s) (h_s_len_le : Slice.length s ≤ 100)
    (h_s_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_letter_len : Slice.length letter = 1)
    (h_letter_lower : isLowerAscii (letterByte letter))
    (h_count_lt : countOcc s (letterByte letter) < Slice.length s), ∀ r : I64, Aegis.PercentageLetter.percentage_letter s letter = ok r →
      r.val ≤ ((100 * (Slice.length s - 1) / Slice.length s : ℕ) : ℤ)) := by
  sorry

end AegisSpec.PercentageLetter
