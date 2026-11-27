import Aegis.DetectCapitalUse.Code.Funs

/-!
# Specifications of `Aegis.DetectCapitalUse.detect_capital_use`

LeetCode problem `detect-capital`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DetectCapitalUse

def isUpper (c : U8) : Prop := 65 ≤ c.val ∧ c.val ≤ 90

def isLower (c : U8) : Prop := 97 ≤ c.val ∧ c.val ≤ 122

def isLetter (c : U8) : Prop := isUpper c ∨ isLower c

def allLetters (word : Slice U8) : Prop :=
  ∀ (i : Nat) (hi : i < word.val.length), isLetter word.val[i]

def allUpper (word : Slice U8) : Prop :=
  ∀ (i : Nat) (hi : i < word.val.length), isUpper word.val[i]

def allLower (word : Slice U8) : Prop :=
  ∀ (i : Nat) (hi : i < word.val.length), isLower word.val[i]

def allLowerFromOne (word : Slice U8) : Prop :=
  ∀ (i : Nat) (hpos : 1 ≤ i) (hi : i < word.val.length), isLower word.val[i]

def isUpperB (c : U8) : Bool := decide (65 ≤ c.val) && decide (c.val ≤ 90)

theorem isUpperB_eq_true (c : U8) : isUpperB c = true ↔ isUpper c := by
  simp [isUpperB, isUpper]

def upperCount (word : Slice U8) : Nat := word.val.countP isUpperB

/-- The function returns a result r (so it does not fail), and r = true if and only if at least one of the following three conditions holds: (1) every byte word[i] with 0 <= i < len(word) is uppercase; (2) every byte word[i] with 0 <= i < len(word) is lowercase; (3) word[0] is uppercase and every byte word[i] with 1 <= i < len(word) is lowercase.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, and every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_1 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔
        (allUpper word ∨ allLower word ∨
          (isUpper word.val[0] ∧ allLowerFromOne word))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔
        (allUpper word ∨ allLower word ∨
          (isUpper word.val[0] ∧ allLowerFromOne word)))) := by
  sorry

/-- For every input word satisfying the preconditions, the function returns a result r; it does not panic, overflow, or index out of bounds.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, and every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_2 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122), and len(word) = 1. -/
theorem spec_3 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (hlen : word.val.length = 1) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (hlen : word.val.length = 1), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧ r = true) := by
  sorry

/-- The function returns a result r and r = true if and only if it is not the case that word[0] is lowercase and word[1] is uppercase.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122), and len(word) = 2. -/
theorem spec_4 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (hlen : word.val.length = 2) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ ¬ (isLower word.val[0] ∧ isUpper word.val[1])) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (hlen : word.val.length = 2), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ ¬ (isLower word.val[0] ∧ isUpper word.val[1]))) := by
  sorry

/-- The function returns a result r and r = true if and only if every byte word[i] with 0 <= i < len(word) is lowercase.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122), and word[0] is lowercase. -/
theorem spec_5 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (h0 : isLower word.val[0]) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ allLower word) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (h0 : isLower word.val[0]), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ allLower word)) := by
  sorry

/-- The function returns a result r and r = true if and only if every byte word[i] with 0 <= i < len(word) is uppercase.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122), len(word) >= 2, and word[1] is uppercase. -/
theorem spec_6 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (hlen2 : 2 ≤ word.val.length)
    (h1 : isUpper word.val[1]) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ allUpper word) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) (hlen2 : 2 ≤ word.val.length)
    (h1 : isUpper word.val[1]), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ allUpper word)) := by
  sorry

/-- The function returns a result r and r = true if and only if word[0] is uppercase and every byte word[i] with 1 <= i < len(word) is lowercase.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122), there exists an index i with 0 <= i < len(word) such that word[i] is uppercase, and there exists an index j with 0 <= j < len(word) such that word[j] is lowercase. -/
theorem spec_7 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word)
    (hupper : ∃ (i : Nat) (hi : i < word.val.length), isUpper word.val[i])
    (hlower : ∃ (j : Nat) (hj : j < word.val.length), isLower word.val[j]) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ isUpper word.val[0] ∧ allLowerFromOne word) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word)
    (hupper : ∃ (i : Nat) (hi : i < word.val.length), isUpper word.val[i])
    (hlower : ∃ (j : Nat) (hj : j < word.val.length), isLower word.val[j]), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔ isUpper word.val[0] ∧ allLowerFromOne word)) := by
  sorry

/-- The function returns a result r and r = false if and only if there exists an index i with 0 <= i < len(word) such that word[i] is lowercase, and there exists an index j with 1 <= j < len(word) such that word[j] is uppercase.
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, and every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_8 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = false ↔
        (∃ (i : Nat) (hi : i < word.val.length), isLower word.val[i]) ∧
          (∃ (j : Nat) (hj1 : 1 ≤ j) (hj : j < word.val.length), isUpper word.val[j])) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = false ↔
        (∃ (i : Nat) (hi : i < word.val.length), isLower word.val[i]) ∧
          (∃ (j : Nat) (hj1 : 1 ≤ j) (hj : j < word.val.length), isUpper word.val[j]))) := by
  sorry

/-- Let k be the number of indices i with 0 <= i < len(word) such that word[i] is uppercase. The function returns a result r and r = true if and only if k = len(word) or k = 0 or (k = 1 and word[0] is uppercase).
  Preconditions: word is a slice of bytes with 1 <= len(word) <= 100, and every byte word[i] with 0 <= i < len(word) is an uppercase English letter (65 <= word[i] <= 90) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_9 (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word) :
    ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔
        upperCount word = word.val.length ∨ upperCount word = 0 ∨
          (upperCount word = 1 ∧ isUpper word.val[0])) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice U8)
    (hlen1 : 1 ≤ word.val.length) (hlen100 : word.val.length ≤ 100)
    (hletter : allLetters word), ∃ r, Aegis.DetectCapitalUse.detect_capital_use word = ok r ∧
      (r = true ↔
        upperCount word = word.val.length ∨ upperCount word = 0 ∨
          (upperCount word = 1 ∧ isUpper word.val[0]))) := by
  sorry

/-- Whenever detect_capital_use(word) returns a result r_word and detect_capital_use(other) returns a result r_other, we have r_word = r_other.
  Preconditions: word and other are slices of bytes with 1 <= len(word) <= 100, 1 <= len(other) <= 100, every byte of each is an uppercase English letter (65..90) or a lowercase English letter (97..122), len(word) = len(other), and for every i with 0 <= i < len(word), word[i] is uppercase if and only if other[i] is uppercase. -/
theorem spec_10 (word other : Slice U8)
    (hw1 : 1 ≤ word.val.length) (hw100 : word.val.length ≤ 100)
    (ho1 : 1 ≤ other.val.length) (ho100 : other.val.length ≤ 100)
    (hw_letter : allLetters word) (ho_letter : allLetters other)
    (hlen : word.val.length = other.val.length)
    (hagree : ∀ (i : Nat) (hi : i < word.val.length),
      (isUpper word.val[i] ↔ isUpper other.val[i])) :
    ∀ (r_word r_other : Bool),
      Aegis.DetectCapitalUse.detect_capital_use word = ok r_word →
        Aegis.DetectCapitalUse.detect_capital_use other = ok r_other →
          r_word = r_other := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word other : Slice U8)
    (hw1 : 1 ≤ word.val.length) (hw100 : word.val.length ≤ 100)
    (ho1 : 1 ≤ other.val.length) (ho100 : other.val.length ≤ 100)
    (hw_letter : allLetters word) (ho_letter : allLetters other)
    (hlen : word.val.length = other.val.length)
    (hagree : ∀ (i : Nat) (hi : i < word.val.length),
      (isUpper word.val[i] ↔ isUpper other.val[i])), ∀ (r_word r_other : Bool),
      Aegis.DetectCapitalUse.detect_capital_use word = ok r_word →
        Aegis.DetectCapitalUse.detect_capital_use other = ok r_other →
          r_word = r_other) := by
  sorry

end AegisSpec.DetectCapitalUse
