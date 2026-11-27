import Aegis.LongestBeautifulSubstring.Code.Funs

/-!
# Specifications of `Aegis.LongestBeautifulSubstring.longest_beautiful_substring`

LeetCode problem `longest-substring-of-all-vowels-in-order`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestBeautifulSubstring

def vowelCodes : List ℕ := [97, 101, 105, 111, 117]

def IsVowelByte (b : U8) : Prop := b.val ∈ vowelCodes

def byteAt (word : Slice U8) (k : ℕ) : Option U8 :=
  if h : k < word.val.length then some (word.val.get ⟨k, h⟩) else none

def OccursIn (word : Slice U8) (i j : ℕ) (v : ℕ) : Prop :=
  ∃ k, i ≤ k ∧ k < j ∧ ∃ b, byteAt word k = some b ∧ b.val = v

def ContainsAllVowels (word : Slice U8) (i j : ℕ) : Prop :=
  ∀ v ∈ vowelCodes, OccursIn word i j v

def NondecreasingOn (word : Slice U8) (i j : ℕ) : Prop :=
  ∀ k, i ≤ k → k + 1 < j →
    ∃ b₁ b₂, byteAt word k = some b₁ ∧ byteAt word (k + 1) = some b₂ ∧ b₁.val ≤ b₂.val

def Beautiful (word : Slice U8) (i j : ℕ) : Prop :=
  i ≤ j ∧ j ≤ word.val.length ∧ ContainsAllVowels word i j ∧ NondecreasingOn word i j

noncomputable def beautifulLengths (word : Slice U8) : Finset ℕ := by
  classical
  exact (((Finset.range (word.val.length + 1)).product
        (Finset.range (word.val.length + 1))).filter
      (fun p : ℕ × ℕ => Beautiful word p.1 p.2)).image (fun p : ℕ × ℕ => p.2 - p.1)

noncomputable def longestBeautifulLength (word : Slice U8) : ℕ :=
  (beautifulLengths word).sup id

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r, r equals the maximum of the set containing 0 and all integers j-i such that 0 <= i <= j <= len(word) and word[i..j) is beautiful; equivalently, r is the length of a longest beautiful substring of word, or 0 if word has no beautiful substring.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_1 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      r.val = (longestBeautifulLength word : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      r.val = (longestBeautifulLength word : ℤ)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input word satisfying the preconditions.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_2 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∃ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∃ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_3 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(word).
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_4 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      r.val ≤ (word.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      r.val ≤ (word.val.length : ℤ)) := by
  sorry

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r and r > 0, r >= 5.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_5 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 < r.val →
      (5 : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 < r.val →
      (5 : ℤ) ≤ r.val) := by
  sorry

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r and r > 0, there exist indices i and j such that 0 <= i < j <= len(word), j-i = r, and word[i..j) is beautiful.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_6 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 < r.val →
      ∃ i j, i < j ∧ j ≤ word.val.length ∧ ((j - i : ℕ) : ℤ) = r.val ∧ Beautiful word i j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 < r.val →
      ∃ i j, i < j ∧ j ≤ word.val.length ∧ ((j - i : ℕ) : ℤ) = r.val ∧ Beautiful word i j) := by
  sorry

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r, for every i and j with 0 <= i <= j <= len(word), if word[i..j) is beautiful then j-i <= r.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_7 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      ∀ i j, i ≤ j → j ≤ word.val.length → Beautiful word i j → ((j - i : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      ∀ i j, i ≤ j → j ≤ word.val.length → Beautiful word i j → ((j - i : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r and r = 0, there is no beautiful substring of word; that is, for all i and j with 0 <= i <= j <= len(word), word[i..j) is not beautiful.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_8 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → r.val = 0 →
      ∀ i j, i ≤ j → j ≤ word.val.length → ¬ Beautiful word i j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → r.val = 0 →
      ∀ i j, i ≤ j → j ≤ word.val.length → ¬ Beautiful word i j) := by
  sorry

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r, if there is no beautiful substring of word (i.e. for all i and j with 0 <= i <= j <= len(word), word[i..j) is not beautiful), then r = 0.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_9 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      (∀ i j, i ≤ j → j ≤ word.val.length → ¬ Beautiful word i j) → r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      (∀ i j, i ≤ j → j ≤ word.val.length → ¬ Beautiful word i j) → r.val = 0) := by
  sorry

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r and the entire word word[0..len(word)) is beautiful, r = len(word).
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_10 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      Beautiful word 0 word.val.length → r.val = (word.val.length : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      Beautiful word 0 word.val.length → r.val = (word.val.length : ℤ)) := by
  sorry

/-- Here a substring word[i..j) with 0 <= i <= j <= len(word) is called beautiful iff it contains at least one occurrence of each of 'a', 'e', 'i', 'o', 'u' and for every k with i <= k < j-1, word[k] <= word[k+1]. Whenever the function returns a result r and r = len(word), the entire word word[0..len(word)) is beautiful.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_11 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      r.val = (word.val.length : ℤ) → Beautiful word 0 word.val.length := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      r.val = (word.val.length : ℤ) → Beautiful word 0 word.val.length) := by
  sorry

/-- Whenever the function returns a result r and there exists a vowel v in {'a', 'e', 'i', 'o', 'u'} that does not occur anywhere in word, r = 0.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_12 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      (∃ v, v ∈ vowelCodes ∧ ∀ b ∈ word.val, b.val ≠ v) → r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      (∃ v, v ∈ vowelCodes ∧ ∀ b ∈ word.val, b.val ≠ v) → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r and len(word) < 5, r = 0.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_13 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      word.val.length < 5 → r.val = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r →
      word.val.length < 5 → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r and r > 0, each of the five bytes 'a', 'e', 'i', 'o', 'u' occurs at least once somewhere in word.
  Preconditions: 1 <= len(word) <= 500000; every byte of word is one of 'a', 'e', 'i', 'o', 'u' (ASCII codes 97, 101, 105, 111, 117). -/
theorem spec_14 (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b) :
    ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 < r.val →
      ∀ v ∈ vowelCodes, ∃ b ∈ word.val, b.val = v := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (word : Slice U8) (h_len_pos : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 500000) (h_vowels : ∀ b ∈ word.val, IsVowelByte b), ∀ r, Aegis.LongestBeautifulSubstring.longest_beautiful_substring word = ok r → 0 < r.val →
      ∀ v ∈ vowelCodes, ∃ b ∈ word.val, b.val = v) := by
  sorry

end AegisSpec.LongestBeautifulSubstring
