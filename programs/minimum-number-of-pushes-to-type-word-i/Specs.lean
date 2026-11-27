import Aegis.MinimumPushes.Code.Funs

/-!
# Specifications of `Aegis.MinimumPushes.minimum_pushes`

LeetCode problem `minimum-number-of-pushes-to-type-word-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumPushes (minimum_pushes)

namespace AegisSpec.MinimumPushes

def allLowercase (word : Slice U8) : Prop :=
  ∀ (i : ℕ) (hi : i < word.val.length), 97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122

def allDistinct (word : Slice U8) : Prop :=
  ∀ (i j : ℕ) (hi : i < word.val.length) (hj : j < word.val.length),
    i < j → word.val[i]'hi ≠ word.val[j]'hj

def ind (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

def countKey (word : Slice U8) (key : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range word.val.length).filter (fun i => key i = k)).card

structure Layout (word : Slice U8) where

  key : ℕ → ℕ

  push : ℕ → ℕ

  key_ge : ∀ i, i < word.val.length → 2 ≤ key i

  key_le : ∀ i, i < word.val.length → key i ≤ 9

  push_ge : ∀ i, i < word.val.length → 1 ≤ push i

  push_le : ∀ i, i < word.val.length → push i ≤ countKey word key (key i)

  push_inj : ∀ i j, i < word.val.length → j < word.val.length →
    key i = key j → push i = push j → i = j

namespace Layout

variable {word : Slice U8}

def keyCount (L : Layout word) (k : ℕ) : ℕ := countKey word L.key k

def total (L : Layout word) : ℤ := ∑ i ∈ Finset.range word.val.length, (L.push i : ℤ)

end Layout

/-- Whenever the function returns a result r, r = n + max(0, n - 8) + max(0, n - 16) + max(0, n - 24).
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122 (word[i] is a lowercase English letter); and for every i, j with 0 <= i < j < n, word[i] != word[j]. -/
theorem spec_1 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word) :
    ∀ r : I64, minimum_pushes word = ok r →
      r.val = (word.val.length : ℤ) + max 0 ((word.val.length : ℤ) - 8)
        + max 0 ((word.val.length : ℤ) - 16) + max 0 ((word.val.length : ℤ) - 24) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word), ∀ r : I64, minimum_pushes word = ok r →
      r.val = (word.val.length : ℤ) + max 0 ((word.val.length : ℤ) - 8)
        + max 0 ((word.val.length : ℤ) - 16) + max 0 ((word.val.length : ℤ) - 24)) := by
  sorry

/-- The function returns a result (it does not fail) for every word satisfying the preconditions.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; and for every i, j with 0 <= i < j < n, word[i] != word[j]. -/
theorem spec_2 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word) :
    ∃ r : I64, minimum_pushes word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word), ∃ r : I64, minimum_pushes word = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= n.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; and for every i, j with 0 <= i < j < n, word[i] != word[j]. -/
theorem spec_3 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word) :
    ∀ r : I64, minimum_pushes word = ok r → (word.val.length : ℤ) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word), ∀ r : I64, minimum_pushes word = ok r → (word.val.length : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 56.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; and for every i, j with 0 <= i < j < n, word[i] != word[j]. -/
theorem spec_4 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word) :
    ∀ r : I64, minimum_pushes word = ok r → r.val ≤ 56 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word), ∀ r : I64, minimum_pushes word = ok r → r.val ≤ 56) := by
  sorry

/-- Whenever the function returns r1 on word1 and r2 on word2, if n1 = n2 then r1 = r2.
  Preconditions: Let n1 = len(word1) and n2 = len(word2). Both word1 and word2 satisfy: 1 <= n1, n2 <= 26; all their bytes are lowercase English letters (97..122); and all letters within each word are distinct. -/
theorem spec_5 (word1 word2 : Slice U8)
    (hpos1 : 1 ≤ word1.val.length) (hlen1 : word1.val.length ≤ 26)
    (hlower1 : allLowercase word1) (hdistinct1 : allDistinct word1)
    (hpos2 : 1 ≤ word2.val.length) (hlen2 : word2.val.length ≤ 26)
    (hlower2 : allLowercase word2) (hdistinct2 : allDistinct word2) :
    ∀ r1 r2 : I64, minimum_pushes word1 = ok r1 → minimum_pushes word2 = ok r2 →
      word1.val.length = word2.val.length → r1.val = r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word1 word2 : Slice U8)
    (hpos1 : 1 ≤ word1.val.length) (hlen1 : word1.val.length ≤ 26)
    (hlower1 : allLowercase word1) (hdistinct1 : allDistinct word1)
    (hpos2 : 1 ≤ word2.val.length) (hlen2 : word2.val.length ≤ 26)
    (hlower2 : allLowercase word2) (hdistinct2 : allDistinct word2), ∀ r1 r2 : I64, minimum_pushes word1 = ok r1 → minimum_pushes word2 = ok r2 →
      word1.val.length = word2.val.length → r1.val = r2.val) := by
  sorry

/-- Whenever the function returns r1 on word1 and r2 on word2, if n1 <= n2 then r1 <= r2.
  Preconditions: Let n1 = len(word1) and n2 = len(word2). Both word1 and word2 satisfy: 1 <= n1, n2 <= 26; all their bytes are lowercase English letters (97..122); and all letters within each word are distinct. -/
theorem spec_6 (word1 word2 : Slice U8)
    (hpos1 : 1 ≤ word1.val.length) (hlen1 : word1.val.length ≤ 26)
    (hlower1 : allLowercase word1) (hdistinct1 : allDistinct word1)
    (hpos2 : 1 ≤ word2.val.length) (hlen2 : word2.val.length ≤ 26)
    (hlower2 : allLowercase word2) (hdistinct2 : allDistinct word2) :
    ∀ r1 r2 : I64, minimum_pushes word1 = ok r1 → minimum_pushes word2 = ok r2 →
      word1.val.length ≤ word2.val.length → r1.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word1 word2 : Slice U8)
    (hpos1 : 1 ≤ word1.val.length) (hlen1 : word1.val.length ≤ 26)
    (hlower1 : allLowercase word1) (hdistinct1 : allDistinct word1)
    (hpos2 : 1 ≤ word2.val.length) (hlen2 : word2.val.length ≤ 26)
    (hlower2 : allLowercase word2) (hdistinct2 : allDistinct word2), ∀ r1 r2 : I64, minimum_pushes word1 = ok r1 → minimum_pushes word2 = ok r2 →
      word1.val.length ≤ word2.val.length → r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns a result r, for every valid remapping of the n letters of word onto keys 2 through 9 and every ordering of the letters assigned to each key, the total number of pushes is at least r, where the push count of a letter is its 1-based position in the ordering of its assigned key and the total is the sum of these counts over all n letters.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; and for every i, j with 0 <= i < j < n, word[i] != word[j]. -/
theorem spec_7 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word) :
    ∀ r : I64, minimum_pushes word = ok r →
      ∀ L : Layout word, r.val ≤ L.total := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word), ∀ r : I64, minimum_pushes word = ok r →
      ∀ L : Layout word, r.val ≤ L.total) := by
  sorry

/-- Whenever the function returns a result r, there exists a valid remapping of the n letters of word onto keys 2 through 9 and an ordering of the letters assigned to each key such that the total number of pushes is exactly r and every key is assigned at most 4 letters.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; and for every i, j with 0 <= i < j < n, word[i] != word[j]. -/
theorem spec_8 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word) :
    ∀ r : I64, minimum_pushes word = ok r →
      ∃ L : Layout word, L.total = r.val ∧ ∀ k : ℕ, L.keyCount k ≤ 4 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word), ∀ r : I64, minimum_pushes word = ok r →
      ∃ L : Layout word, L.total = r.val ∧ ∀ k : ℕ, L.keyCount k ≤ 4) := by
  sorry

/-- Whenever the function returns r1 on word1 and r2 on word2, r2 - r1 = 1 + [n >= 8] + [n >= 16] + [n >= 24], where [P] is 1 when P is true and 0 otherwise.
  Preconditions: Let n1 = len(word1) and n2 = len(word2). Both word1 and word2 satisfy: 1 <= n1, n2 <= 26; all their bytes are lowercase English letters (97..122); and all letters within each word are distinct. Also n2 = n1 + 1, and let n = n1. -/
theorem spec_9 (word1 word2 : Slice U8)
    (hpos1 : 1 ≤ word1.val.length) (hlen1 : word1.val.length ≤ 26)
    (hlower1 : allLowercase word1) (hdistinct1 : allDistinct word1)
    (hpos2 : 1 ≤ word2.val.length) (hlen2 : word2.val.length ≤ 26)
    (hlower2 : allLowercase word2) (hdistinct2 : allDistinct word2)
    (hsucc : word2.val.length = word1.val.length + 1) :
    ∀ r1 r2 : I64, minimum_pushes word1 = ok r1 → minimum_pushes word2 = ok r2 →
      r2.val - r1.val = 1 + ind (8 ≤ (word1.val.length : ℤ))
        + ind (16 ≤ (word1.val.length : ℤ)) + ind (24 ≤ (word1.val.length : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word1 word2 : Slice U8)
    (hpos1 : 1 ≤ word1.val.length) (hlen1 : word1.val.length ≤ 26)
    (hlower1 : allLowercase word1) (hdistinct1 : allDistinct word1)
    (hpos2 : 1 ≤ word2.val.length) (hlen2 : word2.val.length ≤ 26)
    (hlower2 : allLowercase word2) (hdistinct2 : allDistinct word2)
    (hsucc : word2.val.length = word1.val.length + 1), ∀ r1 r2 : I64, minimum_pushes word1 = ok r1 → minimum_pushes word2 = ok r2 →
      r2.val - r1.val = 1 + ind (8 ≤ (word1.val.length : ℤ))
        + ind (16 ≤ (word1.val.length : ℤ)) + ind (24 ≤ (word1.val.length : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, every remapping whose total number of pushes is r uses all eight keys; exactly two keys are assigned 4 letters and the other six keys are assigned 3 letters.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; for every i, j with 0 <= i < j < n, word[i] != word[j]; and n = 26. -/
theorem spec_10 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word)
    (h26 : word.val.length = 26) :
    ∀ r : I64, minimum_pushes word = ok r →
      ∀ L : Layout word, L.total = r.val →
        (∀ k ∈ Finset.Icc (2 : ℕ) 9, 0 < L.keyCount k) ∧
          ((Finset.Icc (2 : ℕ) 9).filter (fun k => L.keyCount k = 4)).card = 2 ∧
          (∀ k ∈ Finset.Icc (2 : ℕ) 9, L.keyCount k = 4 ∨ L.keyCount k = 3) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word)
    (h26 : word.val.length = 26), ∀ r : I64, minimum_pushes word = ok r →
      ∀ L : Layout word, L.total = r.val →
        (∀ k ∈ Finset.Icc (2 : ℕ) 9, 0 < L.keyCount k) ∧
          ((Finset.Icc (2 : ℕ) 9).filter (fun k => L.keyCount k = 4)).card = 2 ∧
          (∀ k ∈ Finset.Icc (2 : ℕ) 9, L.keyCount k = 4 ∨ L.keyCount k = 3)) := by
  sorry

/-- Whenever the function returns a result r, there exists a remapping whose total number of pushes is r and in which each of the n letters is assigned to a different key, so every letter has push count 1.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; for every i, j with 0 <= i < j < n, word[i] != word[j]; and n <= 8. -/
theorem spec_11 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word)
    (h8 : word.val.length ≤ 8) :
    ∀ r : I64, minimum_pushes word = ok r →
      ∃ L : Layout word,
        L.total = r.val ∧
          (∀ i j, i < word.val.length → j < word.val.length → L.key i = L.key j → i = j) ∧
          (∀ i, i < word.val.length → L.push i = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word)
    (h8 : word.val.length ≤ 8), ∀ r : I64, minimum_pushes word = ok r →
      ∃ L : Layout word,
        L.total = r.val ∧
          (∀ i j, i < word.val.length → j < word.val.length → L.key i = L.key j → i = j) ∧
          (∀ i, i < word.val.length → L.push i = 1)) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if n <= 8.
  Preconditions: Let n = len(word). The input satisfies: 1 <= n <= 26; for every i with 0 <= i < n, 97 <= word[i] <= 122; and for every i, j with 0 <= i < j < n, word[i] != word[j]. -/
theorem spec_12 (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word) :
    ∀ r : I64, minimum_pushes word = ok r →
      (r.val = (word.val.length : ℤ) ↔ word.val.length ≤ 8) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word : Slice U8)
    (hpos : 1 ≤ word.val.length) (hlen : word.val.length ≤ 26)
    (hlower : allLowercase word) (hdistinct : allDistinct word), ∀ r : I64, minimum_pushes word = ok r →
      (r.val = (word.val.length : ℤ) ↔ word.val.length ≤ 8)) := by
  sorry

end AegisSpec.MinimumPushes
