import Aegis.NumberOfSpecialChars.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSpecialChars.number_of_special_chars`

LeetCode problem `count-the-number-of-special-characters-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfSpecialChars

def L (k : Nat) : Nat := 97 + k

def U (k : Nat) : Nat := 65 + k

abbrev IsLowerByte (b : Nat) : Prop := 97 ≤ b ∧ b ≤ 122

abbrev IsUpperByte (b : Nat) : Prop := 65 ≤ b ∧ b ≤ 90

abbrev IsLetterByte (b : Nat) : Prop := IsLowerByte b ∨ IsUpperByte b

def AllLetterBytes (w : List Std.U8) : Prop := ∀ b ∈ w, IsLetterByte b.val

abbrev Occurs (w : List Std.U8) (b : Nat) : Prop := b ∈ w.map (fun x => x.val)

abbrev OccursL (w : List Std.U8) (k : Nat) : Prop := Occurs w (L k)

abbrev OccursU (w : List Std.U8) (k : Nat) : Prop := Occurs w (U k)

abbrev OccursBoth (w : List Std.U8) (k : Nat) : Prop := OccursL w k ∧ OccursU w k

abbrev LowersPrecedeUppers (w : List Std.U8) (k : Nat) : Prop :=
  ∀ i j : Fin w.length, (w.get i).val = L k → (w.get j).val = U k → i.val < j.val

abbrev IsSpecial (w : List Std.U8) (k : Nat) : Prop :=
  OccursBoth w k ∧ LowersPrecedeUppers w k

abbrev UpperBeforeLower (w : List Std.U8) (k : Nat) : Prop :=
  ∃ i j : Fin w.length, i.val < j.val ∧ (w.get i).val = U k ∧ (w.get j).val = L k

abbrev IsLastIndex (w : List Std.U8) (b : Nat) (i : Fin w.length) : Prop :=
  (w.get i).val = b ∧ ∀ j : Fin w.length, i.val < j.val → (w.get j).val ≠ b

abbrev IsFirstIndex (w : List Std.U8) (b : Nat) (j : Fin w.length) : Prop :=
  (w.get j).val = b ∧ ∀ i : Fin w.length, i.val < j.val → (w.get i).val ≠ b

def countK (p : Nat → Prop) [DecidablePred p] : Nat :=
  ((List.range 26).filter (fun k => decide (p k))).length

abbrev IsAppendByte (w w2 : List Std.U8) (c : Nat) : Prop :=
  w2.map (fun x => x.val) = w.map (fun x => x.val) ++ [c]

def swapCase (b : Nat) : Nat :=
  if 97 ≤ b ∧ b ≤ 122 then b - 32 else if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

abbrev reversedSwapCaseValues (w : List Std.U8) : List Nat :=
  w.reverse.map (fun x => swapCase x.val)

abbrev IsReversedSwapCase (w w2 : List Std.U8) : Prop :=
  w2.map (fun x => x.val) = reversedSwapCaseValues w

/-- The function returns a result r and r equals the number of k with 0 <= k < 26 satisfying all three conditions: (1) there exists i with 0 <= i < len(word) and word[i] = L_k; (2) there exists j with 0 <= j < len(word) and word[j] = U_k; and (3) for every i and j with 0 <= i < len(word), 0 <= j < len(word), if word[i] = L_k and word[j] = U_k then i < j. Here L_k = 97 + k and U_k = 65 + k.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_1 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∃ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r ∧
        r.val = (countK (fun k => IsSpecial word.val k) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∃ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r ∧
        r.val = (countK (fun k => IsSpecial word.val k) : Int)) := by
  sorry

/-- For every word satisfying the preconditions, the function returns a result r; it does not fail, overflow, go out of bounds, or panic.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_2 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∃ r : Std.I64, Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∃ r : Std.I64, Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 26.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_3 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        0 ≤ r.val ∧ r.val ≤ 26 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        0 ≤ r.val ∧ r.val ≤ 26) := by
  sorry

/-- Whenever the function returns a result r, r is at most the number of k with 0 <= k < 26 for which both L_k = 97 + k and U_k = 65 + k occur at least once in word.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_4 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        r.val ≤ (countK (fun k => OccursBoth word.val k) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        r.val ≤ (countK (fun k => OccursBoth word.val k) : Int)) := by
  sorry

/-- Whenever the function returns a result r and len(word) = 1, r = 0.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_5 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        word.val.length = 1 → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        word.val.length = 1 → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if there is no index i with 0 <= i < len(word) and 97 <= word[i] <= 122, then r = 0.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_6 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (¬ ∃ i : Fin word.val.length, IsLowerByte (word.val.get i).val) → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (¬ ∃ i : Fin word.val.length, IsLowerByte (word.val.get i).val) → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if there is no index i with 0 <= i < len(word) and 65 <= word[i] <= 90, then r = 0.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_7 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (¬ ∃ i : Fin word.val.length, IsUpperByte (word.val.get i).val) → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (¬ ∃ i : Fin word.val.length, IsUpperByte (word.val.get i).val) → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if for every k with 0 <= k < 26 such that both L_k = 97 + k and U_k = 65 + k occur in word, there exist indices i and j with 0 <= i,j < len(word), word[i] = U_k, word[j] = L_k, and i < j, then r = 0.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_8 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (∀ k, k < 26 → OccursBoth word.val k → UpperBeforeLower word.val k) → r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (∀ k, k < 26 → OccursBoth word.val k → UpperBeforeLower word.val k) → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if for every i and j with 0 <= i,j < len(word), whenever 97 <= word[i] <= 122 and 65 <= word[j] <= 90 we have i < j, then r equals the number of k with 0 <= k < 26 for which both L_k = 97 + k and U_k = 65 + k occur in word.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_9 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (∀ i j : Fin word.val.length,
          IsLowerByte (word.val.get i).val → IsUpperByte (word.val.get j).val →
            i.val < j.val) →
          r.val = (countK (fun k => OccursBoth word.val k) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (∀ i j : Fin word.val.length,
          IsLowerByte (word.val.get i).val → IsUpperByte (word.val.get j).val →
            i.val < j.val) →
          r.val = (countK (fun k => OccursBoth word.val k) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exists k with 0 <= k < 26 such that both L_k = 97 + k and U_k = 65 + k occur in word and for every i and j with 0 <= i,j < len(word), if word[i] = L_k and word[j] = U_k then i < j.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_10 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (0 < r.val ↔ ∃ k, k < 26 ∧ IsSpecial word.val k) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (0 < r.val ↔ ∃ k, k < 26 ∧ IsSpecial word.val k)) := by
  sorry

/-- Whenever the function returns a result r, r = 26 if and only if for every k with 0 <= k < 26, both L_k = 97 + k and U_k = 65 + k occur in word and for every i and j with 0 <= i,j < len(word), if word[i] = L_k and word[j] = U_k then i < j.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_11 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (r.val = 26 ↔ ∀ k, k < 26 → IsSpecial word.val k) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        (r.val = 26 ↔ ∀ k, k < 26 → IsSpecial word.val k)) := by
  sorry

/-- Suppose that for every i with 0 <= i < len(word), word2[i] is obtained from word[len(word)-1-i] by swapping ASCII case: if word[len(word)-1-i] is in 97..122 then word2[i] = word[len(word)-1-i] - 32, and if word[len(word)-1-i] is in 65..90 then word2[i] = word[len(word)-1-i] + 32. Then whenever the function returns r on word and r2 on word2, r = r2.
  Preconditions: word and word2 are byte arrays with lengths in 1..200000, len(word2) = len(word), and every byte of each is a lowercase or uppercase English letter. -/
theorem spec_12 (word word2 : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hlen_pos2 : 1 ≤ word2.val.length) (hlen_le2 : word2.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) (hletters2 : AllLetterBytes word2.val)
    (hlen_eq : word2.val.length = word.val.length)
    (hrev : IsReversedSwapCase word.val word2.val) :
    ∀ r r2 : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word word2 : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hlen_pos2 : 1 ≤ word2.val.length) (hlen_le2 : word2.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) (hletters2 : AllLetterBytes word2.val)
    (hlen_eq : word2.val.length = word.val.length)
    (hrev : IsReversedSwapCase word.val word2.val), ∀ r r2 : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2 → r.val = r2.val) := by
  sorry

/-- Whenever the function returns a result r, if there exists k with 0 <= k < 26 such that every byte of word is either L_k = 97 + k or U_k = 65 + k, then r = 1 if both L_k and U_k occur in word and for every i and j with 0 <= i,j < len(word), if word[i] = L_k and word[j] = U_k then i < j; otherwise r = 0.
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 (lowercase English letter) or 65..90 (uppercase English letter). -/
theorem spec_13 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ k, k < 26 → (∀ b ∈ word.val, b.val = L k ∨ b.val = U k) →
      ∀ r : Std.I64,
        Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
          r.val = (if IsSpecial word.val k then (1 : Int) else 0) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ k, k < 26 → (∀ b ∈ word.val, b.val = L k ∨ b.val = U k) →
      ∀ r : Std.I64,
        Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
          r.val = (if IsSpecial word.val k then (1 : Int) else 0)) := by
  sorry

/-- Whenever the function returns a result r, for each k with 0 <= k < 26 let lastL(k) be the largest index i with word[i] = L_k = 97+k, if it exists, and let firstU(k) be the smallest index j with word[j] = U_k = 65+k, if it exists. Then r equals the number of k for which both lastL(k) and firstU(k) exist and lastL(k) < firstU(k).
  Preconditions: len(word) is an integer with 1 <= len(word) <= 200000, and for every i with 0 <= i < len(word), word[i] is an ASCII byte in 97..122 or 65..90. -/
theorem spec_14 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        r.val = (countK (fun k => ∃ i j : Fin word.val.length,
          IsLastIndex word.val (L k) i ∧ IsFirstIndex word.val (U k) j ∧ i.val < j.val) :
            Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val), ∀ r : Std.I64,
      Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
        r.val = (countK (fun k => ∃ i j : Fin word.val.length,
          IsLastIndex word.val (L k) i ∧ IsFirstIndex word.val (U k) j ∧ i.val < j.val) :
            Int)) := by
  sorry

/-- Whenever the function returns r on word and r2 on word2, if the appended byte is an uppercase letter U_k, then r2 >= r; if the appended byte is a lowercase letter L_k, then r2 <= r.
  Preconditions: word and word2 are byte arrays with lengths in 1..200000, every byte is a lowercase or uppercase English letter, len(word) < 200000, len(word2) = len(word)+1, word2[i] = word[i] for 0 <= i < len(word), and word2[len(word)] is either U_k = 65+k or L_k = 97+k for some k with 0 <= k < 26. -/
theorem spec_15 (word word2 : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hlen_pos2 : 1 ≤ word2.val.length) (hlen_le2 : word2.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) (hletters2 : AllLetterBytes word2.val)
    (hlen_lt : word.val.length < 200000)
    (happend : ∃ k, k < 26 ∧
      (IsAppendByte word.val word2.val (U k) ∨ IsAppendByte word.val word2.val (L k))) :
    (∀ k, k < 26 → IsAppendByte word.val word2.val (U k) →
        ∀ r r2 : Std.I64,
          Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
            Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2 →
              r.val ≤ r2.val) ∧
    (∀ k, k < 26 → IsAppendByte word.val word2.val (L k) →
        ∀ r r2 : Std.I64,
          Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
            Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2 →
              r2.val ≤ r.val) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (word word2 : Slice Std.U8)
    (hlen_pos : 1 ≤ word.val.length) (hlen_le : word.val.length ≤ 200000)
    (hlen_pos2 : 1 ≤ word2.val.length) (hlen_le2 : word2.val.length ≤ 200000)
    (hletters : AllLetterBytes word.val) (hletters2 : AllLetterBytes word2.val)
    (hlen_lt : word.val.length < 200000)
    (happend : ∃ k, k < 26 ∧
      (IsAppendByte word.val word2.val (U k) ∨ IsAppendByte word.val word2.val (L k))), (∀ k, k < 26 → IsAppendByte word.val word2.val (U k) →
        ∀ r r2 : Std.I64,
          Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
            Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2 →
              r.val ≤ r2.val) ∧
    (∀ k, k < 26 → IsAppendByte word.val word2.val (L k) →
        ∀ r r2 : Std.I64,
          Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r →
            Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2 →
              r2.val ≤ r.val)) := by
  sorry

end AegisSpec.NumberOfSpecialChars
