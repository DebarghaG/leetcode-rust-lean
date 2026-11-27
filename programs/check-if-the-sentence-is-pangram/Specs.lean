import Aegis.CheckIfPangram.Code.Funs

/-!
# Specifications of `Aegis.CheckIfPangram.check_if_pangram`

LeetCode problem `check-if-the-sentence-is-pangram`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckIfPangram

def OccursIn (s : Slice Std.U8) (c : Std.U8) : Prop :=
  ∃ i : Nat, ∃ h : i < s.val.length, s.val.get ⟨i, h⟩ = c

def lettersOccurring (s : Slice Std.U8) : Finset Nat :=
  (s.val.map (fun b => b.val)).toFinset.filter (fun v => 97 ≤ v ∧ v ≤ 122)

def distinctLetterCount (s : Slice Std.U8) : Nat := (lettersOccurring s).card

/-- The function returns a result r and r = true if and only if, for every byte c with 97 <= c <= 122, there exists an index i with 0 <= i < len(sentence) and sentence[i] = c. Thus r is true exactly when the sentence contains at least one occurrence of each lowercase English letter from 'a' (97) through 'z' (122), and r is false otherwise.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_1 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122) :
    ∃ r : Bool, Aegis.CheckIfPangram.check_if_pangram sentence = ok r ∧
      (r = true ↔ ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → OccursIn sentence c) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122), ∃ r : Bool, Aegis.CheckIfPangram.check_if_pangram sentence = ok r ∧
      (r = true ↔ ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → OccursIn sentence c)) := by
  sorry

/-- The function returns a result r: it does not fail, panic, or encounter an out-of-bounds index or arithmetic overflow on any input satisfying the preconditions.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_2 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122) :
    ∃ r : Bool, Aegis.CheckIfPangram.check_if_pangram sentence = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122), ∃ r : Bool, Aegis.CheckIfPangram.check_if_pangram sentence = ok r) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every byte c with 97 <= c <= 122 there exists an index i with 0 <= i < len(sentence) and sentence[i] = c.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_3 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_true : r = true) :
    ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → OccursIn sentence c := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_true : r = true), ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → OccursIn sentence c) := by
  sorry

/-- Whenever the function returns a result r with r = false, there exists a byte c with 97 <= c <= 122 such that for every index i with 0 <= i < len(sentence), sentence[i] != c. That is, at least one lowercase English letter does not occur in sentence.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_4 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_false : r = false) :
    ∃ c : Std.U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧
      ∀ (i : Nat) (hi : i < sentence.val.length),
        sentence.val.get ⟨i, hi⟩ ≠ c := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_false : r = false), ∃ c : Std.U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧
      ∀ (i : Nat) (hi : i < sentence.val.length),
        sentence.val.get ⟨i, hi⟩ ≠ c) := by
  sorry

/-- Whenever the function returns a result r with r = true, len(sentence) >= 26.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_5 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_true : r = true) :
    26 ≤ sentence.val.length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_true : r = true), 26 ≤ sentence.val.length) := by
  sorry

/-- Whenever the function returns a result r and len(sentence) < 26, r = false.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_6 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_short : sentence.val.length < 26) :
    r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_short : sentence.val.length < 26), r = false) := by
  sorry

/-- Whenever the function returns a result r, if there exists a byte c such that for every index i with 0 <= i < len(sentence), sentence[i] = c, then r = false.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_7 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_const : ∃ c : Std.U8, ∀ (i : Nat) (hi : i < sentence.val.length),
      sentence.val.get ⟨i, hi⟩ = c) :
    r = false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_const : ∃ c : Std.U8, ∀ (i : Nat) (hi : i < sentence.val.length),
      sentence.val.get ⟨i, hi⟩ = c), r = false) := by
  sorry

/-- Whenever the function returns a result r, if for every byte c with 97 <= c <= 122 there exists an index i with 0 <= i < len(sentence) and sentence[i] = c, then r = true.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_8 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_pangram : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → OccursIn sentence c) :
    r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_pangram : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → OccursIn sentence c), r = true) := by
  sorry

/-- If, for every byte c with 97 <= c <= 122, there exists i with 0 <= i < len(sentence) and sentence[i] = c if and only if there exists j with 0 <= j < len(sentence2) and sentence2[j] = c, then whenever the function returns a result r for sentence and a result r2 for sentence2, r = r2.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122; for the other slice sentence2, 1 <= len(sentence2) <= 1000 and every byte of sentence2 is in 97..122. -/
theorem spec_9 (sentence : Slice Std.U8) (sentence2 : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (h2_len_lo : 1 ≤ sentence2.val.length)
    (h2_len_hi : sentence2.val.length ≤ 1000)
    (h2_lower : ∀ (j : Nat) (hj : j < sentence2.val.length),
      97 ≤ (sentence2.val.get ⟨j, hj⟩).val ∧ (sentence2.val.get ⟨j, hj⟩).val ≤ 122)
    (h_same : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      (OccursIn sentence c ↔ OccursIn sentence2 c))
    (r : Bool) (r2 : Bool)
    (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_run2 : Aegis.CheckIfPangram.check_if_pangram sentence2 = ok r2) :
    r = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sentence : Slice Std.U8) (sentence2 : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (h2_len_lo : 1 ≤ sentence2.val.length)
    (h2_len_hi : sentence2.val.length ≤ 1000)
    (h2_lower : ∀ (j : Nat) (hj : j < sentence2.val.length),
      97 ≤ (sentence2.val.get ⟨j, hj⟩).val ∧ (sentence2.val.get ⟨j, hj⟩).val ≤ 122)
    (h_same : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      (OccursIn sentence c ↔ OccursIn sentence2 c))
    (r : Bool) (r2 : Bool)
    (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_run2 : Aegis.CheckIfPangram.check_if_pangram sentence2 = ok r2), r = r2) := by
  sorry

/-- If every lowercase byte that occurs in sentence also occurs in sentence2 (formally, for every c with 97 <= c <= 122, if there exists i with 0 <= i < len(sentence) and sentence[i] = c then there exists j with 0 <= j < len(sentence2) and sentence2[j] = c), then whenever the function returns a result r for sentence and a result r2 for sentence2, r = true implies r2 = true.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122; for the other slice sentence2, 1 <= len(sentence2) <= 1000 and every byte of sentence2 is in 97..122. -/
theorem spec_10 (sentence : Slice Std.U8) (sentence2 : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (h2_len_lo : 1 ≤ sentence2.val.length)
    (h2_len_hi : sentence2.val.length ≤ 1000)
    (h2_lower : ∀ (j : Nat) (hj : j < sentence2.val.length),
      97 ≤ (sentence2.val.get ⟨j, hj⟩).val ∧ (sentence2.val.get ⟨j, hj⟩).val ≤ 122)
    (h_subset : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      OccursIn sentence c → OccursIn sentence2 c)
    (r : Bool) (r2 : Bool)
    (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_run2 : Aegis.CheckIfPangram.check_if_pangram sentence2 = ok r2)
    (h_true : r = true) :
    r2 = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (sentence : Slice Std.U8) (sentence2 : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (h2_len_lo : 1 ≤ sentence2.val.length)
    (h2_len_hi : sentence2.val.length ≤ 1000)
    (h2_lower : ∀ (j : Nat) (hj : j < sentence2.val.length),
      97 ≤ (sentence2.val.get ⟨j, hj⟩).val ∧ (sentence2.val.get ⟨j, hj⟩).val ≤ 122)
    (h_subset : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      OccursIn sentence c → OccursIn sentence2 c)
    (r : Bool) (r2 : Bool)
    (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_run2 : Aegis.CheckIfPangram.check_if_pangram sentence2 = ok r2)
    (h_true : r = true), r2 = true) := by
  sorry

/-- Let sentence2 be the slice obtained by appending c to the end of sentence. Whenever the function returns a result r for sentence and a result r2 for sentence2, r = r2.
  Preconditions: 1 <= len(sentence) <= 1000; every byte of sentence is in 97..122; c is a byte with 97 <= c <= 122; len(sentence) < 1000; c occurs in sentence (there exists i with 0 <= i < len(sentence) and sentence[i] = c). -/
theorem spec_11 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (c : Std.U8) (hc_lo : 97 ≤ c.val) (hc_hi : c.val ≤ 122)
    (h_len_lt : sentence.val.length < 1000)
    (hc_occ : OccursIn sentence c)
    (sentence2 : Slice Std.U8)
    (h_sentence2 : sentence2.val = sentence.val ++ [c])
    (r : Bool) (r2 : Bool)
    (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_run2 : Aegis.CheckIfPangram.check_if_pangram sentence2 = ok r2) :
    r = r2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (c : Std.U8) (hc_lo : 97 ≤ c.val) (hc_hi : c.val ≤ 122)
    (h_len_lt : sentence.val.length < 1000)
    (hc_occ : OccursIn sentence c)
    (sentence2 : Slice Std.U8)
    (h_sentence2 : sentence2.val = sentence.val ++ [c])
    (r : Bool) (r2 : Bool)
    (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_run2 : Aegis.CheckIfPangram.check_if_pangram sentence2 = ok r2), r = r2) := by
  sorry

/-- Whenever the function returns a result r, if exactly 25 distinct byte values c with 97 <= c <= 122 occur in sentence (that is, exactly 25 different lowercase English letters have an occurrence), then r = false.
  Preconditions: 1 <= len(sentence) <= 1000; for every index i with 0 <= i < len(sentence), 97 <= sentence[i] <= 122. -/
theorem spec_12 (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_count : distinctLetterCount sentence = 25) :
    r = false := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len_lo : 1 ≤ sentence.val.length)
    (h_len_hi : sentence.val.length ≤ 1000)
    (h_lower : ∀ (i : Nat) (hi : i < sentence.val.length),
      97 ≤ (sentence.val.get ⟨i, hi⟩).val ∧ (sentence.val.get ⟨i, hi⟩).val ≤ 122)
    (r : Bool) (h_run : Aegis.CheckIfPangram.check_if_pangram sentence = ok r)
    (h_count : distinctLetterCount sentence = 25), r = false) := by
  sorry

end AegisSpec.CheckIfPangram
