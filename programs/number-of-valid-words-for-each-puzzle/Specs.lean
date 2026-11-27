import Aegis.FindNumOfValidWords.Code.Funs

/-!
# Specifications of `Aegis.FindNumOfValidWords.find_num_of_valid_words`

LeetCode problem `number-of-valid-words-for-each-puzzle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindNumOfValidWords

  open scoped Classical

  open Aegis.FindNumOfValidWords

  abbrev Bytes := List Std.U8

  def IsLowercase (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def wordAt (words : Slice (alloc.vec.Vec Std.U8)) (j : ℕ) : Bytes :=
    ((words.val[j]?).map (fun v => v.val)).getD []

  def puzzleAt (puzzles : Slice (alloc.vec.Vec Std.U8)) (i : ℕ) : Bytes :=
    ((puzzles.val[i]?).map (fun v => v.val)).getD []

  def letters (v : Bytes) : Finset ℕ := (v.map (fun b => b.val)).toFinset

  def containsFirst (w p : Bytes) : Prop := ∃ k : ℕ, k < w.length ∧ w[k]? = p[0]?

  def bytesIn (w p : Bytes) : Prop := ∀ c : Std.U8, c ∈ w → c ∈ p

  def validPair (w p : Bytes) : Prop := containsFirst w p ∧ bytesIn w p

  noncomputable def countWords (words : Slice (alloc.vec.Vec Std.U8))
      (P : Bytes → Prop) : ℕ :=
    {j : ℕ | j < words.val.length ∧ P (wordAt words j)}.ncard

  noncomputable def numValid (words : Slice (alloc.vec.Vec Std.U8)) (p : Bytes) : ℕ :=
    countWords words (fun w => validPair w p)

  noncomputable def countWithLetters (words : Slice (alloc.vec.Vec Std.U8))
      (S : Finset ℕ) : ℕ :=
    countWords words (fun w => letters w = S)

  noncomputable def firstSubsets (p : Bytes) : Finset (Finset ℕ) :=
    match p[0]? with
    | some b => (letters p).powerset.filter (fun S => b.val ∈ S)
    | none => ∅

  def allLowercase (words puzzles : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    (∀ j : ℕ, j < words.val.length → ∀ b : Std.U8, b ∈ wordAt words j → IsLowercase b) ∧
      (∀ i : ℕ, i < puzzles.val.length → ∀ b : Std.U8, b ∈ puzzleAt puzzles i → IsLowercase b)

  def allNonEmpty (puzzles : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∀ i : ℕ, i < puzzles.val.length → puzzleAt puzzles i ≠ []

  def answerAt (r : List Std.I64) (i : ℕ) : ℤ := ((r[i]?).map (fun v => v.val)).getD 0

  /-- The function returns a result r (it does not fail). The length of r is exactly len(puzzles): len(r) = len(puzzles). For every i with 0 <= i < len(puzzles), r[i] equals the number of indices j with 0 <= j < len(words) such that the word words[j] is valid for the puzzle puzzles[i], where a word w is valid for a puzzle p if and only if (1) w contains p[0] (there exists k with 0 <= k < len(w) and w[k] = p[0]) and (2) every byte of w occurs in p (for every k with 0 <= k < len(w), there exists l with 0 <= l < len(p) and w[k] = p[l]).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_1 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          r.val.length = puzzles.val.length ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                ri.val = (numValid words (puzzleAt puzzles i) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            r.val.length = puzzles.val.length ∧
              ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
                r.val[i]? = some ri →
                  ri.val = (numValid words (puzzleAt puzzles i) : ℤ)) := by
    sorry

  /-- The function returns a result r whose length is exactly len(puzzles): len(r) = len(puzzles). There are no extra entries, and no puzzles are omitted.
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_2 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          r.val.length = puzzles.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            r.val.length = puzzles.val.length) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), 0 <= r[i] <= len(words).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_3 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              0 ≤ ri.val ∧ ri.val ≤ (words.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                0 ≤ ri.val ∧ ri.val ≤ (words.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), r[i] = 0 if and only if there is no index j with 0 <= j < len(words) for which the word words[j] is valid for the puzzle puzzles[i] (validity: words[j] contains puzzles[i][0] and every byte of words[j] occurs in puzzles[i]).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_4 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              (ri.val = 0 ↔
                ∀ j : ℕ, j < words.val.length →
                  ¬ validPair (wordAt words j) (puzzleAt puzzles i)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                (ri.val = 0 ↔
                  ∀ j : ℕ, j < words.val.length →
                    ¬ validPair (wordAt words j) (puzzleAt puzzles i))) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), r[i] = len(words) if and only if every word words[j] (0 <= j < len(words)) is valid for puzzles[i] (i.e., words[j] contains puzzles[i][0] and every byte of words[j] occurs in puzzles[i]).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_5 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              (ri.val = (words.val.length : ℤ) ↔
                ∀ j : ℕ, j < words.val.length →
                  validPair (wordAt words j) (puzzleAt puzzles i)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                (ri.val = (words.val.length : ℤ) ↔
                  ∀ j : ℕ, j < words.val.length →
                    validPair (wordAt words j) (puzzleAt puzzles i))) := by
    sorry

  /-- The function returns a result r such that the sum of r[i] over all i with 0 <= i < len(puzzles) equals the number of pairs (i, j) with 0 <= i < len(puzzles) and 0 <= j < len(words) such that words[j] is valid for puzzles[i] (contains puzzles[i][0] and all its bytes occur in puzzles[i]).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_6 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          (∑ i ∈ Finset.range (puzzles.val.length), answerAt r.val i) =
            (({p : ℕ × ℕ | p.1 < puzzles.val.length ∧ p.2 < words.val.length ∧
                validPair (wordAt words p.2) (puzzleAt puzzles p.1)} : Set (ℕ × ℕ)).ncard : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            (∑ i ∈ Finset.range (puzzles.val.length), answerAt r.val i) =
              (({p : ℕ × ℕ | p.1 < puzzles.val.length ∧ p.2 < words.val.length ∧
                  validPair (wordAt words p.2) (puzzleAt puzzles p.1)} : Set (ℕ × ℕ)).ncard : ℤ)) := by
    sorry

  /-- The function returns a result r such that for any two indices i and k with 0 <= i < len(puzzles) and 0 <= k < len(puzzles), if puzzles[i][0] = puzzles[k][0] and for every byte c it holds that c occurs in puzzles[i] if and only if c occurs in puzzles[k], then r[i] = r[k].
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_7 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i k : ℕ), i < puzzles.val.length → k < puzzles.val.length →
            (puzzleAt puzzles i)[0]? = (puzzleAt puzzles k)[0]? →
              (∀ c : Std.U8, c ∈ puzzleAt puzzles i ↔ c ∈ puzzleAt puzzles k) →
                r.val[i]? = r.val[k]? := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i k : ℕ), i < puzzles.val.length → k < puzzles.val.length →
              (puzzleAt puzzles i)[0]? = (puzzleAt puzzles k)[0]? →
                (∀ c : Std.U8, c ∈ puzzleAt puzzles i ↔ c ∈ puzzleAt puzzles k) →
                  r.val[i]? = r.val[k]?) := by
    sorry

  /-- The function returns a result r such that for any two indices i and k with 0 <= i < len(puzzles) and 0 <= k < len(puzzles), if puzzles[i][0] = puzzles[k][0] and every byte occurring in puzzles[i] also occurs in puzzles[k], then r[i] <= r[k].
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_8 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i k : ℕ), i < puzzles.val.length → k < puzzles.val.length →
            (puzzleAt puzzles i)[0]? = (puzzleAt puzzles k)[0]? →
              (∀ c : Std.U8, c ∈ puzzleAt puzzles i → c ∈ puzzleAt puzzles k) →
                ∀ ri rk : Std.I64, r.val[i]? = some ri → r.val[k]? = some rk →
                  ri.val ≤ rk.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i k : ℕ), i < puzzles.val.length → k < puzzles.val.length →
              (puzzleAt puzzles i)[0]? = (puzzleAt puzzles k)[0]? →
                (∀ c : Std.U8, c ∈ puzzleAt puzzles i → c ∈ puzzleAt puzzles k) →
                  ∀ ri rk : Std.I64, r.val[i]? = some ri → r.val[k]? = some rk →
                    ri.val ≤ rk.val) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), r[i] equals the number of non-empty words w in words (i.e., len(w) >= 1) that are valid for puzzles[i] (contain puzzles[i][0] and have all bytes in puzzles[i]). In particular, any empty word in words contributes 0 to every r[i].
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_9 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              ri.val = (countWords words (fun w => w ≠ [] ∧ validPair w (puzzleAt puzzles i)) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                ri.val = (countWords words (fun w => w ≠ [] ∧ validPair w (puzzleAt puzzles i)) : ℤ)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), if len(puzzles[i]) = 1, then r[i] equals the number of words w in words with len(w) >= 1 such that every byte of w equals puzzles[i][0].
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_10 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → (puzzleAt puzzles i).length = 1 → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              ri.val =
                (countWords words
                  (fun w => w ≠ [] ∧ ∀ k : ℕ, k < w.length → w[k]? = (puzzleAt puzzles i)[0]?) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → (puzzleAt puzzles i).length = 1 → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                ri.val =
                  (countWords words
                    (fun w => w ≠ [] ∧ ∀ k : ℕ, k < w.length → w[k]? = (puzzleAt puzzles i)[0]?) : ℤ)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), if every lowercase letter 'a' through 'z' occurs in puzzles[i], then r[i] equals the number of words w in words that contain puzzles[i][0] (i.e., there exists k with 0 <= k < len(w) and w[k] = puzzles[i][0]).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_11 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length →
            (∀ c : Std.U8, IsLowercase c → c ∈ puzzleAt puzzles i) → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                ri.val =
                  (countWords words (fun w => containsFirst w (puzzleAt puzzles i)) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length →
              (∀ c : Std.U8, IsLowercase c → c ∈ puzzleAt puzzles i) → ∀ ri : Std.I64,
                r.val[i]? = some ri →
                  ri.val =
                    (countWords words (fun w => containsFirst w (puzzleAt puzzles i)) : ℤ)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), r[i] is at most the number of indices j with 0 <= j < len(words) such that words[j] contains puzzles[i][0] (there exists k with 0 <= k < len(words[j]) and words[j][k] = puzzles[i][0]).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_12 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              ri.val ≤ (countWords words (fun w => containsFirst w (puzzleAt puzzles i)) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                ri.val ≤ (countWords words (fun w => containsFirst w (puzzleAt puzzles i)) : ℤ)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < len(puzzles), r[i] is at most the number of indices j with 0 <= j < len(words) such that every byte of words[j] occurs in puzzles[i] (for every k with 0 <= k < len(words[j]), there exists l with 0 <= l < len(puzzles[i]) and words[j][k] = puzzles[i][l]).
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_13 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              ri.val ≤ (countWords words (fun w => bytesIn w (puzzleAt puzzles i)) : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                ri.val ≤ (countWords words (fun w => bytesIn w (puzzleAt puzzles i)) : ℤ)) := by
    sorry

  /-- The function returns a result r1 for (words1, puzzles) and r2 for (words2, puzzles), and neither call fails. If len(words1) = len(words2) and for every j with 0 <= j < len(words1) the set of bytes occurring in words1[j] equals the set of bytes occurring in words2[j] (for every byte c, c occurs in words1[j] if and only if c occurs in words2[j]), then for every i with 0 <= i < len(puzzles), r1[i] = r2[i]. Equivalently, for each puzzle the count depends on each word only through its set of occurring bytes, not the order or multiplicity of those bytes.
    Preconditions: words1, words2, and puzzles are slices of byte vectors. 0 <= len(words1) = len(words2) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_14 (words1 words2 puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords1 : words1.val.length ≤ 100000)
      (hwords2 : words2.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower1 : allLowercase words1 puzzles)
      (hlower2 : allLowercase words2 puzzles)
      (hne : allNonEmpty puzzles)
      (hlen : words1.val.length = words2.val.length)
      (hsets : ∀ j : ℕ, j < words1.val.length →
        ∀ c : Std.U8, c ∈ wordAt words1 j ↔ c ∈ wordAt words2 j) :
      ∃ r1 r2 : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words1 puzzles = ok r1 ∧
          find_num_of_valid_words words2 puzzles = ok r2 ∧
            ∀ i : ℕ, i < puzzles.val.length → r1.val[i]? = r2.val[i]? := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (words1 words2 puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords1 : words1.val.length ≤ 100000)
        (hwords2 : words2.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower1 : allLowercase words1 puzzles)
        (hlower2 : allLowercase words2 puzzles)
        (hne : allNonEmpty puzzles)
        (hlen : words1.val.length = words2.val.length)
        (hsets : ∀ j : ℕ, j < words1.val.length →
          ∀ c : Std.U8, c ∈ wordAt words1 j ↔ c ∈ wordAt words2 j), ∃ r1 r2 : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words1 puzzles = ok r1 ∧
            find_num_of_valid_words words2 puzzles = ok r2 ∧
              ∀ i : ℕ, i < puzzles.val.length → r1.val[i]? = r2.val[i]?) := by
    sorry

  /-- The function returns a result r such that for any permutation sigma of the index set {0, ..., len(words)-1}, if words' is the slice with words'[j] = words[sigma(j)] and r' is the result for (words', puzzles), then for every i with 0 <= i < len(puzzles), r'[i] = r[i].
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_15 (words words' puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hwords' : words'.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hlower' : allLowercase words' puzzles)
      (hne : allNonEmpty puzzles)
      (hlen : words'.val.length = words.val.length)
      (σ : Equiv.Perm (Fin words.val.length))
      (hperm : ∀ j : Fin words.val.length,
        words'.val[(j : ℕ)]? = words.val[((σ j : Fin words.val.length) : ℕ)]?) :
      ∃ r r' : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          find_num_of_valid_words words' puzzles = ok r' ∧
            ∀ i : ℕ, i < puzzles.val.length → r'.val[i]? = r.val[i]? := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (words words' puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hwords' : words'.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hlower' : allLowercase words' puzzles)
        (hne : allNonEmpty puzzles)
        (hlen : words'.val.length = words.val.length)
        (σ : Equiv.Perm (Fin words.val.length))
        (hperm : ∀ j : Fin words.val.length,
          words'.val[(j : ℕ)]? = words.val[((σ j : Fin words.val.length) : ℕ)]?), ∃ r r' : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            find_num_of_valid_words words' puzzles = ok r' ∧
              ∀ i : ℕ, i < puzzles.val.length → r'.val[i]? = r.val[i]?) := by
    sorry

  /-- If r is the result for (words, puzzles) and r' is the result for (words', puzzles), then for every i with 0 <= i < len(puzzles), r'[i] = r[i] + 1 if w is valid for puzzles[i] (w contains puzzles[i][0] and every byte of w occurs in puzzles[i]), and r'[i] = r[i] otherwise.
    Preconditions: words, words', and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5, len(words') = len(words) + 1, and 0 <= len(puzzles) <= 10^4. There is a byte vector w such that words'[j] = words[j] for every 0 <= j < len(words) and words'[len(words)] = w. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_16 (words words' puzzles : Slice (alloc.vec.Vec Std.U8))
      (w : alloc.vec.Vec Std.U8)
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hlower' : allLowercase words' puzzles)
      (hne : allNonEmpty puzzles)
      (hlen : words'.val.length = words.val.length + 1)
      (hprefix : ∀ j : ℕ, j < words.val.length → words'.val[j]? = words.val[j]?)
      (hlast : words'.val[words.val.length]? = some w) :
      ∃ r r' : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          find_num_of_valid_words words' puzzles = ok r' ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri ri' : Std.I64,
              r.val[i]? = some ri → r'.val[i]? = some ri' →
                ((validPair w.val (puzzleAt puzzles i) → ri'.val = ri.val + 1) ∧
                  (¬ validPair w.val (puzzleAt puzzles i) → ri'.val = ri.val)) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (words words' puzzles : Slice (alloc.vec.Vec Std.U8))
        (w : alloc.vec.Vec Std.U8)
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hlower' : allLowercase words' puzzles)
        (hne : allNonEmpty puzzles)
        (hlen : words'.val.length = words.val.length + 1)
        (hprefix : ∀ j : ℕ, j < words.val.length → words'.val[j]? = words.val[j]?)
        (hlast : words'.val[words.val.length]? = some w), ∃ r r' : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            find_num_of_valid_words words' puzzles = ok r' ∧
              ∀ (i : ℕ), i < puzzles.val.length → ∀ ri ri' : Std.I64,
                r.val[i]? = some ri → r'.val[i]? = some ri' →
                  ((validPair w.val (puzzleAt puzzles i) → ri'.val = ri.val + 1) ∧
                    (¬ validPair w.val (puzzleAt puzzles i) → ri'.val = ri.val))) := by
    sorry

  /-- For every i with 0 <= i < len(puzzles), r[i] equals the sum over all sets S of bytes such that puzzles[i][0] is in S and S is a subset of letters(puzzles[i]) of the number of indices j with 0 <= j < len(words) and letters(words[j]) = S, where letters(v) is the set of bytes occurring in v.
    Preconditions: words and puzzles are slices of byte vectors. 0 <= len(words) <= 10^5 and 0 <= len(puzzles) <= 10^4. Every byte occurring in any word or puzzle is a lowercase ASCII letter ('a' through 'z'). Every puzzle is non-empty: for every i with 0 <= i < len(puzzles), len(puzzles[i]) >= 1. -/
  theorem spec_17 (words puzzles : Slice (alloc.vec.Vec Std.U8))
      (hwords : words.val.length ≤ 100000)
      (hpuzzles : puzzles.val.length ≤ 10000)
      (hlower : allLowercase words puzzles)
      (hne : allNonEmpty puzzles) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_num_of_valid_words words puzzles = ok r ∧
          ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
            r.val[i]? = some ri →
              ri.val =
                (∑ S ∈ firstSubsets (puzzleAt puzzles i), (countWithLetters words S : ℤ)) := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (words puzzles : Slice (alloc.vec.Vec Std.U8))
        (hwords : words.val.length ≤ 100000)
        (hpuzzles : puzzles.val.length ≤ 10000)
        (hlower : allLowercase words puzzles)
        (hne : allNonEmpty puzzles), ∃ r : alloc.vec.Vec Std.I64,
          find_num_of_valid_words words puzzles = ok r ∧
            ∀ (i : ℕ), i < puzzles.val.length → ∀ ri : Std.I64,
              r.val[i]? = some ri →
                ri.val =
                  (∑ S ∈ firstSubsets (puzzleAt puzzles i), (countWithLetters words S : ℤ))) := by
    sorry

  end AegisSpec.FindNumOfValidWords
