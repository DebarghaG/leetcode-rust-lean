import Aegis.MostWordsFound.Code.Funs

/-!
# Specifications of `Aegis.MostWordsFound.most_words_found`

LeetCode problem `maximum-number-of-words-found-in-sentences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MostWordsFound

  abbrev Sentence := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

  abbrev Sentences := Aeneas.Std.Slice Sentence

  def byteValid (b : Aeneas.Std.U8) : Prop :=
    b.val = 32 ∨ (97 ≤ b.val ∧ b.val ≤ 122)

  def NoAdjacentSpaces : List Aeneas.Std.U8 → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => ¬ (a.val = 32 ∧ b.val = 32) ∧ NoAdjacentSpaces (b :: rest)

  def SentenceValid (s : Sentence) : Prop :=
    1 ≤ s.val.length ∧
    s.val.length ≤ 100 ∧
    (∀ b ∈ s.val, byteValid b) ∧
    (∀ (h : 0 < s.val.length), (s.val.get ⟨0, h⟩).val ≠ 32) ∧
    (∀ (h : 0 < s.val.length), (s.val.get ⟨s.val.length - 1, by omega⟩).val ≠ 32) ∧
    NoAdjacentSpaces s.val

  def Valid (sentences : Sentences) : Prop :=
    1 ≤ sentences.val.length ∧
    sentences.val.length ≤ 100 ∧
    (∀ (i : ℕ) (h : i < sentences.val.length), SentenceValid (sentences.val.get ⟨i, h⟩))

  def words (s : List Aeneas.Std.U8) : ℕ :=
    1 + (s.filter (fun b => decide (b.val = 32))).length

  def sentenceWords (s : Sentence) : ℕ := words s.val

  def maxWords (ss : List Sentence) : ℕ :=
    Finset.univ.sup (fun i : Fin ss.length => sentenceWords (ss.get i))

  def maxLen (ss : List Sentence) : ℕ :=
    Finset.univ.sup (fun i : Fin ss.length => (ss.get i).val.length)

  /-- The function returns a result r and r = max({ words(sentences[i]) | 0 <= i < len(sentences) }), where for a byte array s, words(s) = 1 + |{ j | 0 <= j < len(s) and s[j] = 32 }|.
    Preconditions: 1 <= len(sentences) <= 100; for every i with 0 <= i < len(sentences), 1 <= len(sentences[i]) <= 100, every byte sentences[i][j] with 0 <= j < len(sentences[i]) is either 32 or a lowercase English letter byte (97 <= sentences[i][j] <= 122), sentences[i][0] != 32, sentences[i][len(sentences[i])-1] != 32, and there are no adjacent spaces (for every j with 0 <= j+1 < len(sentences[i]), not (sentences[i][j] = 32 and sentences[i][j+1] = 32)). -/
  theorem spec_1 (sentences : Sentences) (hpre : Valid sentences) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MostWordsFound.most_words_found sentences = ok r ∧
          r.val = (maxWords sentences.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (sentences : Sentences) (hpre : Valid sentences), ∃ r : Aeneas.Std.I64,
          Aegis.MostWordsFound.most_words_found sentences = ok r ∧
            r.val = (maxWords sentences.val : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: 1 <= len(sentences) <= 100; for every i with 0 <= i < len(sentences), 1 <= len(sentences[i]) <= 100, every byte sentences[i][j] with 0 <= j < len(sentences[i]) is either 32 or a lowercase English letter byte (97 <= sentences[i][j] <= 122), sentences[i][0] != 32, sentences[i][len(sentences[i])-1] != 32, and there are no adjacent spaces (for every j with 0 <= j+1 < len(sentences[i]), not (sentences[i][j] = 32 and sentences[i][j+1] = 32)). -/
  theorem spec_2 (sentences : Sentences) (hpre : Valid sentences) :
      ∃ r : Aeneas.Std.I64, Aegis.MostWordsFound.most_words_found sentences = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (sentences : Sentences) (hpre : Valid sentences), ∃ r : Aeneas.Std.I64, Aegis.MostWordsFound.most_words_found sentences = ok r) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: 1 <= len(sentences) <= 100; for every i with 0 <= i < len(sentences), 1 <= len(sentences[i]) <= 100, every byte sentences[i][j] with 0 <= j < len(sentences[i]) is either 32 or a lowercase English letter byte (97 <= sentences[i][j] <= 122), sentences[i][0] != 32, sentences[i][len(sentences[i])-1] != 32, and there are no adjacent spaces (for every j with 0 <= j+1 < len(sentences[i]), not (sentences[i][j] = 32 and sentences[i][j+1] = 32)). -/
  theorem spec_3 (sentences : Sentences) (hpre : Valid sentences) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MostWordsFound.most_words_found sentences = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (sentences : Sentences) (hpre : Valid sentences), ∃ r : Aeneas.Std.I64,
          Aegis.MostWordsFound.most_words_found sentences = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= 50.
    Preconditions: 1 <= len(sentences) <= 100; for every i with 0 <= i < len(sentences), 1 <= len(sentences[i]) <= 100, every byte sentences[i][j] with 0 <= j < len(sentences[i]) is either 32 or a lowercase English letter byte (97 <= sentences[i][j] <= 122), sentences[i][0] != 32, sentences[i][len(sentences[i])-1] != 32, and there are no adjacent spaces (for every j with 0 <= j+1 < len(sentences[i]), not (sentences[i][j] = 32 and sentences[i][j+1] = 32)). -/
  theorem spec_4 (sentences : Sentences) (hpre : Valid sentences) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MostWordsFound.most_words_found sentences = ok r ∧ r.val ≤ 50 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (sentences : Sentences) (hpre : Valid sentences), ∃ r : Aeneas.Std.I64,
          Aegis.MostWordsFound.most_words_found sentences = ok r ∧ r.val ≤ 50) := by
    sorry

  /-- The function returns a result r and there exists an index i with 0 <= i < len(sentences) such that words(sentences[i]) = r, where for a byte array s, words(s) = 1 + |{ j | 0 <= j < len(s) and s[j] = 32 }|.
    Preconditions: 1 <= len(sentences) <= 100; for every i with 0 <= i < len(sentences), 1 <= len(sentences[i]) <= 100, every byte sentences[i][j] with 0 <= j < len(sentences[i]) is either 32 or a lowercase English letter byte (97 <= sentences[i][j] <= 122), sentences[i][0] != 32, sentences[i][len(sentences[i])-1] != 32, and there are no adjacent spaces (for every j with 0 <= j+1 < len(sentences[i]), not (sentences[i][j] = 32 and sentences[i][j+1] = 32)). -/
  theorem spec_5 (sentences : Sentences) (hpre : Valid sentences) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MostWordsFound.most_words_found sentences = ok r ∧
          ∃ i : ℕ, ∃ h : i < sentences.val.length,
            (sentenceWords (sentences.val.get ⟨i, h⟩) : ℤ) = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (sentences : Sentences) (hpre : Valid sentences), ∃ r : Aeneas.Std.I64,
          Aegis.MostWordsFound.most_words_found sentences = ok r ∧
            ∃ i : ℕ, ∃ h : i < sentences.val.length,
              (sentenceWords (sentences.val.get ⟨i, h⟩) : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and for every i with 0 <= i < len(sentences), words(sentences[i]) <= r, where for a byte array s, words(s) = 1 + |{ j | 0 <= j < len(s) and s[j] = 32 }|.
    Preconditions: 1 <= len(sentences) <= 100; for every i with 0 <= i < len(sentences), 1 <= len(sentences[i]) <= 100, every byte sentences[i][j] with 0 <= j < len(sentences[i]) is either 32 or a lowercase English letter byte (97 <= sentences[i][j] <= 122), sentences[i][0] != 32, sentences[i][len(sentences[i])-1] != 32, and there are no adjacent spaces (for every j with 0 <= j+1 < len(sentences[i]), not (sentences[i][j] = 32 and sentences[i][j+1] = 32)). -/
  theorem spec_6 (sentences : Sentences) (hpre : Valid sentences) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MostWordsFound.most_words_found sentences = ok r ∧
          ∀ i (h : i < sentences.val.length),
            (sentenceWords (sentences.val.get ⟨i, h⟩) : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (sentences : Sentences) (hpre : Valid sentences), ∃ r : Aeneas.Std.I64,
          Aegis.MostWordsFound.most_words_found sentences = ok r ∧
            ∀ i (h : i < sentences.val.length),
              (sentenceWords (sentences.val.get ⟨i, h⟩) : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= max({ len(sentences[i]) | 0 <= i < len(sentences) }).
    Preconditions: 1 <= len(sentences) <= 100; for every i with 0 <= i < len(sentences), 1 <= len(sentences[i]) <= 100, every byte sentences[i][j] with 0 <= j < len(sentences[i]) is either 32 or a lowercase English letter byte (97 <= sentences[i][j] <= 122), sentences[i][0] != 32, sentences[i][len(sentences[i])-1] != 32, and there are no adjacent spaces (for every j with 0 <= j+1 < len(sentences[i]), not (sentences[i][j] = 32 and sentences[i][j+1] = 32)). -/
  theorem spec_7 (sentences : Sentences) (hpre : Valid sentences) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MostWordsFound.most_words_found sentences = ok r ∧
          r.val ≤ (maxLen sentences.val : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (sentences : Sentences) (hpre : Valid sentences), ∃ r : Aeneas.Std.I64,
          Aegis.MostWordsFound.most_words_found sentences = ok r ∧
            r.val ≤ (maxLen sentences.val : ℤ)) := by
    sorry

  /-- Whenever the function returns r on sentences and r' on sentences', we have r = r'.
    Preconditions: sentences and an alternate slice sentences' both satisfy the problem constraints (1 <= len <= 100; each element nonempty with length <= 100; bytes are 32 or 97..122; no leading/trailing spaces; no adjacent spaces). Also len(sentences') = len(sentences) and there exists a permutation pi of {0,...,len(sentences)-1} such that sentences'[i] = sentences[pi(i)] for every i with 0 <= i < len(sentences). -/
  theorem spec_8 (sentences sentences' : Sentences)
      (hpre : Valid sentences) (hpre' : Valid sentences')
      (hlen : sentences'.val.length = sentences.val.length)
      (hperm : ∃ π : Equiv.Perm (Fin sentences.val.length),
        sentences'.val = List.ofFn (fun i => sentences.val.get (π i))) :
      ∀ r r' : Aeneas.Std.I64,
        Aegis.MostWordsFound.most_words_found sentences = ok r →
          Aegis.MostWordsFound.most_words_found sentences' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (sentences sentences' : Sentences)
        (hpre : Valid sentences) (hpre' : Valid sentences')
        (hlen : sentences'.val.length = sentences.val.length)
        (hperm : ∃ π : Equiv.Perm (Fin sentences.val.length),
          sentences'.val = List.ofFn (fun i => sentences.val.get (π i))), ∀ r r' : Aeneas.Std.I64,
          Aegis.MostWordsFound.most_words_found sentences = ok r →
            Aegis.MostWordsFound.most_words_found sentences' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.MostWordsFound
