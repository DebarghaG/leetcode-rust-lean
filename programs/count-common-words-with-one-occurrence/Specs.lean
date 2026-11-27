import Aegis.CountWords.Code.Funs

/-!
# Specifications of `Aegis.CountWords.count_words`

LeetCode problem `count-common-words-with-one-occurrence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountWords

  def isAsciiLower (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def IsWord (v : alloc.vec.Vec U8) : Prop :=
    1 ≤ v.val.length ∧ v.val.length ≤ 30 ∧ ∀ b, b ∈ v.val → isAsciiLower b

  def WordsConstraints (xs : Slice (alloc.vec.Vec U8)) : Prop :=
    1 ≤ xs.val.length ∧ xs.val.length ≤ 1000 ∧
      ∀ (i : ℕ) (hi : i < xs.val.length), IsWord (xs.val.get ⟨i, hi⟩)

  def ProblemConstraints (words1 words2 : Slice (alloc.vec.Vec U8)) : Prop :=
    WordsConstraints words1 ∧ WordsConstraints words2

  def occ (xs : Slice (alloc.vec.Vec U8)) (w : List U8) : ℕ :=
    (xs.val.filter (fun v => v.val = w)).length

  def OccursSet (xs : Slice (alloc.vec.Vec U8)) : Finset (List U8) :=
    (xs.val.map (fun v => v.val)).toFinset

  def OnceSet (xs : Slice (alloc.vec.Vec U8)) : Finset (List U8) :=
    Finset.filter (fun w => occ xs w = 1) (OccursSet xs)

  def BothOnceSet (words1 words2 : Slice (alloc.vec.Vec U8)) : Finset (List U8) :=
    OnceSet words1 ∩ OnceSet words2

  def BothOccursSet (words1 words2 : Slice (alloc.vec.Vec U8)) : Finset (List U8) :=
    OccursSet words1 ∩ OccursSet words2

  /-- Define occ(xs,w) as the number of indices i with 0 <= i < len(xs) and xs[i] = w, where w ranges over byte sequences. Let S = {w | occ(words1,w) = 1 and occ(words2,w) = 1}. Whenever count_words(words1,words2) returns a result r, r equals the number of elements of S, i.e. the number of distinct strings that occur exactly once in words1 and exactly once in words2.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_1 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (r : I64)
      (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      r.val = ((BothOnceSet words1 words2).card : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (r : I64)
        (hr : Aegis.CountWords.count_words words1 words2 = ok r), r.val = ((BothOnceSet words1 words2).card : ℤ)) := by
    sorry

  /-- count_words(words1, words2) returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_2 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) :
      ∃ r : I64, Aegis.CountWords.count_words words1 words2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2), ∃ r : I64, Aegis.CountWords.count_words words1 words2 = ok r) := by
    sorry

  /-- Whenever count_words(words1, words2) returns a result r, r <= len(words1) and r <= len(words2); equivalently r <= min(len(words1), len(words2)).
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_3 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (r : I64)
      (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      r.val ≤ (words1.val.length : ℤ) ∧ r.val ≤ (words2.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (r : I64)
        (hr : Aegis.CountWords.count_words words1 words2 = ok r), r.val ≤ (words1.val.length : ℤ) ∧ r.val ≤ (words2.val.length : ℤ)) := by
    sorry

  /-- Define occ(xs,w) as the number of indices i with 0 <= i < len(xs) and xs[i] = w. Whenever count_words(words1, words2) returns a result r, r <= |{w | occ(words1,w) = 1}| and r <= |{w | occ(words2,w) = 1}|.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_4 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (r : I64)
      (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      r.val ≤ ((OnceSet words1).card : ℤ) ∧ r.val ≤ ((OnceSet words2).card : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (r : I64)
        (hr : Aegis.CountWords.count_words words1 words2 = ok r), r.val ≤ ((OnceSet words1).card : ℤ) ∧ r.val ≤ ((OnceSet words2).card : ℤ)) := by
    sorry

  /-- Whenever count_words(words1, words2) returns a result r1 and count_words(words2, words1) returns a result r2, r1 = r2.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_5 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (r1 r2 : I64)
      (hr1 : Aegis.CountWords.count_words words1 words2 = ok r1)
      (hr2 : Aegis.CountWords.count_words words2 words1 = ok r2) :
      r1.val = r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (r1 r2 : I64)
        (hr1 : Aegis.CountWords.count_words words1 words2 = ok r1)
        (hr2 : Aegis.CountWords.count_words words2 words1 = ok r2), r1.val = r2.val) := by
    sorry

  /-- If for every i with 0 <= i < len(words1) and every j with 0 <= j < len(words2), words1[i] != words2[j] (no string occurs in both arrays), then whenever count_words(words1, words2) returns a result r, r = 0.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_6 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2)
      (hdisj : ∀ (i : ℕ) (hi : i < words1.val.length) (j : ℕ) (hj : j < words2.val.length),
        (words1.val.get ⟨i, hi⟩).val ≠ (words2.val.get ⟨j, hj⟩).val)
      (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2)
        (hdisj : ∀ (i : ℕ) (hi : i < words1.val.length) (j : ℕ) (hj : j < words2.val.length),
          (words1.val.get ⟨i, hi⟩).val ≠ (words2.val.get ⟨j, hj⟩).val)
        (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r), r.val = 0) := by
    sorry

  /-- If there is a byte sequence s such that every word in words1 equals s and every word in words2 equals s, then whenever count_words(words1, words2) returns a result r: r = 1 if len(words1) = 1 and len(words2) = 1, and r = 0 otherwise.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_7 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (s : List U8)
      (h1 : ∀ (i : ℕ) (hi : i < words1.val.length), (words1.val.get ⟨i, hi⟩).val = s)
      (h2 : ∀ (j : ℕ) (hj : j < words2.val.length), (words2.val.get ⟨j, hj⟩).val = s)
      (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      (words1.val.length = 1 ∧ words2.val.length = 1 → r.val = 1) ∧
        (¬ (words1.val.length = 1 ∧ words2.val.length = 1) → r.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (s : List U8)
        (h1 : ∀ (i : ℕ) (hi : i < words1.val.length), (words1.val.get ⟨i, hi⟩).val = s)
        (h2 : ∀ (j : ℕ) (hj : j < words2.val.length), (words2.val.get ⟨j, hj⟩).val = s)
        (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r), (words1.val.length = 1 ∧ words2.val.length = 1 → r.val = 1) ∧
          (¬ (words1.val.length = 1 ∧ words2.val.length = 1) → r.val = 0)) := by
    sorry

  /-- Assume that every string occurring in words1 occurs exactly once in words1 and every string occurring in words2 occurs exactly once in words2; equivalently, for every byte sequence w, occ(words1,w) <= 1 and occ(words2,w) <= 1, where occ(xs,w) is the number of indices i with 0 <= i < len(xs) and xs[i] = w. Then whenever count_words(words1, words2) returns a result r, r equals the number of distinct byte sequences that occur in both words1 and words2 (the size of the intersection of the two sets of strings).
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_8 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2)
      (hu1 : ∀ w : List U8, occ words1 w ≤ 1)
      (hu2 : ∀ w : List U8, occ words2 w ≤ 1)
      (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      r.val = ((BothOccursSet words1 words2).card : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2)
        (hu1 : ∀ w : List U8, occ words1 w ≤ 1)
        (hu2 : ∀ w : List U8, occ words2 w ≤ 1)
        (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r), r.val = ((BothOccursSet words1 words2).card : ℤ)) := by
    sorry

  /-- If len(words1) = 1, let a = words1[0]. Then whenever count_words(words1, words2) returns a result r: r = 1 if occ(words2,a) = 1, and r = 0 otherwise, where occ(words2,a) is the number of indices j with 0 <= j < len(words2) and words2[j] = a.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_9 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (h1 : words1.val.length = 1) (r : I64)
      (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      (occ words2 ((words1.val.get ⟨0, by omega⟩).val) = 1 → r.val = 1) ∧
        (occ words2 ((words1.val.get ⟨0, by omega⟩).val) ≠ 1 → r.val = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (h1 : words1.val.length = 1) (r : I64)
        (hr : Aegis.CountWords.count_words words1 words2 = ok r), (occ words2 ((words1.val.get ⟨0, by omega⟩).val) = 1 → r.val = 1) ∧
          (occ words2 ((words1.val.get ⟨0, by omega⟩).val) ≠ 1 → r.val = 0)) := by
    sorry

  /-- Whenever count_words(words1, words2) returns a result r and r > 0, there exists an index i with 0 <= i < len(words1) such that words1[i] occurs exactly once in words1 and exactly once in words2; that is, occ(words1, words1[i]) = 1 and occ(words2, words1[i]) = 1, where occ(xs,w) is the number of indices k with 0 <= k < len(xs) and xs[k] = w.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_10 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (r : I64)
      (hr : Aegis.CountWords.count_words words1 words2 = ok r) (hpos : 0 < r.val) :
      ∃ (i : ℕ) (hi : i < words1.val.length),
        occ words1 (words1.val.get ⟨i, hi⟩).val = 1 ∧
          occ words2 (words1.val.get ⟨i, hi⟩).val = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (r : I64)
        (hr : Aegis.CountWords.count_words words1 words2 = ok r) (hpos : 0 < r.val), ∃ (i : ℕ) (hi : i < words1.val.length),
          occ words1 (words1.val.get ⟨i, hi⟩).val = 1 ∧
            occ words2 (words1.val.get ⟨i, hi⟩).val = 1) := by
    sorry

  /-- For any word lists words1' and words2' satisfying the same problem constraints, if for every byte sequence w, (occ(words1',w) = 1 iff occ(words1,w) = 1) and (occ(words2',w) = 1 iff occ(words2,w) = 1), where occ(xs,w) is the number of indices i with 0 <= i < len(xs) and xs[i] = w, then whenever count_words(words1, words2) returns r and count_words(words1', words2') returns r', r = r'.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_11 (words1 words2 words1' words2' : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2) (h' : ProblemConstraints words1' words2')
      (hinv1 : ∀ w : List U8, occ words1' w = 1 ↔ occ words1 w = 1)
      (hinv2 : ∀ w : List U8, occ words2' w = 1 ↔ occ words2 w = 1)
      (r r' : I64)
      (hr : Aegis.CountWords.count_words words1 words2 = ok r)
      (hr' : Aegis.CountWords.count_words words1' words2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words1 words2 words1' words2' : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2) (h' : ProblemConstraints words1' words2')
        (hinv1 : ∀ w : List U8, occ words1' w = 1 ↔ occ words1 w = 1)
        (hinv2 : ∀ w : List U8, occ words2' w = 1 ↔ occ words2 w = 1)
        (r r' : I64)
        (hr : Aegis.CountWords.count_words words1 words2 = ok r)
        (hr' : Aegis.CountWords.count_words words1' words2' = ok r'), r.val = r'.val) := by
    sorry

  /-- If no byte sequence occurs exactly once in words1, i.e. for every byte sequence w, occ(words1,w) != 1, where occ(words1,w) is the number of indices i with 0 <= i < len(words1) and words1[i] = w, then whenever count_words(words1, words2) returns a result r, r = 0.
    Preconditions: Problem constraints hold: 1 <= len(words1) <= 1000 and 1 <= len(words2) <= 1000; for every i with 0 <= i < len(words1), 1 <= len(words1[i]) <= 30 and all bytes of words1[i] are ASCII lowercase letters; for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 30 and all bytes of words2[j] are ASCII lowercase letters. Words are byte sequences, compared by length and bytewise equality. -/
  theorem spec_12 (words1 words2 : Slice (alloc.vec.Vec U8))
      (h : ProblemConstraints words1 words2)
      (hne : ∀ w : List U8, occ words1 w ≠ 1)
      (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words1 words2 : Slice (alloc.vec.Vec U8))
        (h : ProblemConstraints words1 words2)
        (hne : ∀ w : List U8, occ words1 w ≠ 1)
        (r : I64) (hr : Aegis.CountWords.count_words words1 words2 = ok r), r.val = 0) := by
    sorry

  end AegisSpec.CountWords
