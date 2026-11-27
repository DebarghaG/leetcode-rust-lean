import Aegis.WordBreak.Code.Funs

/-!
# Specifications of `Aegis.WordBreak.word_break`

LeetCode problem `word-break-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WordBreak

  abbrev ByteVec : Type := alloc.vec.Vec Std.U8

  abbrev SentenceVec : Type := alloc.vec.Vec ByteVec

  def space : Std.U8 := 32#u8

  abbrev IsSpace (b : Std.U8) : Prop := b.val = 32

  theorem space_val : (space : Std.U8).val = 32 := by decide

  def dictWord (wordDict : Slice ByteVec) (j : Nat) : List Std.U8 :=
    match wordDict.val[j]? with
    | some w => w.val
    | none => []

  def concatWords (wordDict : Slice ByteVec) (js : List Nat) : List Std.U8 :=
    (js.map (dictWord wordDict)).flatten

  def joinWords (wordDict : Slice ByteVec) (js : List Nat) : List Std.U8 :=
    List.intercalate [space] (js.map (dictWord wordDict))

  def Splits (s : Slice Std.U8) (wordDict : Slice ByteVec) (js : List Nat) : Prop :=
    js ≠ [] ∧ (∀ j ∈ js, j < wordDict.val.length) ∧ s.val = concatWords wordDict js

  def IsValidSentence (s : Slice Std.U8) (wordDict : Slice ByteVec) (t : List Std.U8) : Prop :=
    ∃ js : List Nat, Splits s wordDict js ∧ t = joinWords wordDict js

  def countOcc (t : List Std.U8) (r : SentenceVec) : Nat :=
    (r.val.filter (fun v => decide (v.val = t))).length

  def deleteSpaces (t : List Std.U8) : List Std.U8 :=
    t.filter (fun b => decide (¬ IsSpace b))

  def blocks (t : List Std.U8) : List (List Std.U8) :=
    (t.splitOn space).filter (fun b => decide (b ≠ []))

  def numBlocks (t : List Std.U8) : Nat :=
    (blocks t).length

  def AllLower (l : List Std.U8) : Prop :=
    ∀ b ∈ l, 97 ≤ b.val ∧ b.val ≤ 122

  structure WellFormed (s : Slice Std.U8) (wordDict : Slice ByteVec) : Prop where

    s_len_lower : 1 ≤ s.val.length

    s_len_upper : s.val.length ≤ 20

    dict_len_lower : 1 ≤ wordDict.val.length

    dict_len_upper : wordDict.val.length ≤ 1000

    word_len_bounds :
      ∀ j, j < wordDict.val.length →
        1 ≤ (dictWord wordDict j).length ∧ (dictWord wordDict j).length ≤ 10

    s_lower : AllLower s.val

    dict_lower : ∀ j, j < wordDict.val.length → AllLower (dictWord wordDict j)

    dict_nodup :
      ∀ j k, j < k → k < wordDict.val.length → dictWord wordDict j ≠ dictWord wordDict k

  def indexSeqs (n : Nat) : Nat → List (List Nat)
    | 0 => [[]]
    | k + 1 => (List.range n).flatMap (fun j => (indexSeqs n k).map (fun js => js ++ [j]))

  def numSplits (s : Slice Std.U8) (wordDict : Slice ByteVec) : Nat :=
    (((List.range (s.val.length + 1)).flatMap (fun k => indexSeqs wordDict.val.length k)).filter
      (fun js => decide (js ≠ [] ∧ s.val = concatWords wordDict js))).length

  open Classical in

  /-- The function returns a result r and, for every byte vector t, the number of indices i with 0 <= i < len(r) and r[i] = t is 1 if t is a valid sentence and is 0 otherwise. A byte vector t is a valid sentence exactly when there exist an integer k >= 1 and indices j_0,...,j_{k-1} with 0 <= j_l < len(wordDict) for every l, such that s equals the byte concatenation of wordDict[j_0], wordDict[j_1], ..., wordDict[j_{k-1}] in that order, and t equals the byte concatenation of wordDict[j_0], then one byte 32 (ASCII space), then wordDict[j_1], then one byte 32, ..., then one byte 32, then wordDict[j_{k-1}]. In particular, r contains every valid sentence exactly once, in any order, and contains no other vectors.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_1 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict) :
      ∃ r : SentenceVec,
        Aegis.WordBreak.word_break s wordDict = ok r ∧
          ∀ t : List Std.U8,
            countOcc t r = if IsValidSentence s wordDict t then 1 else 0 := by
    sorry

  open Classical in
  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict), ∃ r : SentenceVec,
          Aegis.WordBreak.word_break s wordDict = ok r ∧
            ∀ t : List Std.U8,
              countOcc t r = if IsValidSentence s wordDict t then 1 else 0) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail, panic, or overflow.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_2 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict) :
      ∃ r : SentenceVec, Aegis.WordBreak.word_break s wordDict = ok r := by
    sorry

  open Classical in
  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict), ∃ r : SentenceVec, Aegis.WordBreak.word_break s wordDict = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), the byte vector r[i] is a valid sentence. A byte vector t is a valid sentence exactly when there exist an integer k >= 1 and indices j_0,...,j_{k-1} with 0 <= j_l < len(wordDict) for every l, such that s equals the byte concatenation of wordDict[j_0], wordDict[j_1], ..., wordDict[j_{k-1}] in that order, and t equals the byte concatenation of wordDict[j_0], then one byte 32 (ASCII space), then wordDict[j_1], then one byte 32, ..., then one byte 32, then wordDict[j_{k-1}].
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_3 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ (i : Nat) (hi : i < r.val.length), IsValidSentence s wordDict (r.val[i]'hi).val := by
    sorry

  open Classical in
  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ (i : Nat) (hi : i < r.val.length), IsValidSentence s wordDict (r.val[i]'hi).val) := by
    sorry

  /-- Whenever the function returns a result r, for every valid sentence t, there exists an index i with 0 <= i < len(r) such that r[i] = t. A byte vector t is a valid sentence exactly when there exist an integer k >= 1 and indices j_0,...,j_{k-1} with 0 <= j_l < len(wordDict) for every l, such that s equals the byte concatenation of wordDict[j_0], wordDict[j_1], ..., wordDict[j_{k-1}] in that order, and t equals the byte concatenation of wordDict[j_0], then one byte 32 (ASCII space), then wordDict[j_1], then one byte 32, ..., then one byte 32, then wordDict[j_{k-1}].
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_4 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ t : List Std.U8,
        IsValidSentence s wordDict t →
          ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = t := by
    sorry

  open Classical in
  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ t : List Std.U8,
          IsValidSentence s wordDict t →
            ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = t) := by
    sorry

  /-- Whenever the function returns a result r, for all i and j with 0 <= i < len(r) and 0 <= j < len(r), if r[i] = r[j], then i = j.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_5 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
        (r.val[i]'hi).val = (r.val[j]'hj).val → i = j := by
    sorry

  open Classical in
  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
          (r.val[i]'hi).val = (r.val[j]'hj).val → i = j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), deleting from r[i] all bytes equal to 32 (ASCII space) yields exactly the byte vector s.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_6 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ (i : Nat) (hi : i < r.val.length), deleteSpaces (r.val[i]'hi).val = s.val := by
    sorry

  open Classical in
  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ (i : Nat) (hi : i < r.val.length), deleteSpaces (r.val[i]'hi).val = s.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), every maximal contiguous block of bytes of r[i] that are unequal to 32 (that is, every word between spaces or the whole sentence if there are no spaces) is equal, as a byte vector, to wordDict[j] for some j with 0 <= j < len(wordDict).
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_7 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ (i : Nat) (hi : i < r.val.length), ∀ b ∈ blocks (r.val[i]'hi).val,
        ∃ (j : Nat) (hj : j < wordDict.val.length), dictWord wordDict j = b := by
    sorry

  open Classical in
  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ (i : Nat) (hi : i < r.val.length), ∀ b ∈ blocks (r.val[i]'hi).val,
          ∃ (j : Nat) (hj : j < wordDict.val.length), dictWord wordDict j = b) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), writing t = r[i], we have len(t) > 0, t[0] != 32, t[len(t)-1] != 32, and for every p with 0 <= p < len(t)-1, it is not the case that both t[p] = 32 and t[p+1] = 32.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_8 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ (i : Nat) (hi : i < r.val.length),
        let t := (r.val[i]'hi).val
        t ≠ [] ∧
          (∀ b : Std.U8, t[0]? = some b → ¬ IsSpace b) ∧
            (∀ b : Std.U8, t[t.length - 1]? = some b → ¬ IsSpace b) ∧
              (∀ (p : Nat) (a b : Std.U8),
                t[p]? = some a → t[p + 1]? = some b → ¬ (IsSpace a ∧ IsSpace b)) := by
    sorry

  open Classical in
  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ (i : Nat) (hi : i < r.val.length),
          let t := (r.val[i]'hi).val
          t ≠ [] ∧
            (∀ b : Std.U8, t[0]? = some b → ¬ IsSpace b) ∧
              (∀ b : Std.U8, t[t.length - 1]? = some b → ¬ IsSpace b) ∧
                (∀ (p : Nat) (a b : Std.U8),
                  t[p]? = some a → t[p + 1]? = some b → ¬ (IsSpace a ∧ IsSpace b))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), len(r[i]) <= 2*len(s) - 1.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_9 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val.length ≤ 2 * s.val.length - 1 := by
    sorry

  open Classical in
  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val.length ≤ 2 * s.val.length - 1) := by
    sorry

  /-- Whenever the function returns a result r, len(r) equals the number of sequences (j_0,...,j_{k-1}) of indices such that k >= 1, 0 <= j_l < len(wordDict) for every l, and s equals the byte concatenation of wordDict[j_0], wordDict[j_1], ..., wordDict[j_{k-1}] in that order.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_10 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      r.val.length = numSplits s wordDict := by
    sorry

  open Classical in
  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), r.val.length = numSplits s wordDict) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0 if and only if there do not exist an integer k >= 1 and indices j_0,...,j_{k-1} with 0 <= j_l < len(wordDict) for every l such that s equals the byte concatenation of wordDict[j_0], wordDict[j_1], ..., wordDict[j_{k-1}] in that order.
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_11 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      r.val.length = 0 ↔ ¬ ∃ js : List Nat, Splits s wordDict js := by
    sorry

  open Classical in
  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), r.val.length = 0 ↔ ¬ ∃ js : List Nat, Splits s wordDict js) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), the number of maximal contiguous blocks of bytes in r[i] that are unequal to 32 (that is, the number of words in the sentence) is at most len(s).
    Preconditions: 1 <= len(s) <= 20; 1 <= len(wordDict) <= 1000; for every j with 0 <= j < len(wordDict), 1 <= len(wordDict[j]) <= 10; every byte of s and of every wordDict[j] is an ASCII lowercase letter (97 <= byte <= 122); for all j and k with 0 <= j < k < len(wordDict), wordDict[j] != wordDict[k]. -/
  theorem spec_12 (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
      (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r) :
      ∀ (i : Nat) (hi : i < r.val.length), numBlocks (r.val[i]'hi).val ≤ s.val.length := by
    sorry

  open Classical in
  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (wordDict : Slice ByteVec) (hpre : WellFormed s wordDict)
        (r : SentenceVec) (hr : Aegis.WordBreak.word_break s wordDict = ok r), ∀ (i : Nat) (hi : i < r.val.length), numBlocks (r.val[i]'hi).val ≤ s.val.length) := by
    sorry

  end AegisSpec.WordBreak
