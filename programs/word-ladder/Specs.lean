import Aegis.LadderLength.Code.Funs

/-!
# Specifications of `Aegis.LadderLength.ladder_length`

LeetCode problem `word-ladder`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LadderLength

namespace AegisSpec.LadderLength

def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def AllLowerBytes (w : List Std.U8) : Prop := ∀ b, b ∈ w → IsLowerByte b

def DiffersAtOneIndex (a b : List Std.U8) : Prop :=
  a.length = b.length ∧
    ∃ j, j < a.length ∧ (a[j]!).val ≠ (b[j]!).val ∧
      ∀ t, t < a.length → t ≠ j → (a[t]!).val = (b[t]!).val

def OccursIn (w : List Std.U8) (words : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∃ i, i < words.length ∧ (words[i]!).val = w

def PairwiseDistinctWords (words : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ i j, i < j → j < words.length → (words[i]!).val ≠ (words[j]!).val

def PairwiseDistinctSeq (w : List (List Std.U8)) : Prop :=
  ∀ i j, i < w.length → j < w.length → i ≠ j → w[i]! ≠ w[j]!

def ValidSeq (beginWord endWord : List Std.U8) (words : List (alloc.vec.Vec Std.U8))
    (w : List (List Std.U8)) : Prop :=
  1 ≤ w.length ∧
    w[0]! = beginWord ∧
    w[w.length - 1]! = endWord ∧
    (∀ i, i + 1 < w.length → DiffersAtOneIndex w[i]! w[i + 1]!) ∧
    (∀ i, 0 < i → i < w.length → OccursIn w[i]! words)

def PermutedWords (words words' : List (alloc.vec.Vec Std.U8)) : Prop :=
  (words.map (fun v => v.val)).Perm (words'.map (fun v => v.val))

def WellFormed (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ beginWord.val.length ∧
    beginWord.val.length ≤ 10 ∧
    endWord.val.length = beginWord.val.length ∧
    1 ≤ wordList.val.length ∧
    wordList.val.length ≤ 5000 ∧
    (∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length) ∧
    AllLowerBytes beginWord.val ∧
    AllLowerBytes endWord.val ∧
    (∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val) ∧
    beginWord.val ≠ endWord.val ∧
    PairwiseDistinctWords wordList.val

/-- Whenever ladder_length(beginWord, endWord, wordList) returns a result r, the following holds. If no valid transformation sequence exists, then r = 0. If a valid transformation sequence exists, then r > 0, there is a valid transformation sequence with exactly r words, and every valid transformation sequence has at least r words. A valid transformation sequence is a finite sequence of byte arrays w[0],...,w[m-1] with m >= 1 such that w[0] = beginWord, w[m-1] = endWord, for each i with 0 <= i < m-1 the arrays w[i] and w[i+1] have equal length and differ at exactly one index (there is j with 0 <= j < len(w[i]) such that w[i][j] != w[i+1][j] and w[i][t] = w[i+1][t] for every t != j), and for each i with 1 <= i < m there is k with 0 <= k < len(wordList) and w[i] = wordList[k]. Its number of words is m.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and for all i, j with 0 <= i < j < len(wordList), wordList[i] != wordList[j]. -/
theorem spec_1 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ((¬ ∃ w, ValidSeq beginWord.val endWord.val wordList.val w) → r.val = 0) ∧
          ((∃ w, ValidSeq beginWord.val endWord.val wordList.val w) →
            0 < r.val ∧
              (∃ w, ValidSeq beginWord.val endWord.val wordList.val w ∧
                (w.length : Int) = r.val) ∧
              (∀ w, ValidSeq beginWord.val endWord.val wordList.val w →
                r.val ≤ (w.length : Int))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ((¬ ∃ w, ValidSeq beginWord.val endWord.val wordList.val w) → r.val = 0) ∧
          ((∃ w, ValidSeq beginWord.val endWord.val wordList.val w) →
            0 < r.val ∧
              (∃ w, ValidSeq beginWord.val endWord.val wordList.val w ∧
                (w.length : Int) = r.val) ∧
              (∀ w, ValidSeq beginWord.val endWord.val wordList.val w →
                r.val ≤ (w.length : Int)))) := by
  sorry

/-- ladder_length(beginWord, endWord, wordList) returns a result r; in particular it does not fail, overflow, panic, or get stuck on any input satisfying the preconditions.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_2 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∃ r : Std.I64, ladder_length beginWord endWord wordList = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∃ r : Std.I64, ladder_length beginWord endWord wordList = ok r) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns a result r, 0 <= r <= len(wordList) + 1.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_3 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        0 ≤ r.val ∧ r.val ≤ (wordList.val.length : Int) + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        0 ≤ r.val ∧ r.val ≤ (wordList.val.length : Int) + 1) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns a result r and r != 0, r >= 2.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_4 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r → r.val ≠ 0 → 2 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r → r.val ≠ 0 → 2 ≤ r.val) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns a result r, if there is no index i with 0 <= i < len(wordList) such that wordList[i] = endWord, then r = 0.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_5 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ¬ OccursIn endWord.val wordList.val → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ¬ OccursIn endWord.val wordList.val → r.val = 0) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns a result r, if for every i with 0 <= i < len(wordList), wordList[i] and beginWord do not differ at exactly one index (that is, they are equal, have different lengths, or differ at two or more indices), then r = 0.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_6 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        (∀ i, i < wordList.val.length →
          ¬ DiffersAtOneIndex (wordList.val[i]!).val beginWord.val) → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        (∀ i, i < wordList.val.length →
          ¬ DiffersAtOneIndex (wordList.val[i]!).val beginWord.val) → r.val = 0) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns a result r, if endWord occurs in wordList and beginWord and endWord differ at exactly one index, then r = 2.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_7 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val)
    (hEndOccurs : OccursIn endWord.val wordList.val)
    (hAdjacent : DiffersAtOneIndex beginWord.val endWord.val) :
    ∀ r : Std.I64, ladder_length beginWord endWord wordList = ok r → r.val = 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val)
    (hEndOccurs : OccursIn endWord.val wordList.val)
    (hAdjacent : DiffersAtOneIndex beginWord.val endWord.val), ∀ r : Std.I64, ladder_length beginWord endWord wordList = ok r → r.val = 2) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns a result r with r > 0, there exists a valid transformation sequence w[0],...,w[r-1] with exactly r words such that w[0] = beginWord, w[r-1] = endWord, each adjacent pair w[i], w[i+1] differs at exactly one index, each w[i] with 1 <= i < r occurs in wordList, and the r words w[0],...,w[r-1] are pairwise distinct.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); 1 <= len(wordList) <= 5000; for every i with 0 <= i < len(wordList), len(wordList[i]) = len(beginWord); beginWord, endWord, and every wordList[i] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_8 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        0 < r.val →
          ∃ w, ValidSeq beginWord.val endWord.val wordList.val w ∧
            PairwiseDistinctSeq w ∧ (w.length : Int) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : 1 ≤ wordList.val.length)
    (hListLenLe : wordList.val.length ≤ 5000)
    (hWordLens : ∀ i, i < wordList.val.length →
      (wordList.val[i]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWordsLower : ∀ i, i < wordList.val.length → AllLowerBytes (wordList.val[i]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        0 < r.val →
          ∃ w, ValidSeq beginWord.val endWord.val wordList.val w ∧
            PairwiseDistinctSeq w ∧ (w.length : Int) = r.val) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns r and ladder_length(beginWord, endWord, wordList') returns r', it holds that r' = r.
  Preconditions: The constraints of spec_1 hold for (beginWord, endWord, wordList); wordList' is a slice of byte-vector words satisfying the same constraints with respect to beginWord and endWord; and wordList' is a permutation of wordList (the two slices have the same multiset of byte arrays). -/
theorem spec_9 (beginWord endWord : Slice Std.U8)
    (wordList wordList' : Slice (alloc.vec.Vec Std.U8))
    (hWF : WellFormed beginWord endWord wordList)
    (hWF' : WellFormed beginWord endWord wordList')
    (hPerm : PermutedWords wordList.val wordList'.val) :
    ∀ r r' : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ladder_length beginWord endWord wordList' = ok r' → r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList wordList' : Slice (alloc.vec.Vec Std.U8))
    (hWF : WellFormed beginWord endWord wordList)
    (hWF' : WellFormed beginWord endWord wordList')
    (hPerm : PermutedWords wordList.val wordList'.val), ∀ r r' : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ladder_length beginWord endWord wordList' = ok r' → r' = r) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns r and ladder_length(beginWord, endWord, wordList') returns r', if r > 0 then r' > 0 and r' <= r.
  Preconditions: The constraints of spec_1 hold for (beginWord, endWord, wordList); wordList' is a slice of byte-vector words satisfying the same constraints with respect to beginWord and endWord; and every byte array occurring as an entry of wordList also occurs as an entry of wordList'. -/
theorem spec_10 (beginWord endWord : Slice Std.U8)
    (wordList wordList' : Slice (alloc.vec.Vec Std.U8))
    (hWF : WellFormed beginWord endWord wordList)
    (hWF' : WellFormed beginWord endWord wordList')
    (hSubset : ∀ w, OccursIn w wordList.val → OccursIn w wordList'.val) :
    ∀ r r' : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ladder_length beginWord endWord wordList' = ok r' →
          0 < r.val → 0 < r'.val ∧ r'.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList wordList' : Slice (alloc.vec.Vec Std.U8))
    (hWF : WellFormed beginWord endWord wordList)
    (hWF' : WellFormed beginWord endWord wordList')
    (hSubset : ∀ w, OccursIn w wordList.val → OccursIn w wordList'.val), ∀ r r' : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ladder_length beginWord endWord wordList' = ok r' →
          0 < r.val → 0 < r'.val ∧ r'.val ≤ r.val) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns r and ladder_length(endWord, beginWord, wordList) returns r', it holds that r' = r.
  Preconditions: The constraints of spec_1 hold for (beginWord, endWord, wordList); wordList contains beginWord and wordList contains endWord. -/
theorem spec_11 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hWF : WellFormed beginWord endWord wordList)
    (hBeginOccurs : OccursIn beginWord.val wordList.val)
    (hEndOccurs : OccursIn endWord.val wordList.val) :
    ∀ r r' : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ladder_length endWord beginWord wordList = ok r' → r' = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hWF : WellFormed beginWord endWord wordList)
    (hBeginOccurs : OccursIn beginWord.val wordList.val)
    (hEndOccurs : OccursIn endWord.val wordList.val), ∀ r r' : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ladder_length endWord beginWord wordList = ok r' → r' = r) := by
  sorry

/-- Whenever ladder_length(beginWord, endWord, wordList) returns r, if wordList[0] = endWord and beginWord and wordList[0] differ at exactly one index, then r = 2; otherwise r = 0.
  Preconditions: 1 <= len(beginWord) <= 10; len(endWord) = len(beginWord); len(wordList) = 1; len(wordList[0]) = len(beginWord); beginWord, endWord, and wordList[0] consist only of bytes 97 through 122 (lowercase English letters); beginWord != endWord; and all wordList entries are pairwise distinct. -/
theorem spec_12 (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : wordList.val.length = 1)
    (hWord0Len : (wordList.val[0]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWord0Lower : AllLowerBytes (wordList.val[0]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val) :
    ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ((((wordList.val[0]!).val = endWord.val) ∧
            DiffersAtOneIndex beginWord.val (wordList.val[0]!).val) → r.val = 2) ∧
          (¬ (((wordList.val[0]!).val = endWord.val) ∧
              DiffersAtOneIndex beginWord.val (wordList.val[0]!).val) → r.val = 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (beginWord endWord : Slice Std.U8)
    (wordList : Slice (alloc.vec.Vec Std.U8))
    (hBeginLen : 1 ≤ beginWord.val.length)
    (hBeginLenLe : beginWord.val.length ≤ 10)
    (hEndLen : endWord.val.length = beginWord.val.length)
    (hListLen : wordList.val.length = 1)
    (hWord0Len : (wordList.val[0]!).val.length = beginWord.val.length)
    (hBeginLower : AllLowerBytes beginWord.val)
    (hEndLower : AllLowerBytes endWord.val)
    (hWord0Lower : AllLowerBytes (wordList.val[0]!).val)
    (hBeginEndNe : beginWord.val ≠ endWord.val)
    (hWordsDistinct : PairwiseDistinctWords wordList.val), ∀ r : Std.I64,
      ladder_length beginWord endWord wordList = ok r →
        ((((wordList.val[0]!).val = endWord.val) ∧
            DiffersAtOneIndex beginWord.val (wordList.val[0]!).val) → r.val = 2) ∧
          (¬ (((wordList.val[0]!).val = endWord.val) ∧
              DiffersAtOneIndex beginWord.val (wordList.val[0]!).val) → r.val = 0)) := by
  sorry

end AegisSpec.LadderLength
