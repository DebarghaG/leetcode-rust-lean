import Aegis.SumPrefixScores.Code.Funs

/-!
# Specifications of `Aegis.SumPrefixScores.sum_prefix_scores`

LeetCode problem `sum-of-prefix-scores-of-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumPrefixScores

  abbrev Word := alloc.vec.Vec Std.U8

  def contents (words : Slice Word) : List (List Std.U8) := words.val.map (fun w => w.val)

  def numWords (words : Slice Word) : Nat := (contents words).length

  def wordAt (words : Slice Word) (i : Nat) : List Std.U8 := (contents words).getD i []

  def wordLen (words : Slice Word) (i : Nat) : Nat := (wordAt words i).length

  def answerContents (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun s => s.val)

  def answerAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Int := (answerContents r).getD i 0

  def byteOf (w : List Std.U8) (t : Nat) : Nat := (w.getD t default).val

  def firstByteOf (w : List Std.U8) : Nat := byteOf w 0

  abbrev agreeOn (x y : List Std.U8) (k : Nat) : Prop := x.take k = y.take k

  def lcp (x y : List Std.U8) : Nat :=
    Nat.findGreatest (fun L => agreeOn x y L) (min x.length y.length)

  def score (words : Slice Word) (i k : Nat) : Nat :=
    ((contents words).filter
      (fun w => decide (k ≤ w.length ∧ agreeOn (wordAt words i) w k))).length

  def firstByteCount (words : Slice Word) (i : Nat) : Nat :=
    ((contents words).filter
      (fun w => decide (firstByteOf w = firstByteOf (wordAt words i)))).length

  /-- Whenever the function returns a result r, len(r) = n and for every i with 0 <= i < n, r[i] = sum_{k=1}^{len(words[i])} score(i,k), where score(i,k) is the number of indices j with 0 <= j < n such that k <= len(words[j]) and for every t with 0 <= t < k, words[i][t] = words[j][t].
    Preconditions: words is a slice of byte vectors; let n = len(words). 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 1000; every byte of every words[i] is a lowercase English letter (ASCII 97..122). -/
  theorem spec_1 (words : Slice Word)
      (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
      (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
      (hlower : ∀ i t, i < numWords words → t < wordLen words i →
        97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122) :
      ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
        (answerContents r).length = numWords words ∧
          ∀ i, i < numWords words →
            answerAt r i
              = ∑ k ∈ Finset.Icc 1 (wordLen words i), (score words i k : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice Word)
        (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
        (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
        (hlower : ∀ i t, i < numWords words → t < wordLen words i →
          97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122), ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
          (answerContents r).length = numWords words ∧
            ∀ i, i < numWords words →
              answerAt r i
                = ∑ k ∈ Finset.Icc 1 (wordLen words i), (score words i k : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every words satisfying the preconditions.
    Preconditions: words is a slice of byte vectors; let n = len(words). 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 1000; every byte of every words[i] is a lowercase English letter (ASCII 97..122). -/
  theorem spec_2 (words : Slice Word)
      (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
      (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
      (hlower : ∀ i t, i < numWords words → t < wordLen words i →
        97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122) :
      ∃ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice Word)
        (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
        (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
        (hlower : ∀ i t, i < numWords words → t < wordLen words i →
          97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122), ∃ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i,j < n, if words[i] is a prefix of words[j] (len(words[i]) <= len(words[j]) and words[i][t] = words[j][t] for all 0 <= t < len(words[i])), then r[j] - r[i] >= len(words[j]) - len(words[i]).
    Preconditions: words is a slice of byte vectors; let n = len(words). 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 1000; every byte of every words[i] is a lowercase English letter (ASCII 97..122). -/
  theorem spec_3 (words : Slice Word)
      (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
      (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
      (hlower : ∀ i t, i < numWords words → t < wordLen words i →
        97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122) :
      ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
        ∀ i, i < numWords words → ∀ j, j < numWords words →
          List.IsPrefix (wordAt words i) (wordAt words j) →
            answerAt r j - answerAt r i
              ≥ (wordLen words j : Int) - (wordLen words i : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice Word)
        (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
        (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
        (hlower : ∀ i t, i < numWords words → t < wordLen words i →
          97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122), ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
          ∀ i, i < numWords words → ∀ j, j < numWords words →
            List.IsPrefix (wordAt words i) (wordAt words j) →
              answerAt r j - answerAt r i
                ≥ (wordLen words j : Int) - (wordLen words i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = sum_{j=0}^{n-1} lcp(words[i], words[j]), where for byte strings x,y, lcp(x,y) is the largest L with 0 <= L <= min(len(x),len(y)) such that x[t] = y[t] for every t with 0 <= t < L.
    Preconditions: words is a slice of byte vectors; let n = len(words). 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 1000; every byte of every words[i] is a lowercase English letter (ASCII 97..122). -/
  theorem spec_4 (words : Slice Word)
      (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
      (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
      (hlower : ∀ i t, i < numWords words → t < wordLen words i →
        97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122) :
      ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
        ∀ i, i < numWords words →
          answerAt r i
            = ∑ j ∈ Finset.range (numWords words),
                (lcp (wordAt words i) (wordAt words j) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice Word)
        (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
        (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
        (hlower : ∀ i t, i < numWords words → t < wordLen words i →
          97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122), ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
          ∀ i, i < numWords words →
            answerAt r i
              = ∑ j ∈ Finset.range (numWords words),
                  (lcp (wordAt words i) (wordAt words j) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= len(words[i]) * C_i, where C_i is the number of j with 0 <= j < n and words[j][0] = words[i][0].
    Preconditions: words is a slice of byte vectors; let n = len(words). 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 1000; every byte of every words[i] is a lowercase English letter (ASCII 97..122). -/
  theorem spec_5 (words : Slice Word)
      (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
      (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
      (hlower : ∀ i t, i < numWords words → t < wordLen words i →
        97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122) :
      ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
        ∀ i, i < numWords words →
          answerAt r i ≤ (wordLen words i : Int) * (firstByteCount words i : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice Word)
        (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
        (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
        (hlower : ∀ i t, i < numWords words → t < wordLen words i →
          97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122), ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
          ∀ i, i < numWords words →
            answerAt r i ≤ (wordLen words i : Int) * (firstByteCount words i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] >= C_i + len(words[i]) - 1, where C_i is the number of j with 0 <= j < n and words[j][0] = words[i][0].
    Preconditions: words is a slice of byte vectors; let n = len(words). 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 1000; every byte of every words[i] is a lowercase English letter (ASCII 97..122). -/
  theorem spec_6 (words : Slice Word)
      (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
      (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
      (hlower : ∀ i t, i < numWords words → t < wordLen words i →
        97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122) :
      ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
        ∀ i, i < numWords words →
          answerAt r i ≥ (firstByteCount words i : Int) + (wordLen words i : Int) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice Word)
        (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
        (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
        (hlower : ∀ i t, i < numWords words → t < wordLen words i →
          97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122), ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
          ∀ i, i < numWords words →
            answerAt r i ≥ (firstByteCount words i : Int) + (wordLen words i : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = len(words[i]) if and only if for every j with 0 <= j < n and j != i, words[j][0] != words[i][0].
    Preconditions: words is a slice of byte vectors; let n = len(words). 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 1000; every byte of every words[i] is a lowercase English letter (ASCII 97..122). -/
  theorem spec_7 (words : Slice Word)
      (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
      (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
      (hlower : ∀ i t, i < numWords words → t < wordLen words i →
        97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122) :
      ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
        ∀ i, i < numWords words →
          (answerAt r i = (wordLen words i : Int) ↔
            ∀ j, j < numWords words → j ≠ i →
              firstByteOf (wordAt words j) ≠ firstByteOf (wordAt words i)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice Word)
        (hn : 1 ≤ numWords words ∧ numWords words ≤ 1000)
        (hwlen : ∀ i, i < numWords words → 1 ≤ wordLen words i ∧ wordLen words i ≤ 1000)
        (hlower : ∀ i t, i < numWords words → t < wordLen words i →
          97 ≤ byteOf (wordAt words i) t ∧ byteOf (wordAt words i) t ≤ 122), ∀ r, Aegis.SumPrefixScores.sum_prefix_scores words = ok r →
          ∀ i, i < numWords words →
            (answerAt r i = (wordLen words i : Int) ↔
              ∀ j, j < numWords words → j ≠ i →
                firstByteOf (wordAt words j) ≠ firstByteOf (wordAt words i))) := by
    sorry

  end AegisSpec.SumPrefixScores
