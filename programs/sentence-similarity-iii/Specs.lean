import Aegis.AreSentencesSimilar.Code.Funs

/-!
# Specifications of `Aegis.AreSentencesSimilar.are_sentences_similar`

LeetCode problem `sentence-similarity-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.AreSentencesSimilar

namespace AegisSpec.AreSentencesSimilar

def spaceByte : Std.U8 := 32#u8

def isSpaceByte (b : Std.U8) : Bool := b == spaceByte

def words (s : Slice Std.U8) : List (List Std.U8) :=
  (List.splitOnP isSpaceByte s.val).filter (fun w => !w.isEmpty)

def isLetterOrSpaceByte (b : Std.U8) : Prop :=
  (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122) ∨ b.val = 32

def noLeadingSpace (s : List Std.U8) : Prop :=
  ∀ b, s.head? = some b → b.val ≠ 32

def noTrailingSpace (s : List Std.U8) : Prop :=
  ∀ b, s.getLast? = some b → b.val ≠ 32

def noConsecutiveSpaces (s : List Std.U8) : Prop :=
  ∀ (i : Nat) (b1 b2 : Std.U8),
    s[i]? = some b1 → s[i + 1]? = some b2 → ¬ (b1.val = 32 ∧ b2.val = 32)

def validSentence (s : Slice Std.U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 100 ∧
  (∀ b, b ∈ s.val → isLetterOrSpaceByte b) ∧
  noLeadingSpace s.val ∧ noTrailingSpace s.val ∧ noConsecutiveSpaces s.val

def InsertionSimilar (W1 W2 : List (List Std.U8)) : Prop :=
  (W1.length ≤ W2.length ∧
    ∃ k, k ≤ W1.length ∧
      (∀ i, i < k → W1[i]? = W2[i]?) ∧
      (∀ i, k ≤ i → i < W1.length →
        W1[i]? = W2[i + (W2.length - W1.length)]?)) ∨
  (W2.length ≤ W1.length ∧
    ∃ k, k ≤ W2.length ∧
      (∀ i, i < k → W2[i]? = W1[i]?) ∧
      (∀ i, k ≤ i → i < W2.length →
        W2[i]? = W1[i + (W1.length - W2.length)]?))

def IsSubsequence (A B : List (List Std.U8)) : Prop :=
  ∃ j : Nat → Nat,
    (∀ i, i < A.length → j i < B.length) ∧
    (∀ i₁ i₂, i₁ < i₂ → i₂ < A.length → j i₁ < j i₂) ∧
    (∀ i, i < A.length → A[i]? = B[j i]?)

def commonPrefixLen : List (List Std.U8) → List (List Std.U8) → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as', b :: bs => if a = b then 1 + commonPrefixLen as' bs else 0

def commonSuffixLen (A B : List (List Std.U8)) : Nat :=
  commonPrefixLen A.reverse B.reverse

def shorterWords (W1 W2 : List (List Std.U8)) : List (List Std.U8) :=
  if W1.length ≤ W2.length then W1 else W2

def longerWords (W1 W2 : List (List Std.U8)) : List (List Std.U8) :=
  if W1.length ≤ W2.length then W2 else W1

/-- Define InsertionSimilar(W1,W2) to hold iff either (a) n1 <= n2 and there exists an integer k with 0 <= k <= n1 such that for every i with 0 <= i < k, W1[i] = W2[i], and for every i with k <= i < n1, W1[i] = W2[i + (n2 - n1)]; or (b) n2 <= n1 and there exists an integer k with 0 <= k <= n2 such that for every i with 0 <= i < k, W2[i] = W1[i], and for every i with k <= i < n2, W2[i] = W1[i + (n1 - n2)]. The function returns a result r and r = true iff InsertionSimilar(W1,W2).
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order, with each block compared as a byte string; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Thus W1 and W2 are nonempty word sequences. -/
theorem spec_1 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2) :
    ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔ InsertionSimilar (words sentence1) (words sentence2)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2), ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔ InsertionSimilar (words sentence1) (words sentence2))) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, panic, or overflow on these inputs.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. -/
theorem spec_2 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2) :
    ∃ r, are_sentences_similar sentence1 sentence2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2), ∃ r, are_sentences_similar sentence1 sentence2 = ok r) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Assume W1 = W2 as sequences of words. -/
theorem spec_3 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hwords : words sentence1 = words sentence2) :
    ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hwords : words sentence1 = words sentence2), ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧ r = true) := by
  sorry

/-- Let r12 be the result of are_sentences_similar(sentence1, sentence2) and r21 be the result of are_sentences_similar(sentence2, sentence1). The function returns results for both calls and r12 = r21.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order. Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. -/
theorem spec_4 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2) :
    ∃ r12 r21, are_sentences_similar sentence1 sentence2 = ok r12 ∧
      are_sentences_similar sentence2 sentence1 = ok r21 ∧ r12 = r21 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2), ∃ r12 r21, are_sentences_similar sentence1 sentence2 = ok r12 ∧
      are_sentences_similar sentence2 sentence1 = ok r21 ∧ r12 = r21) := by
  sorry

/-- The function returns a result r and r = true iff W1[0] = W2[0] or W1[0] = W2[n2 - 1].
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Assume n1 = 1. -/
theorem spec_5 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn1 : (words sentence1).length = 1) :
    ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔ ((words sentence1).head? = (words sentence2).head? ∨
        (words sentence1).head? = (words sentence2).getLast?)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn1 : (words sentence1).length = 1), ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔ ((words sentence1).head? = (words sentence2).head? ∨
        (words sentence1).head? = (words sentence2).getLast?))) := by
  sorry

/-- The function returns a result r and r = false.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Assume W1[0] != W2[0] and W1[n1 - 1] != W2[n2 - 1]. -/
theorem spec_6 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hhead : (words sentence1).head? ≠ (words sentence2).head?)
    (hlast : (words sentence1).getLast? ≠ (words sentence2).getLast?) :
    ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧ r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hhead : (words sentence1).head? ≠ (words sentence2).head?)
    (hlast : (words sentence1).getLast? ≠ (words sentence2).getLast?), ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧ r = false) := by
  sorry

/-- The function returns a result r and r = true iff W1[i] = W2[i] for every i with 0 <= i < n1.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Assume n1 = n2. -/
theorem spec_7 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn : (words sentence1).length = (words sentence2).length) :
    ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔ ∀ i, i < (words sentence1).length →
        (words sentence1)[i]? = (words sentence2)[i]?) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn : (words sentence1).length = (words sentence2).length), ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔ ∀ i, i < (words sentence1).length →
        (words sentence1)[i]? = (words sentence2)[i]?)) := by
  sorry

/-- Whenever the function returns a result r, if r = true then W1[i] = W2[i + (n2 - n1)] for every i with 0 <= i < n1; equivalently, W1 is a suffix of W2.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Assume n1 < n2 and W1[0] != W2[0]. -/
theorem spec_8 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn : (words sentence1).length < (words sentence2).length)
    (hhead : (words sentence1).head? ≠ (words sentence2).head?) :
    ∀ r, are_sentences_similar sentence1 sentence2 = ok r → r = true →
      ∀ i, i < (words sentence1).length →
        (words sentence1)[i]? =
          (words sentence2)[i + ((words sentence2).length -
            (words sentence1).length)]? := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn : (words sentence1).length < (words sentence2).length)
    (hhead : (words sentence1).head? ≠ (words sentence2).head?), ∀ r, are_sentences_similar sentence1 sentence2 = ok r → r = true →
      ∀ i, i < (words sentence1).length →
        (words sentence1)[i]? =
          (words sentence2)[i + ((words sentence2).length -
            (words sentence1).length)]?) := by
  sorry

/-- Whenever the function returns a result r, if r = true then W1[i] = W2[i] for every i with 0 <= i < n1; equivalently, W1 is a prefix of W2.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Assume n1 < n2 and W1[n1 - 1] != W2[n2 - 1]. -/
theorem spec_9 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn : (words sentence1).length < (words sentence2).length)
    (hlast : (words sentence1).getLast? ≠ (words sentence2).getLast?) :
    ∀ r, are_sentences_similar sentence1 sentence2 = ok r → r = true →
      ∀ i, i < (words sentence1).length →
        (words sentence1)[i]? = (words sentence2)[i]? := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2)
    (hn : (words sentence1).length < (words sentence2).length)
    (hlast : (words sentence1).getLast? ≠ (words sentence2).getLast?), ∀ r, are_sentences_similar sentence1 sentence2 = ok r → r = true →
      ∀ i, i < (words sentence1).length →
        (words sentence1)[i]? = (words sentence2)[i]?) := by
  sorry

/-- Whenever the function returns a result r, if r = true then either W1 is a subsequence of W2 or W2 is a subsequence of W1. Here W1 is a subsequence of W2 means there exist indices j_0 < j_1 < ... < j_{n1-1} with 0 <= j_i < n2 and W1[i] = W2[j_i] for all i with 0 <= i < n1; the other direction is defined analogously.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. -/
theorem spec_10 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2) :
    ∀ r, are_sentences_similar sentence1 sentence2 = ok r → r = true →
      IsSubsequence (words sentence1) (words sentence2) ∨
        IsSubsequence (words sentence2) (words sentence1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2), ∀ r, are_sentences_similar sentence1 sentence2 = ok r → r = true →
      IsSubsequence (words sentence1) (words sentence2) ∨
        IsSubsequence (words sentence2) (words sentence1)) := by
  sorry

/-- The function returns a result r and r = true iff p + q >= m.
  Preconditions: Let words(s) be the sequence of maximal contiguous non-space blocks of the byte slice s, in left-to-right order; let W1=words(sentence1), W2=words(sentence2), n1=len(W1), n2=len(W2). Assume sentence1 and sentence2 are valid sentences: 1 <= len(sentence1) <= 100 and 1 <= len(sentence2) <= 100; every byte is an uppercase/lowercase English ASCII letter (65-90 or 97-122) or a space (32); the first and last bytes are not spaces; and no two consecutive bytes are spaces. Let S = W1 and L = W2 if n1 <= n2; otherwise let S = W2 and L = W1; let m = len(S). Let p be the greatest integer with 0 <= p <= m such that S[i] = L[i] for every i with 0 <= i < p, and let q be the greatest integer with 0 <= q <= m such that S[m - 1 - i] = L[len(L) - 1 - i] for every i with 0 <= i < q. -/
theorem spec_11 (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2) :
    ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔
        commonPrefixLen (shorterWords (words sentence1) (words sentence2))
            (longerWords (words sentence1) (words sentence2)) +
          commonSuffixLen (shorterWords (words sentence1) (words sentence2))
            (longerWords (words sentence1) (words sentence2)) ≥
          (shorterWords (words sentence1) (words sentence2)).length) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8)
    (hvalid1 : validSentence sentence1) (hvalid2 : validSentence sentence2), ∃ r, are_sentences_similar sentence1 sentence2 = ok r ∧
      (r = true ↔
        commonPrefixLen (shorterWords (words sentence1) (words sentence2))
            (longerWords (words sentence1) (words sentence2)) +
          commonSuffixLen (shorterWords (words sentence1) (words sentence2))
            (longerWords (words sentence1) (words sentence2)) ≥
          (shorterWords (words sentence1) (words sentence2)).length)) := by
  sorry

end AegisSpec.AreSentencesSimilar
