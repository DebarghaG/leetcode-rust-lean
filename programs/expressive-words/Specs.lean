import Aegis.ExpressiveWords.Code.Funs

/-!
# Specifications of `Aegis.ExpressiveWords.expressive_words`

LeetCode problem `expressive-words`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ExpressiveWords

  def sliceBytes (s : Slice Std.U8) : List Nat :=
    s.val.map (fun b => b.val)

  def wordBytes (w : alloc.vec.Vec Std.U8) : List Nat :=
    w.val.map (fun b => b.val)

  def wordsBytes (words : Slice (alloc.vec.Vec Std.U8)) : List (List Nat) :=
    words.val.map wordBytes

  def groups : List Nat → List (Nat × Nat)
    | [] => []
    | c :: rest =>
        let k := (rest.takeWhile (fun b => b = c)).length
        (c, k + 1) :: groups (rest.drop k)
    termination_by l => l.length
    decreasing_by
      simp only [List.length_cons]
      rw [List.length_drop]
      exact Nat.lt_succ_of_le (Nat.sub_le _ _)

  def GroupMatch : List (Nat × Nat) → List (Nat × Nat) → Prop
    | [], [] => True
    | (bw, dw) :: rw, (bs, ds) :: rs =>
        bw = bs ∧ dw ≤ ds ∧ (dw = ds ∨ 3 ≤ ds) ∧ GroupMatch rw rs
    | _, _ => False

  def Stretchy (w s : List Nat) : Prop := GroupMatch (groups w) (groups s)

  noncomputable def numStretchy (s : List Nat) (words : List (List Nat)) : Nat := by
    classical
    exact (words.filter (fun w => decide (Stretchy w s))).length

  def numEqual (s : List Nat) (words : List (List Nat)) : Nat :=
    (words.filter (fun w => w = s)).length

  def numShort (s : List Nat) (words : List (List Nat)) : Nat :=
    (words.filter (fun w => w.length ≤ s.length)).length

  def SameMultiset (l1 l2 : List (List Nat)) : Prop :=
    ∀ w : List Nat, (l1.filter (fun v => v = w)).length = (l2.filter (fun v => v = w)).length

  /-- The function returns a result r (it does not fail). The returned value r equals the number of indices i with 0 <= i < len(words) such that words[i] is stretchy to s, where: a group of a nonempty byte string x is a maximal contiguous block of equal bytes (maximal means it cannot be extended left or right without including a different byte), listed from left to right and represented by its byte and its length; and a word w is stretchy to s iff w and s have the same number of groups, the k-th group of w has the same byte as the k-th group of s for every group index k, and, writing d_k for the length of the k-th group of w and c_k for the length of the k-th group of s, one has d_k <= c_k and (d_k = c_k or c_k >= 3).
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_1
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r ∧
          r.val = ((numStretchy (sliceBytes s) (wordsBytes words) : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r ∧
            r.val = ((numStretchy (sliceBytes s) (wordsBytes words) : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, expressive_words(s, words) returns a result r (a Result.ok value); it does not overflow, index out of bounds, panic, or otherwise fail.
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_2
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.ExpressiveWords.expressive_words s words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.ExpressiveWords.expressive_words s words = ok r) := by
    sorry

  /-- Whenever expressive_words(s, words) returns a result r, 0 <= r <= len(words).
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_3
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          0 ≤ r.val ∧ r.val ≤ ((words.val.length : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            0 ≤ r.val ∧ r.val ≤ ((words.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever expressive_words(s, words) returns a result r, if for every i with 0 <= i < len(words), len(words[i]) > len(s), then r = 0.
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_4
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          (∀ w ∈ words.val, s.val.length < w.val.length) → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            (∀ w ∈ words.val, s.val.length < w.val.length) → r.val = 0) := by
    sorry

  /-- Whenever expressive_words(s, words) returns a result r, r = 0 if and only if there is no index i with 0 <= i < len(words) such that words[i] is stretchy to s (stretchy is the group condition defined in spec_1); equivalently, r > 0 if and only if such a stretchy index exists.
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_5
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          (r.val = 0 ↔ ¬ ∃ w ∈ words.val, Stretchy (wordBytes w) (sliceBytes s)) ∧
            (0 < r.val ↔ ∃ w ∈ words.val, Stretchy (wordBytes w) (sliceBytes s)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            (r.val = 0 ↔ ¬ ∃ w ∈ words.val, Stretchy (wordBytes w) (sliceBytes s)) ∧
              (0 < r.val ↔ ∃ w ∈ words.val, Stretchy (wordBytes w) (sliceBytes s))) := by
    sorry

  /-- Whenever expressive_words(s, words) returns a result r, r = len(words) if and only if for every i with 0 <= i < len(words), words[i] is stretchy to s (using the group condition defined in spec_1).
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_6
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          (r.val = ((words.val.length : Nat) : Int) ↔
            ∀ w ∈ words.val, Stretchy (wordBytes w) (sliceBytes s)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            (r.val = ((words.val.length : Nat) : Int) ↔
              ∀ w ∈ words.val, Stretchy (wordBytes w) (sliceBytes s))) := by
    sorry

  /-- Whenever expressive_words(s, words1) returns r1 and expressive_words(s, words2) returns r2, if words1 and words2 have the same multiset of query byte strings (for every byte string w, the number of i with 0 <= i < len(words1) and words1[i] = w equals the number of j with 0 <= j < len(words2) and words2[j] = w), then r1 = r2.
    Preconditions: len(s) >= 1; len(words1) >= 1; len(words2) >= 1; len(s) <= 100; len(words1) <= 100; len(words2) <= 100; every word in words1 or words2 has length between 1 and 100; every byte of s and of every word in words1 or words2 is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_7
      (s : Slice Std.U8) (words1 words2 : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length)
      (hwords1_pos : 1 ≤ words1.val.length) (hwords2_pos : 1 ≤ words2.val.length)
      (hs_ub : s.val.length ≤ 100)
      (hwords1_ub : words1.val.length ≤ 100) (hwords2_ub : words2.val.length ≤ 100)
      (hwords1_len : ∀ w ∈ words1.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
      (hwords2_len : ∀ w ∈ words2.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords1_ascii : ∀ w ∈ words1.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords2_ascii : ∀ w ∈ words2.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r1 r2 : I64,
        Aegis.ExpressiveWords.expressive_words s words1 = ok r1 →
          Aegis.ExpressiveWords.expressive_words s words2 = ok r2 →
            SameMultiset (wordsBytes words1) (wordsBytes words2) →
              r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (words1 words2 : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length)
        (hwords1_pos : 1 ≤ words1.val.length) (hwords2_pos : 1 ≤ words2.val.length)
        (hs_ub : s.val.length ≤ 100)
        (hwords1_ub : words1.val.length ≤ 100) (hwords2_ub : words2.val.length ≤ 100)
        (hwords1_len : ∀ w ∈ words1.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
        (hwords2_len : ∀ w ∈ words2.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords1_ascii : ∀ w ∈ words1.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords2_ascii : ∀ w ∈ words2.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r1 r2 : I64,
          Aegis.ExpressiveWords.expressive_words s words1 = ok r1 →
            Aegis.ExpressiveWords.expressive_words s words2 = ok r2 →
              SameMultiset (wordsBytes words1) (wordsBytes words2) →
                r1 = r2) := by
    sorry

  /-- Whenever expressive_words(s, A) returns rA and expressive_words(s, B) returns rB, if A is a subsequence of B (B can be obtained from A by inserting zero or more query words, preserving order), then rA <= rB.
    Preconditions: len(s) >= 1; len(A) >= 1; len(B) >= 1; len(s) <= 100; len(A) <= 100; len(B) <= 100; every word in A or B has length between 1 and 100; every byte of s and of every word in A or B is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_8
      (s : Slice Std.U8) (A B : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length)
      (hA_pos : 1 ≤ A.val.length) (hB_pos : 1 ≤ B.val.length)
      (hs_ub : s.val.length ≤ 100)
      (hA_ub : A.val.length ≤ 100) (hB_ub : B.val.length ≤ 100)
      (hA_len : ∀ w ∈ A.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
      (hB_len : ∀ w ∈ B.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hA_ascii : ∀ w ∈ A.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hB_ascii : ∀ w ∈ B.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ rA rB : I64,
        Aegis.ExpressiveWords.expressive_words s A = ok rA →
          Aegis.ExpressiveWords.expressive_words s B = ok rB →
            List.Sublist A.val B.val → rA.val ≤ rB.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (A B : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length)
        (hA_pos : 1 ≤ A.val.length) (hB_pos : 1 ≤ B.val.length)
        (hs_ub : s.val.length ≤ 100)
        (hA_ub : A.val.length ≤ 100) (hB_ub : B.val.length ≤ 100)
        (hA_len : ∀ w ∈ A.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
        (hB_len : ∀ w ∈ B.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hA_ascii : ∀ w ∈ A.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hB_ascii : ∀ w ∈ B.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ rA rB : I64,
          Aegis.ExpressiveWords.expressive_words s A = ok rA →
            Aegis.ExpressiveWords.expressive_words s B = ok rB →
              List.Sublist A.val B.val → rA.val ≤ rB.val) := by
    sorry

  /-- Whenever expressive_words(s, words) returns r and expressive_words(s, words') returns r', r' = r + 1 if w is stretchy to s (using the group condition defined in spec_1), and r' = r if w is not stretchy to s.
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 99; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122); w is a byte string with 1 <= len(w) <= 100 and lowercase bytes; words' is the list obtained from words by appending w as a new last element (so len(words') = len(words) + 1 <= 100). -/
  theorem spec_9
      (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
      (w : alloc.vec.Vec Std.U8)
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ v ∈ words.val, 1 ≤ v.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 99)
      (hword_ub : ∀ v ∈ words.val, v.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hw_len : 1 ≤ w.val.length ∧ w.val.length ≤ 100)
      (hw_ascii : ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords' : words'.val = words.val ++ [w]) :
      ∀ r r' : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          Aegis.ExpressiveWords.expressive_words s words' = ok r' →
            (Stretchy (wordBytes w) (sliceBytes s) → r'.val = r.val + 1) ∧
              (¬ Stretchy (wordBytes w) (sliceBytes s) → r'.val = r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (words words' : Slice (alloc.vec.Vec Std.U8))
        (w : alloc.vec.Vec Std.U8)
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ v ∈ words.val, 1 ≤ v.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 99)
        (hword_ub : ∀ v ∈ words.val, v.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ v ∈ words.val, ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hw_len : 1 ≤ w.val.length ∧ w.val.length ≤ 100)
        (hw_ascii : ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords' : words'.val = words.val ++ [w]), ∀ r r' : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            Aegis.ExpressiveWords.expressive_words s words' = ok r' →
              (Stretchy (wordBytes w) (sliceBytes s) → r'.val = r.val + 1) ∧
                (¬ Stretchy (wordBytes w) (sliceBytes s) → r'.val = r.val)) := by
    sorry

  /-- Whenever expressive_words(s, words) returns a result r, if every maximal contiguous group of equal bytes in s has length 1 or 2, then r equals the number of indices i with 0 <= i < len(words) such that words[i] equals s byte-for-byte.
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_10
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          (∀ g ∈ groups (sliceBytes s), g.2 = 1 ∨ g.2 = 2) →
            r.val = ((numEqual (sliceBytes s) (wordsBytes words) : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            (∀ g ∈ groups (sliceBytes s), g.2 = 1 ∨ g.2 = 2) →
              r.val = ((numEqual (sliceBytes s) (wordsBytes words) : Nat) : Int)) := by
    sorry

  /-- Whenever expressive_words(s, words) returns a result r, r is at least the number of indices i with 0 <= i < len(words) such that words[i] equals s byte-for-byte.
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_11
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          ((numEqual (sliceBytes s) (wordsBytes words) : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            ((numEqual (sliceBytes s) (wordsBytes words) : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever expressive_words(s, words) returns a result r, r is at most the number of indices i with 0 <= i < len(words) such that len(words[i]) <= len(s).
    Preconditions: len(s) >= 1; len(words) >= 1; for every i with 0 <= i < len(words), len(words[i]) >= 1; len(s) <= 100; len(words) <= 100; for every i with 0 <= i < len(words), len(words[i]) <= 100; every byte of s and of every words[i] is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_12
      (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
      (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
      (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
      (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : I64,
        Aegis.ExpressiveWords.expressive_words s words = ok r →
          r.val ≤ ((numShort (sliceBytes s) (wordsBytes words) : Nat) : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length) (hwords_pos : 1 ≤ words.val.length)
        (hword_pos : ∀ w ∈ words.val, 1 ≤ w.val.length)
        (hs_ub : s.val.length ≤ 100) (hwords_ub : words.val.length ≤ 100)
        (hword_ub : ∀ w ∈ words.val, w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hwords_ascii : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : I64,
          Aegis.ExpressiveWords.expressive_words s words = ok r →
            r.val ≤ ((numShort (sliceBytes s) (wordsBytes words) : Nat) : Int)) := by
    sorry

  /-- Whenever expressive_words(s, A) returns rA, expressive_words(s, B) returns rB, and expressive_words(s, A ++ B) returns rAB, one has rAB = rA + rB.
    Preconditions: len(s) >= 1; len(A) >= 1; len(B) >= 1; len(s) <= 100; len(A) <= 100; len(B) <= 100; len(A) + len(B) <= 100; every word in A or B has length between 1 and 100; every byte of s and of every word in A or B is a lowercase ASCII letter (97 <= byte <= 122). -/
  theorem spec_13
      (s : Slice Std.U8) (A B C : Slice (alloc.vec.Vec Std.U8))
      (hs_pos : 1 ≤ s.val.length)
      (hA_pos : 1 ≤ A.val.length) (hB_pos : 1 ≤ B.val.length)
      (hs_ub : s.val.length ≤ 100)
      (hA_ub : A.val.length ≤ 100) (hB_ub : B.val.length ≤ 100)
      (hAB_ub : A.val.length + B.val.length ≤ 100)
      (hA_len : ∀ w ∈ A.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
      (hB_len : ∀ w ∈ B.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
      (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hA_ascii : ∀ w ∈ A.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hB_ascii : ∀ w ∈ B.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hC : C.val = A.val ++ B.val) :
      ∀ rA rB rAB : I64,
        Aegis.ExpressiveWords.expressive_words s A = ok rA →
          Aegis.ExpressiveWords.expressive_words s B = ok rB →
            Aegis.ExpressiveWords.expressive_words s C = ok rAB →
              rAB.val = rA.val + rB.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (A B C : Slice (alloc.vec.Vec Std.U8))
        (hs_pos : 1 ≤ s.val.length)
        (hA_pos : 1 ≤ A.val.length) (hB_pos : 1 ≤ B.val.length)
        (hs_ub : s.val.length ≤ 100)
        (hA_ub : A.val.length ≤ 100) (hB_ub : B.val.length ≤ 100)
        (hAB_ub : A.val.length + B.val.length ≤ 100)
        (hA_len : ∀ w ∈ A.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
        (hB_len : ∀ w ∈ B.val, 1 ≤ w.val.length ∧ w.val.length ≤ 100)
        (hs_ascii : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hA_ascii : ∀ w ∈ A.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hB_ascii : ∀ w ∈ B.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hC : C.val = A.val ++ B.val), ∀ rA rB rAB : I64,
          Aegis.ExpressiveWords.expressive_words s A = ok rA →
            Aegis.ExpressiveWords.expressive_words s B = ok rB →
              Aegis.ExpressiveWords.expressive_words s C = ok rAB →
                rAB.val = rA.val + rB.val) := by
    sorry

  end AegisSpec.ExpressiveWords
