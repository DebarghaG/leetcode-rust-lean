import Aegis.MinDistance.Code.Funs

/-!
# Specifications of `Aegis.MinDistance.min_distance`

LeetCode problem `delete-operation-for-two-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinDistance

  namespace AegisSpec.MinDistance

  def CommonSubseq (u s t : List Std.U8) : Prop := u.Sublist s ∧ u.Sublist t

  def IsLongestCommonSubseqLen (L : Nat) (s t : List Std.U8) : Prop :=
    (∃ u : List Std.U8, CommonSubseq u s t ∧ u.length = L) ∧
      ∀ L' : Nat, (∃ u : List Std.U8, CommonSubseq u s t ∧ u.length = L') → L' ≤ L

  def revSlice (w : Slice Std.U8) : Slice Std.U8 :=
    Slice.from w.val.reverse (by
      have h : w.val.length = w.leng := Data.ListN.ListN_length w.list
      rw [List.length_reverse, h]
      exact w.bound)

  def tailSlice (w : Slice Std.U8) : Slice Std.U8 :=
    Slice.from w.val.tail (by
      have h : w.val.length = w.leng := Data.ListN.ListN_length w.list
      have hb : w.leng ≤ Usize.max := w.bound
      have h2 := List.length_tail (l := w.val)
      omega)

  def initSlice (w : Slice Std.U8) : Slice Std.U8 :=
    Slice.from w.val.dropLast (by
      have h : w.val.length = w.leng := Data.ListN.ListN_length w.list
      have hb : w.leng ≤ Usize.max := w.bound
      have h2 := List.length_dropLast (xs := w.val)
      omega)

  /-- The function returns a result r (an I64) and r equals the minimum total number of single-character deletions, taken from word1 and word2, that make the two byte sequences equal. Equivalently, let L be the largest natural number for which there exists a byte sequence s of length L that is a subsequence of both word1 and word2, where a sequence is a subsequence if it can be obtained by deleting zero or more bytes, so the empty sequence is allowed; then r = len(word1) + len(word2) - 2*L.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_1 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, min_distance word1 word2 = ok r ∧
        ∃ L : Nat, IsLongestCommonSubseqLen L word1.val word2.val ∧
          r.val = (word1.val.length : Int) + (word2.val.length : Int) - 2 * (L : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, min_distance word1 word2 = ok r ∧
          ∃ L : Nat, IsLongestCommonSubseqLen L word1.val word2.val ∧
            r.val = (word1.val.length : Int) + (word2.val.length : Int) - 2 * (L : Int)) := by
    sorry

  /-- For every word1 and word2 satisfying the preconditions, the function returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_2 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, min_distance word1 word2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, min_distance word1 word2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, 0 <= r.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_3 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, r <= len(word1) + len(word2).
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_4 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      r.val ≤ (word1.val.length : Int) + (word2.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), r.val ≤ (word1.val.length : Int) + (word2.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, r >= |len(word1) - len(word2)|, where |x| denotes absolute value.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_5 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      |(word1.val.length : Int) - (word2.val.length : Int)| ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), |(word1.val.length : Int) - (word2.val.length : Int)| ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, r and len(word1) + len(word2) have the same parity; equivalently, len(word1) + len(word2) - r is an even integer.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_6 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      ∃ k : Int, (word1.val.length : Int) + (word2.val.length : Int) - r.val = 2 * k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), ∃ k : Int, (word1.val.length : Int) + (word2.val.length : Int) - r.val = 2 * k) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, r = 0 if and only if word1 and word2 are equal byte-for-byte, that is, len(word1) = len(word2) and for every 0 <= i < len(word1), word1[i] = word2[i].
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_7 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      r.val = 0 ↔ word1.val = word2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), r.val = 0 ↔ word1.val = word2.val) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, if no byte value occurs in both word1 and word2, meaning for every 0 <= i < len(word1) and every 0 <= j < len(word2), word1[i] != word2[j], then r = len(word1) + len(word2).
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_8 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h7 : ∀ (i : Nat) (hi : i < word1.val.length) (j : Nat) (hj : j < word2.val.length),
              word1.val[i] ≠ word2.val[j])
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      r.val = (word1.val.length : Int) + (word2.val.length : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h7 : ∀ (i : Nat) (hi : i < word1.val.length) (j : Nat) (hj : j < word2.val.length),
                word1.val[i] ≠ word2.val[j])
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), r.val = (word1.val.length : Int) + (word2.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, if word1 is a subsequence of word2, that is, word1 can be obtained by deleting zero or more bytes from word2 (which implies len(word1) <= len(word2)), then r = len(word2) - len(word1).
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_9 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h7 : word1.val.Sublist word2.val)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      r.val = (word2.val.length : Int) - (word1.val.length : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h7 : word1.val.Sublist word2.val)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), r.val = (word2.val.length : Int) - (word1.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, there exists a byte sequence t that is a subsequence of both word1 and word2 such that r = len(word1) + len(word2) - 2*len(t).
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_10 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      ∃ t : List Std.U8, CommonSubseq t word1.val word2.val ∧
        r.val = (word1.val.length : Int) + (word2.val.length : Int) - 2 * (t.length : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), ∃ t : List Std.U8, CommonSubseq t word1.val word2.val ∧
          r.val = (word1.val.length : Int) + (word2.val.length : Int) - 2 * (t.length : Int)) := by
    sorry

  /-- For every word1 and word2 satisfying the preconditions, if min_distance(word1, word2) returns r1 and min_distance(word2, word1) returns r2, then r1 = r2.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_11 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
      (hr2 : min_distance word2 word1 = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
        (hr2 : min_distance word2 word1 = ok r2), r1 = r2) := by
    sorry

  /-- Let rev(u) be the byte sequence obtained by reversing u. For every word1 and word2 satisfying the preconditions, if min_distance(word1, word2) returns r1 and min_distance(rev(word1), rev(word2)) returns r2, then r1 = r2.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_12 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
      (hr2 : min_distance (revSlice word1) (revSlice word2) = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
        (hr2 : min_distance (revSlice word1) (revSlice word2) = ok r2), r1 = r2) := by
    sorry

  /-- If len(word1) >= 2, len(word2) >= 2, and word1[0] = word2[0], then whenever min_distance(word1, word2) returns r1 and min_distance(word1[1:], word2[1:]) returns r2, we have r1 = r2, where u[1:] is the suffix obtained by deleting the first byte of u.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_13 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h7 : 2 ≤ word1.val.length) (h8 : 2 ≤ word2.val.length)
      (h9 : word1.val[0] = word2.val[0])
      (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
      (hr2 : min_distance (tailSlice word1) (tailSlice word2) = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h7 : 2 ≤ word1.val.length) (h8 : 2 ≤ word2.val.length)
        (h9 : word1.val[0] = word2.val[0])
        (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
        (hr2 : min_distance (tailSlice word1) (tailSlice word2) = ok r2), r1 = r2) := by
    sorry

  /-- If len(word1) >= 2, len(word2) >= 2, and word1[len(word1)-1] = word2[len(word2)-1], then whenever min_distance(word1, word2) returns r1 and min_distance(word1[0:len(word1)-1], word2[0:len(word2)-1]) returns r2, we have r1 = r2.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_14 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h7 : 2 ≤ word1.val.length) (h8 : 2 ≤ word2.val.length)
      (h9 : word1.val[word1.val.length - 1] = word2.val[word2.val.length - 1])
      (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
      (hr2 : min_distance (initSlice word1) (initSlice word2) = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h7 : 2 ≤ word1.val.length) (h8 : 2 ≤ word2.val.length)
        (h9 : word1.val[word1.val.length - 1] = word2.val[word2.val.length - 1])
        (r1 r2 : Std.I64) (hr1 : min_distance word1 word2 = ok r1)
        (hr2 : min_distance (initSlice word1) (initSlice word2) = ok r2), r1 = r2) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, r = len(word1) + len(word2) if and only if no byte value occurs in both word1 and word2, i.e. for every 0 <= i < len(word1) and every 0 <= j < len(word2), word1[i] != word2[j].
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_15 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      r.val = (word1.val.length : Int) + (word2.val.length : Int) ↔
        (∀ (i : Nat) (hi : i < word1.val.length) (j : Nat) (hj : j < word2.val.length),
          word1.val[i] ≠ word2.val[j]) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), r.val = (word1.val.length : Int) + (word2.val.length : Int) ↔
          (∀ (i : Nat) (hi : i < word1.val.length) (j : Nat) (hj : j < word2.val.length),
            word1.val[i] ≠ word2.val[j])) := by
    sorry

  /-- Whenever the function returns a result r on word1 and word2, r = |len(word1) - len(word2)| if and only if the shorter string is a subsequence of the longer one: if len(word1) <= len(word2), word1 is a subsequence of word2; otherwise, word2 is a subsequence of word1.
    Preconditions: len(word1) >= 1, len(word2) >= 1, len(word1) <= 500, len(word2) <= 500, and every byte of word1 and word2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_16 (word1 word2 : Slice Std.U8)
      (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
      (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
      (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (r : Std.I64) (hr : min_distance word1 word2 = ok r) :
      r.val = |(word1.val.length : Int) - (word2.val.length : Int)| ↔
        ((word1.val.length ≤ word2.val.length → word1.val.Sublist word2.val) ∧
          (word2.val.length < word1.val.length → word2.val.Sublist word1.val)) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1 : 1 ≤ word1.val.length) (h2 : 1 ≤ word2.val.length)
        (h3 : word1.val.length ≤ 500) (h4 : word2.val.length ≤ 500)
        (h5 : ∀ b : Std.U8, b ∈ word1.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (h6 : ∀ b : Std.U8, b ∈ word2.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (r : Std.I64) (hr : min_distance word1 word2 = ok r), r.val = |(word1.val.length : Int) - (word2.val.length : Int)| ↔
          ((word1.val.length ≤ word2.val.length → word1.val.Sublist word2.val) ∧
            (word2.val.length < word1.val.length → word2.val.Sublist word1.val))) := by
    sorry

  end AegisSpec.MinDistance
