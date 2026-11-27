import Aegis.IsPrefixString.Code.Funs

/-!
# Specifications of `Aegis.IsPrefixString.is_prefix_string`

LeetCode problem `check-if-string-is-a-prefix-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsPrefixString (is_prefix_string)

namespace AegisSpec.IsPrefixString

def concatFrom (words : Slice (alloc.vec.Vec U8)) (lo k : Nat) : List U8 :=
  (((words.val.drop lo).take k).map (fun w => w.val)).flatten

def concatPrefix (words : Slice (alloc.vec.Vec U8)) (k : Nat) : List U8 :=
  concatFrom words 0 k

def concatAll (words : Slice (alloc.vec.Vec U8)) : List U8 :=
  concatPrefix words words.val.length

def sumLensPrefix (words : Slice (alloc.vec.Vec U8)) (k : Nat) : Nat :=
  ((words.val.take k).map (fun w => w.val.length)).sum

def sumLensAll (words : Slice (alloc.vec.Vec U8)) : Nat :=
  sumLensPrefix words words.val.length

/-- The function returns a result r, and r = true if and only if there exists an integer k with 1 <= k <= len(words) such that s equals the byte-sequence concatenation of words[0], words[1], ..., words[k-1]. The concatenation of zero words is the empty byte sequence; the concatenation of words[0..k-1] has length sum_{i=0}^{k-1} len(words[i]) and at each position j (0 <= j < that length) its byte is words[i][j - offset], where i is the unique index with offset <= j < offset + len(words[i]) and offset = sum_{t=0}^{i-1} len(words[t]).
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_1 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r, is_prefix_string s words = ok r ∧
      (r = true ↔ ∃ k, 1 ≤ k ∧ k ≤ words.val.length ∧ s.val = concatPrefix words k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∃ r, is_prefix_string s words = ok r ∧
      (r = true ↔ ∃ k, 1 ≤ k ∧ k ≤ words.val.length ∧ s.val = concatPrefix words k)) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, no out-of-bounds slice access, no arithmetic overflow) for any inputs satisfying the preconditions.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_2 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r, is_prefix_string s words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∃ r, is_prefix_string s words = ok r) := by
  sorry

/-- Whenever the function returns a result r with r = true, there exists an integer k with 1 <= k <= len(words) such that len(s) = sum_{i=0}^{k-1} len(words[i]).
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_3 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true) :
    ∃ k, 1 ≤ k ∧ k ≤ words.val.length ∧ s.val.length = sumLensPrefix words k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true), ∃ k, 1 ≤ k ∧ k ≤ words.val.length ∧ s.val.length = sumLensPrefix words k) := by
  sorry

/-- Whenever the function returns a result r with r = true, len(words[0]) <= len(s) <= sum_{i=0}^{len(words)-1} len(words[i]).
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_4 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true) :
    (words.val[0]).val.length ≤ s.val.length ∧ s.val.length ≤ sumLensAll words := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true), (words.val[0]).val.length ≤ s.val.length ∧ s.val.length ≤ sumLensAll words) := by
  sorry

/-- Whenever len(s) < len(words[0]), the function returns a result r with r = false.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_5 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hlen : s.val.length < (words.val[0]).val.length) :
    ∃ r, is_prefix_string s words = ok r ∧ r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hlen : s.val.length < (words.val[0]).val.length), ∃ r, is_prefix_string s words = ok r ∧ r = false) := by
  sorry

/-- Whenever s equals words[0] as byte sequences (len(s) = len(words[0]) and s[i] = words[0][i] for every i with 0 <= i < len(s)), the function returns a result r with r = true.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_6 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (heq : s.val = (words.val[0]).val) :
    ∃ r, is_prefix_string s words = ok r ∧ r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (heq : s.val = (words.val[0]).val), ∃ r, is_prefix_string s words = ok r ∧ r = true) := by
  sorry

/-- Whenever len(s) > sum_{i=0}^{len(words)-1} len(words[i]), the function returns a result r with r = false.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_7 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hlen : sumLensAll words < s.val.length) :
    ∃ r, is_prefix_string s words = ok r ∧ r = false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hlen : sumLensAll words < s.val.length), ∃ r, is_prefix_string s words = ok r ∧ r = false) := by
  sorry

/-- Whenever s equals the byte-sequence concatenation of all words words[0], words[1], ..., words[len(words)-1], the function returns a result r with r = true.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_8 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (heq : s.val = concatAll words) :
    ∃ r, is_prefix_string s words = ok r ∧ r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (heq : s.val = concatAll words), ∃ r, is_prefix_string s words = ok r ∧ r = true) := by
  sorry

/-- Whenever len(s) = len(words[0]) and s is not equal to words[0] as byte sequences, the function returns a result r with r = false.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_9 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hlen : s.val.length = (words.val[0]).val.length)
    (hne : s.val ≠ (words.val[0]).val) :
    ∃ r, is_prefix_string s words = ok r ∧ r = false := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hlen : s.val.length = (words.val[0]).val.length)
    (hne : s.val ≠ (words.val[0]).val), ∃ r, is_prefix_string s words = ok r ∧ r = false) := by
  sorry

/-- Whenever the function returns a result r with r = true, s is a prefix of the concatenation of all words: i.e., len(s) <= sum_{i=0}^{len(words)-1} len(words[i]) and for every j with 0 <= j < len(s), the j-th byte of s equals the j-th byte of the concatenation of words[0], words[1], ..., words[len(words)-1].
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_10 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true) :
    s.val.length ≤ sumLensAll words ∧
      ∀ (j : Nat), j < s.val.length → s.val[j]! = (concatAll words)[j]! := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true), s.val.length ≤ sumLensAll words ∧
      ∀ (j : Nat), j < s.val.length → s.val[j]! = (concatAll words)[j]!) := by
  sorry

/-- Whenever the function returns a result r with r = true and s is not equal to words[0] as byte sequences (which forces len(words) >= 2 and len(s) > len(words[0])), let t be the suffix of s obtained by deleting its first len(words[0]) bytes: len(t) = len(s) - len(words[0]) and t[j] = s[len(words[0]) + j] for every j with 0 <= j < len(t). Then t is a prefix string of the slice consisting of words[1], words[2], ..., words[len(words)-1], i.e. there exists an integer m with 1 <= m <= len(words)-1 such that t equals the byte-sequence concatenation of words[1], words[2], ..., words[m].
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_11 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true)
    (hne : s.val ≠ (words.val[0]).val) :
    ∃ m, 1 ≤ m ∧ m ≤ words.val.length - 1 ∧
      s.val.drop (words.val[0]).val.length = concatFrom words 1 m := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true)
    (hne : s.val ≠ (words.val[0]).val), ∃ m, 1 ≤ m ∧ m ≤ words.val.length - 1 ∧
      s.val.drop (words.val[0]).val.length = concatFrom words 1 m) := by
  sorry

/-- Whenever the function returns a result r with r = true, there exists exactly one integer k with 1 <= k <= len(words) such that s equals the byte-sequence concatenation of words[0], words[1], ..., words[k-1].
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_12 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true) :
    ∃! k, 1 ≤ k ∧ k ≤ words.val.length ∧ s.val = concatPrefix words k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true), ∃! k, 1 ≤ k ∧ k ≤ words.val.length ∧ s.val = concatPrefix words k) := by
  sorry

/-- Whenever the function returns a result r with r = true, the byte sequence s begins with words[0]: len(words[0]) <= len(s) and for every i with 0 <= i < len(words[0]), s[i] = words[0][i]. Equivalently, if len(s) < len(words[0]) or s[i] != words[0][i] for some 0 <= i < len(words[0]), then r = false.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_13 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true) :
    (words.val[0]).val.length ≤ s.val.length ∧
      ∀ (i : Nat), i < (words.val[0]).val.length → s.val[i]! = (words.val[0]).val[i]! := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok true), (words.val[0]).val.length ≤ s.val.length ∧
      ∀ (i : Nat), i < (words.val[0]).val.length → s.val[i]! = (words.val[0]).val[i]!) := by
  sorry

/-- Whenever the function returns a result r with r = false, for every integer k with 1 <= k <= len(words), s is not equal to the byte-sequence concatenation of words[0], words[1], ..., words[k-1].
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 20; 1 <= len(s) <= 1000; every byte of s and of each words[i] is an ASCII code of a lowercase English letter (97 <= byte <= 122). -/
theorem spec_14 (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok false) :
    ∀ k, 1 ≤ k → k ≤ words.val.length → s.val ≠ concatPrefix words k := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8) (words : Slice (alloc.vec.Vec U8))
    (hwords_len_lo : 1 ≤ words.val.length) (hwords_len_hi : words.val.length ≤ 100)
    (hword_len_bounds : ∀ i (hi : i < words.val.length),
      1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 20)
    (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 1000)
    (hs_ascii : ∀ b, b ∈ s.val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hwords_ascii : ∀ i (hi : i < words.val.length),
      ∀ b, b ∈ (words.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122)
    (hres : is_prefix_string s words = ok false), ∀ k, 1 ≤ k → k ≤ words.val.length → s.val ≠ concatPrefix words k) := by
  sorry

end AegisSpec.IsPrefixString
