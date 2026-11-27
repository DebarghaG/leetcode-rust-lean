import Aegis.ValidSequence.Code.Funs

/-!
# Specifications of `Aegis.ValidSequence.valid_sequence`

LeetCode problem `find-the-lexicographically-smallest-valid-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ValidSequence

namespace AegisSpec.ValidSequence

def charAt (word1 : Slice Std.U8) (i : Int) : Option Std.U8 :=
  if 0 ≤ i then word1.val[i.toNat]? else none

def intVals (r : alloc.vec.Vec Std.I64) : List Int :=
  r.val.map fun x => x.val

def mismatchCount (word1 word2 : Slice Std.U8) (s : List Int) : Nat :=
  go word1 word2.val s
where

  go : Slice Std.U8 → List Std.U8 → List Int → Nat
    | _, [], _ => 0
    | _, _ :: _, [] => 0
    | w1, b :: bs, i :: is =>
        (match charAt w1 i with
         | some c => if c.val = b.val then 0 else 1
         | none => 1) + go w1 bs is

def StrictIncr (s : List Int) : Prop :=
  ∀ (i : Nat) (h : i + 1 < s.length), s[i]'(by omega) < s[i+1]'(by omega)

def InBounds (s : List Int) (n : Nat) : Prop :=
  ∀ (i : Nat) (h : i < s.length), 0 ≤ s[i]'(by omega) ∧ s[i]'(by omega) < (n : Int)

def IsValidSeq (word1 word2 : Slice Std.U8) (s : List Int) : Prop :=
  s.length = word2.val.length ∧
    StrictIncr s ∧
    InBounds s word1.val.length ∧
    mismatchCount word1 word2 s ≤ 1

def LexLE (a b : List Int) : Prop :=
  a = b ∨
    ∃ (k : Nat), ∃ (ha : k < a.length) (hb : k < b.length),
      (∀ (i : Nat) (hi : i < k), a[i]'(by omega) = b[i]'(by omega)) ∧
        a[k]'ha < b[k]'hb

/-- The function returns a result r. If there exists a valid sequence of indices for word1 and word2, then len(r) = m, r itself is a valid sequence, and r is lexicographically less than or equal to every valid sequence of length m. If no valid sequence exists, then r is the empty vector. A valid sequence s of length m is one with 0 <= s[0] < s[1] < ... < s[m-1] < n and with at most one i in 0..m-1 such that word1[s[i]] != word2[i]. Lexicographic comparison is on the integer arrays: for equal-length arrays a and b, a <=lex b means a = b, or there is k with 0 <= k < m such that a[i] = b[i] for all i < k and a[k] < b[k].
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_1 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : alloc.vec.Vec Std.I64,
      valid_sequence word1 word2 = ok r ∧
        ((∃ s : List Int, IsValidSeq word1 word2 s) →
          r.val.length = word2.val.length ∧
            IsValidSeq word1 word2 (intVals r) ∧
            ∀ s : List Int, IsValidSeq word1 word2 s → LexLE (intVals r) s) ∧
        (¬ (∃ s : List Int, IsValidSeq word1 word2 s) → r.val = []) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : alloc.vec.Vec Std.I64,
      valid_sequence word1 word2 = ok r ∧
        ((∃ s : List Int, IsValidSeq word1 word2 s) →
          r.val.length = word2.val.length ∧
            IsValidSeq word1 word2 (intVals r) ∧
            ∀ s : List Int, IsValidSeq word1 word2 s → LexLE (intVals r) s) ∧
        (¬ (∃ s : List Int, IsValidSeq word1 word2 s) → r.val = [])) := by
  sorry

/-- The function returns a result r rather than failing: for these inputs there is no overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_2 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : alloc.vec.Vec Std.I64, valid_sequence word1 word2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : alloc.vec.Vec Std.I64, valid_sequence word1 word2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 or len(r) = m; that is, the returned vector is either empty or has exactly len(word2) elements.
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_3 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r) :
    r.val.length = 0 ∨ r.val.length = word2.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r), r.val.length = 0 ∨ r.val.length = word2.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), the integer r[i] is nonnegative: 0 <= r[i].
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_4 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length), 0 ≤ (r.val[i]'(by omega)).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r), ∀ (i : Nat) (hi : i < r.val.length), 0 ≤ (r.val[i]'(by omega)).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] < n; hence every returned value is a valid 0-based index into word1.
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_5 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length), (r.val[i]'(by omega)).val < (word1.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r), ∀ (i : Nat) (hi : i < r.val.length), (r.val[i]'(by omega)).val < (word1.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, its entries are strictly increasing: for every i with 0 <= i and i+1 < len(r), r[i] < r[i+1].
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_6 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r) :
    ∀ (i : Nat) (hi : i + 1 < r.val.length),
      (r.val[i]'(by omega)).val < (r.val[i+1]'(by omega)).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r), ∀ (i : Nat) (hi : i + 1 < r.val.length),
      (r.val[i]'(by omega)).val < (r.val[i+1]'(by omega)).val) := by
  sorry

/-- Whenever the function returns a result r with len(r) = m and 0 <= r[i] < n for all i in 0..m-1, the selected string x defined by x[i] = word1[r[i]] for 0 <= i < m differs from word2 in at most one position: the number of i with 0 <= i < m and word1[r[i]] != word2[i] is at most 1.
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_7 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r)
    (hlen : r.val.length = word2.val.length)
    (hbounds : ∀ (i : Nat) (hi : i < word2.val.length),
      0 ≤ (r.val[i]'(by omega)).val ∧
        (r.val[i]'(by omega)).val < (word1.val.length : Int)) :
    mismatchCount word1 word2 (intVals r) ≤ 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r)
    (hlen : r.val.length = word2.val.length)
    (hbounds : ∀ (i : Nat) (hi : i < word2.val.length),
      0 ≤ (r.val[i]'(by omega)).val ∧
        (r.val[i]'(by omega)).val < (word1.val.length : Int)), mismatchCount word1 word2 (intVals r) ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 if and only if there does not exist a strictly increasing sequence s = (s[0],...,s[m-1]) with 0 <= s[0] < ... < s[m-1] < n and with at most one i in 0..m-1 such that word1[s[i]] != word2[i].
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_8 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r) :
    r.val.length = 0 ↔ ¬ (∃ s : List Int, IsValidSeq word1 word2 s) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r), r.val.length = 0 ↔ ¬ (∃ s : List Int, IsValidSeq word1 word2 s)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = m, r is a valid sequence and r is lexicographically minimal among all valid sequences: 0 <= r[0] < ... < r[m-1] < n, at most one i in 0..m-1 has word1[r[i]] != word2[i], and for every valid sequence s = (s[0],...,s[m-1]) with 0 <= s[0] < ... < s[m-1] < n and at most one mismatch, either r = s or there exists k with 0 <= k < m such that r[i] = s[i] for all i < k and r[k] < s[k].
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_9 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r)
    (hlen : r.val.length = word2.val.length) :
    IsValidSeq word1 word2 (intVals r) ∧
      ∀ s : List Int, IsValidSeq word1 word2 s → LexLE (intVals r) s := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r)
    (hlen : r.val.length = word2.val.length), IsValidSeq word1 word2 (intVals r) ∧
      ∀ s : List Int, IsValidSeq word1 word2 s → LexLE (intVals r) s) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 0, every strictly increasing sequence s = (s[0],...,s[m-1]) with 0 <= s[0] < ... < s[m-1] < n has at least two mismatches: the number of i in 0..m-1 with word1[s[i]] != word2[i] is at least 2.
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, and every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters). -/
theorem spec_10 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r)
    (hlen : r.val.length = 0) :
    ∀ (s : List Int), s.length = word2.val.length → StrictIncr s →
      InBounds s word1.val.length → 2 ≤ mismatchCount word1 word2 s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (r : alloc.vec.Vec Std.I64) (hr : valid_sequence word1 word2 = ok r)
    (hlen : r.val.length = 0), ∀ (s : List Int), s.length = word2.val.length → StrictIncr s →
      InBounds s word1.val.length → 2 ≤ mismatchCount word1 word2 s) := by
  sorry

/-- The function returns the one-element vector [0]; that is, the result r has len(r) = 1 and r[0] = 0.
  Preconditions: Let n = len(word1) and m = len(word2). We assume 1 <= m < n <= 300000, every byte of word1 and word2 is in the ASCII range 97..122 (lowercase English letters), and in addition m = 1. -/
theorem spec_11 (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h6 : word2.val.length = 1) :
    ∃ (r : alloc.vec.Vec Std.I64) (x : Std.I64),
      valid_sequence word1 word2 = ok r ∧ r.val.length = 1 ∧ r.val = [x] ∧ x.val = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1 : 1 ≤ word2.val.length) (h2 : word2.val.length < word1.val.length)
    (h3 : word1.val.length ≤ 300000)
    (h4 : ∀ b ∈ word1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h5 : ∀ b ∈ word2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h6 : word2.val.length = 1), ∃ (r : alloc.vec.Vec Std.I64) (x : Std.I64),
      valid_sequence word1 word2 = ok r ∧ r.val.length = 1 ∧ r.val = [x] ∧ x.val = 0) := by
  sorry

end AegisSpec.ValidSequence
