import Aegis.MaxRepeating.Code.Funs

/-!
# Specifications of `Aegis.MaxRepeating.max_repeating`

LeetCode problem `maximum-repeating-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxRepeating

def byteAt (l : List Std.U8) (i : Nat) : Nat :=
  (l[i]?).elim 0 fun b => b.val

def LowercaseBytes (s : Slice Std.U8) : Prop :=
  ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122

def wordPow (word : Slice Std.U8) : Nat → List Std.U8
  | 0 => []
  | k + 1 => wordPow word k ++ word.val

def Occurs (sequence word : Slice Std.U8) (k : Nat) : Prop :=
  ∃ i : Nat, i + k * word.val.length ≤ sequence.val.length ∧
    ∀ j : Nat, j < k * word.val.length →
      byteAt sequence.val (i + j) = byteAt word.val (j % word.val.length)

def RunOf (sequence : Slice Std.U8) (b : Nat) (L : Nat) : Prop :=
  ∃ i : Nat, i + L ≤ sequence.val.length ∧
    ∀ j : Nat, j < L → byteAt sequence.val (i + j) = b

/-- The function returns a result r (an i64) and r is the maximum k >= 0 such that the concatenation of k copies of word is a contiguous substring of sequence. Formally, let word^k denote the byte sequence obtained by concatenating k copies of word (with word^0 the empty sequence). Then: (1) word^r is a contiguous substring of sequence, meaning there exists an index i with 0 <= i and i + r*len(word) <= len(sequence) such that for every j with 0 <= j < r*len(word), sequence[i+j] = word[j mod len(word)]; and (2) for every integer k > r, word^k is not a contiguous substring of sequence. Equivalently, r = max{ k >= 0 : word^k is a contiguous substring of sequence }.
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_1 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        0 ≤ r.val ∧ Occurs sequence word r.val.toNat ∧
        ∀ k : Nat, r.val < (k : Int) → ¬ Occurs sequence word k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        0 ≤ r.val ∧ Occurs sequence word r.val.toNat ∧
        ∀ k : Nat, r.val < (k : Int) → ¬ Occurs sequence word k) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_2 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r * len(word) <= len(sequence).
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_3 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        r.val * (word.val.length : Int) ≤ (sequence.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        r.val * (word.val.length : Int) ≤ (sequence.val.length : Int)) := by
  sorry

/-- The function returns a result r and the concatenation of r copies of word is a contiguous substring of sequence, i.e., there exists an index i with 0 <= i and i + r*len(word) <= len(sequence) such that for every j with 0 <= j < r*len(word), sequence[i+j] = word[j mod len(word)].
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_4 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        Occurs sequence word r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        Occurs sequence word r.val.toNat) := by
  sorry

/-- The function returns a result r and for every integer k with k > r, the concatenation of k copies of word is not a contiguous substring of sequence. That is, there is no index i with 0 <= i and i + k*len(word) <= len(sequence) such that for every j with 0 <= j < k*len(word), sequence[i+j] = word[j mod len(word)].
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_5 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        ∀ k : Nat, r.val < (k : Int) → ¬ Occurs sequence word k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        ∀ k : Nat, r.val < (k : Int) → ¬ Occurs sequence word k) := by
  sorry

/-- The function returns a result r and (r >= 1) if and only if word is a contiguous substring of sequence, i.e., there exists an index i with 0 <= i and i + len(word) <= len(sequence) such that for every j with 0 <= j < len(word), sequence[i+j] = word[j].
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_6 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        (1 ≤ r.val ↔ Occurs sequence word 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        (1 ≤ r.val ↔ Occurs sequence word 1)) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters), and len(word) > len(sequence). -/
theorem spec_7 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_longer : sequence.val.length < word.val.length) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_longer : sequence.val.length < word.val.length), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = 1 if for every j with 0 <= j < len(sequence), sequence[j] = word[j]; otherwise r = 0.
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters), and len(word) = len(sequence). -/
theorem spec_8 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_same_len : word.val.length = sequence.val.length) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        ((∀ j : Nat, j < sequence.val.length →
            byteAt sequence.val j = byteAt word.val j) → r.val = 1) ∧
        ((∃ j : Nat, j < sequence.val.length ∧
            byteAt sequence.val j ≠ byteAt word.val j) → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_same_len : word.val.length = sequence.val.length), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        ((∀ j : Nat, j < sequence.val.length →
            byteAt sequence.val j = byteAt word.val j) → r.val = 1) ∧
        ((∃ j : Nat, j < sequence.val.length ∧
            byteAt sequence.val j ≠ byteAt word.val j) → r.val = 0)) := by
  sorry

/-- The function returns a result r and r = len(sequence) / len(word) (integer division).
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters), len(sequence) is a multiple of len(word), and for every j with 0 <= j < len(sequence), sequence[j] = word[j mod len(word)]. -/
theorem spec_9 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_multiple : word.val.length ∣ sequence.val.length)
    (h_periodic : ∀ j : Nat, j < sequence.val.length →
      byteAt sequence.val j = byteAt word.val (j % word.val.length)) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        r.val = ((sequence.val.length / word.val.length : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_multiple : word.val.length ∣ sequence.val.length)
    (h_periodic : ∀ j : Nat, j < sequence.val.length →
      byteAt sequence.val j = byteAt word.val (j % word.val.length)), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        r.val = ((sequence.val.length / word.val.length : Nat) : Int)) := by
  sorry

/-- The function returns a result r and for every integer k with 1 <= k <= r, the concatenation of k copies of word is a contiguous substring of sequence.
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_10 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        ∀ k : Nat, 1 ≤ k → (k : Int) ≤ r.val → Occurs sequence word k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        ∀ k : Nat, 1 ≤ k → (k : Int) ≤ r.val → Occurs sequence word k) := by
  sorry

/-- The function returns a result r (i.e., it does not panic, overflow, or fail to terminate) for every sequence and word satisfying the preconditions.
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, and every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters). -/
theorem spec_11 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word) :
    ∃ r : Std.I64, Aegis.MaxRepeating.max_repeating sequence word = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word), ∃ r : Std.I64, Aegis.MaxRepeating.max_repeating sequence word = ok r) := by
  sorry

/-- The function returns a result r and r is the length of the longest contiguous run of the byte word[0] in sequence. That is, r is the maximum integer L >= 0 such that there exists an index i with 0 <= i and i + L <= len(sequence) and for every j with 0 <= j < L, sequence[i+j] = word[0].
  Preconditions: 1 <= len(sequence) <= 100, 1 <= len(word) <= 100, every byte in sequence and word is between 97 and 122 (inclusive, i.e., lowercase English letters), and len(word) = 1. -/
theorem spec_12 (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_one : word.val.length = 1) :
    ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        0 ≤ r.val ∧ RunOf sequence (byteAt word.val 0) r.val.toNat ∧
        ∀ L : Nat, r.val < (L : Int) → ¬ RunOf sequence (byteAt word.val 0) L := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (sequence word : Slice Std.U8)
    (h_n1 : 1 ≤ sequence.val.length) (h_n2 : sequence.val.length ≤ 100)
    (h_w1 : 1 ≤ word.val.length) (h_w2 : word.val.length ≤ 100)
    (h_seq : LowercaseBytes sequence) (h_word : LowercaseBytes word)
    (h_one : word.val.length = 1), ∃ r : Std.I64,
      Aegis.MaxRepeating.max_repeating sequence word = ok r ∧
        0 ≤ r.val ∧ RunOf sequence (byteAt word.val 0) r.val.toNat ∧
        ∀ L : Nat, r.val < (L : Int) → ¬ RunOf sequence (byteAt word.val 0) L) := by
  sorry

end AegisSpec.MaxRepeating
