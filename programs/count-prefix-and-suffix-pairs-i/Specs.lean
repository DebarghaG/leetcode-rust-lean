import Aegis.CountPrefixSuffixPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs`

LeetCode problem `count-prefix-and-suffix-pairs-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountPrefixSuffixPairs

  def wordBytes (words : Slice (alloc.vec.Vec U8)) : List (List Nat) :=
    words.val.map fun w => w.val.map fun b => b.val

  def wordList (words : Slice (alloc.vec.Vec U8)) (i : Nat) : List Nat :=
    (wordBytes words).getD i []

  def wordLen (words : Slice (alloc.vec.Vec U8)) (i : Nat) : Nat := (wordList words i).length

  def wordByte (words : Slice (alloc.vec.Vec U8)) (i k : Nat) : Nat :=
    (wordList words i).getD k 0

  def LenLE (words : Slice (alloc.vec.Vec U8)) (i j : Nat) : Prop :=
    wordLen words i ≤ wordLen words j

  def LenEq (words : Slice (alloc.vec.Vec U8)) (i j : Nat) : Prop :=
    wordLen words i = wordLen words j

  def SamePrefix (words : Slice (alloc.vec.Vec U8)) (i j : Nat) : Prop :=
    ∀ k, k < wordLen words i → wordByte words i k = wordByte words j k

  def SameSuffix (words : Slice (alloc.vec.Vec U8)) (i j : Nat) : Prop :=
    ∀ k, k < wordLen words i →
      wordByte words i k = wordByte words j (wordLen words j - wordLen words i + k)

  def IsPrefixSuffix (words : Slice (alloc.vec.Vec U8)) (i j : Nat) : Prop :=
    LenLE words i j ∧ SamePrefix words i j ∧ SameSuffix words i j

  noncomputable def pairCount (words : Slice (alloc.vec.Vec U8))
      (p : Nat → Nat → Prop) : Nat :=
    ((List.range words.val.length).product (List.range words.val.length)).countP
      fun q => @decide (q.1 < q.2 ∧ p q.1 q.2) (Classical.propDecidable _)

  def ValidInput (words : Slice (alloc.vec.Vec U8)) : Prop :=
    1 ≤ words.val.length ∧ words.val.length ≤ 50 ∧
    (∀ i, i < words.val.length → 1 ≤ wordLen words i ∧ wordLen words i ≤ 10) ∧
    (∀ i, i < words.val.length → ∀ k, k < wordLen words i →
      97 ≤ wordByte words i k ∧ wordByte words i k ≤ 122)

  /-- Whenever the function returns a result r, r equals the number of index pairs (i, j) satisfying all of: 0 <= i < j < len(words); len(words[i]) <= len(words[j]); for every k with 0 <= k < len(words[i]), the k-th byte of words[i] equals the k-th byte of words[j]; and for every k with 0 <= k < len(words[i]), the k-th byte of words[i] equals the (len(words[j]) - len(words[i]) + k)-th byte of words[j].
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_1 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        r.val = (pairCount words fun i j =>
              LenLE words i j ∧ SamePrefix words i j ∧ SameSuffix words i j : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          r.val = (pairCount words fun i j =>
                LenLE words i j ∧ SamePrefix words i j ∧ SameSuffix words i j : Int)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail (no overflow, out-of-bounds access, or panic) for any input satisfying the preconditions.
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_2 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∃ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∃ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_3 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= (len(words) * (len(words) - 1)) / 2.
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_4 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        r.val ≤ ((words.val.length * (words.val.length - 1)) / 2 : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          r.val ≤ ((words.val.length * (words.val.length - 1)) / 2 : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the number of index pairs (i, j) such that 0 <= i < j < len(words) and len(words[i]) <= len(words[j]).
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_5 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        r.val ≤ (pairCount words fun i j => LenLE words i j : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          r.val ≤ (pairCount words fun i j => LenLE words i j : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the number of index pairs (i, j) such that 0 <= i < j < len(words), len(words[i]) <= len(words[j]), and for every k with 0 <= k < len(words[i]), the k-th byte of words[i] equals the k-th byte of words[j].
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_6 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        r.val ≤ (pairCount words fun i j => LenLE words i j ∧ SamePrefix words i j : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          r.val ≤ (pairCount words fun i j => LenLE words i j ∧ SamePrefix words i j : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the number of index pairs (i, j) such that 0 <= i < j < len(words), len(words[i]) <= len(words[j]), and for every k with 0 <= k < len(words[i]), the k-th byte of words[i] equals the (len(words[j]) - len(words[i]) + k)-th byte of words[j].
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_7 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        r.val ≤ (pairCount words fun i j => LenLE words i j ∧ SameSuffix words i j : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          r.val ≤ (pairCount words fun i j => LenLE words i j ∧ SameSuffix words i j : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the number of index pairs (i, j) such that 0 <= i < j < len(words), len(words[i]) = len(words[j]), and for every k with 0 <= k < len(words[i]), the k-th byte of words[i] equals the k-th byte of words[j].
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_8 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        (pairCount words fun i j => LenEq words i j ∧ SamePrefix words i j : Int) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          (pairCount words fun i j => LenEq words i j ∧ SamePrefix words i j : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if there exists a nonempty byte vector w such that words[i] is byte-equal to w for every i with 0 <= i < len(words), then r = (len(words) * (len(words) - 1)) / 2.
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_9 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        (∃ w : List Nat, w ≠ [] ∧ ∀ i, i < words.val.length → wordList words i = w) →
        r.val = ((words.val.length * (words.val.length - 1)) / 2 : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          (∃ w : List Nat, w ≠ [] ∧ ∀ i, i < words.val.length → wordList words i = w) →
          r.val = ((words.val.length * (words.val.length - 1)) / 2 : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an integer L with L >= 1 such that len(words[i]) = L for every i with 0 <= i < len(words), then r equals the number of index pairs (i, j) such that 0 <= i < j < len(words), len(words[i]) = len(words[j]), and for every k with 0 <= k < len(words[i]), the k-th byte of words[i] equals the k-th byte of words[j].
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_10 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        (∃ L : Nat, 1 ≤ L ∧ ∀ i, i < words.val.length → wordLen words i = L) →
        r.val = (pairCount words fun i j => LenEq words i j ∧ SamePrefix words i j : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          (∃ L : Nat, 1 ≤ L ∧ ∀ i, i < words.val.length → wordLen words i = L) →
          r.val = (pairCount words fun i j => LenEq words i j ∧ SamePrefix words i j : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if for every i and j with 0 <= i < j < len(words) we have len(words[i]) > len(words[j]), then r = 0.
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_11 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        (∀ i j, i < j → j < words.val.length → wordLen words j < wordLen words i) →
        r.val = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          (∀ i j, i < j → j < words.val.length → wordLen words j < wordLen words i) →
          r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, if for every i and j with 0 <= i < j < len(words), the first byte of words[i] differs from the first byte of words[j], then r = 0.
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_12 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        (∀ i j, i < j → j < words.val.length → wordByte words i 0 ≠ wordByte words j 0) →
        r.val = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          (∀ i j, i < j → j < words.val.length → wordByte words i 0 ≠ wordByte words j 0) →
          r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exist indices i and j such that 0 <= i < j < len(words), len(words[i]) <= len(words[j]), for every k with 0 <= k < len(words[i]) the k-th byte of words[i] equals the k-th byte of words[j], and for every k with 0 <= k < len(words[i]) the k-th byte of words[i] equals the (len(words[j]) - len(words[i]) + k)-th byte of words[j].
    Preconditions: len(words) is an integer with 1 <= len(words) <= 50; for every i with 0 <= i < len(words), len(words[i]) is an integer with 1 <= len(words[i]) <= 10; and for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]), the k-th byte of words[i] is a lowercase English letter (97 <= byte <= 122). All indices are 0-based. -/
  theorem spec_13 (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words) :
      ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
        0 < r.val ↔ ∃ i j, i < j ∧ j < words.val.length ∧
          LenLE words i j ∧ SamePrefix words i j ∧ SameSuffix words i j := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (h : ValidInput words), ∀ r, Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs words = ok r →
          0 < r.val ↔ ∃ i j, i < j ∧ j < words.val.length ∧
            LenLE words i j ∧ SamePrefix words i j ∧ SameSuffix words i j) := by
    sorry

  end AegisSpec.CountPrefixSuffixPairs
