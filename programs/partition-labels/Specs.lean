import Aegis.PartitionLabels.Code.Funs

/-!
# Specifications of `Aegis.PartitionLabels.partition_labels`

LeetCode problem `partition-labels`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.PartitionLabels

namespace AegisSpec.PartitionLabels

def prefixSum (r : List I64) (j : Nat) : Int := ((r.take j).map (fun x => x.val)).sum

def total (r : List I64) : Int := (r.map (fun x => x.val)).sum

def OccursIn (s : Slice U8) (a b : Int) (c : Int) : Prop :=
  ∃ (i : Nat) (hi : i < s.val.length), a ≤ (i : Int) ∧ (i : Int) < b ∧ ((s.val[i]'hi).val : Int) = c

def IsCut (s : Slice U8) (a q b : Int) : Prop :=
  ∀ c : Int, ¬ (OccursIn s a q c ∧ OccursIn s q b c)

def distinctCount (s : Slice U8) : Nat := (s.val.map (fun b => b.val)).dedup.length

def PairwiseDistinct (s : Slice U8) : Prop := (s.val.map (fun b => b.val)).Nodup

def SameEqualityPattern (s t : Slice U8) : Prop :=
  ∀ i j : Nat, i < s.val.length → j < s.val.length →
    (s.val[i]? = s.val[j]? ↔ t.val[i]? = t.val[j]?)

/-- The function returns a result r. Let n = len(s), k = len(r), and P(j) = r[0] + r[1] + ... + r[j-1] for 0 <= j <= k (so P(0) = 0). Then: (a) k >= 1 and r[i] >= 1 for every i with 0 <= i < k; (b) P(k) = n; (c) for every j with 0 < j < k and every byte value c, it is not the case that both (c = s[i] for some i with 0 <= i < P(j)) and (c = s[i'] for some i' with P(j) <= i' < n); (d) for every list r' of integers with k' = len(r'), P'(0) = 0, P'(j) = r'[0] + ... + r'[j-1], which satisfies (a)-(c) with r', k', P' in place of r, k, P, we have k' <= k.
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s) (s is a string of lowercase English letters represented as a byte slice). -/
theorem spec_1 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∃ r : alloc.vec.Vec I64,
      partition_labels s = ok r ∧

      1 ≤ r.val.length ∧
      (∀ (i : Nat) (hi : i < r.val.length), 1 ≤ (r.val[i]'hi).val) ∧

      prefixSum r.val r.val.length = (s.val.length : Int) ∧

      (∀ (j : Nat), 0 < j → j < r.val.length →
        IsCut s 0 (prefixSum r.val j) (s.val.length : Int)) ∧

      (∀ r' : List I64,
        1 ≤ r'.length →
        (∀ (i : Nat) (hi : i < r'.length), 1 ≤ (r'[i]'hi).val) →
        prefixSum r' r'.length = (s.val.length : Int) →
        (∀ (j : Nat), 0 < j → j < r'.length →
          IsCut s 0 (prefixSum r' j) (s.val.length : Int)) →
        r'.length ≤ r.val.length) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∃ r : alloc.vec.Vec I64,
      partition_labels s = ok r ∧

      1 ≤ r.val.length ∧
      (∀ (i : Nat) (hi : i < r.val.length), 1 ≤ (r.val[i]'hi).val) ∧

      prefixSum r.val r.val.length = (s.val.length : Int) ∧

      (∀ (j : Nat), 0 < j → j < r.val.length →
        IsCut s 0 (prefixSum r.val j) (s.val.length : Int)) ∧

      (∀ r' : List I64,
        1 ≤ r'.length →
        (∀ (i : Nat) (hi : i < r'.length), 1 ≤ (r'[i]'hi).val) →
        prefixSum r' r'.length = (s.val.length : Int) →
        (∀ (j : Nat), 0 < j → j < r'.length →
          IsCut s 0 (prefixSum r' j) (s.val.length : Int)) →
        r'.length ≤ r.val.length)) := by
  sorry

/-- The function returns a result r: for every s satisfying the preconditions the call fails neither by arithmetic overflow, nor by out-of-bounds access, nor by a panic.
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s). -/
theorem spec_2 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∃ r : alloc.vec.Vec I64, partition_labels s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∃ r : alloc.vec.Vec I64, partition_labels s = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r): 1 <= r[i] <= len(s).
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s). -/
theorem spec_3 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        1 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ (s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        1 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, the sum of all elements of r equals len(s).
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s). -/
theorem spec_4 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      total r.val = (s.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      total r.val = (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, 1 <= len(r) <= d, where d is the number of distinct byte values occurring among s[0], ..., s[len(s)-1]; consequently len(r) <= 26 and len(r) <= len(s).
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s). -/
theorem spec_5 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      1 ≤ r.val.length ∧ r.val.length ≤ distinctCount s ∧
      r.val.length ≤ 26 ∧ r.val.length ≤ s.val.length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      1 ≤ r.val.length ∧ r.val.length ≤ distinctCount s ∧
      r.val.length ≤ 26 ∧ r.val.length ≤ s.val.length) := by
  sorry

/-- Whenever the function returns a result r, with k = len(r), P(0) = 0 and P(j) = r[0] + ... + r[j-1]: for every pair of indices i, i' with 0 <= i < len(s), 0 <= i' < len(s) and s[i] = s[i'], there is no part boundary strictly separating them, i.e. no j with 0 < j < k satisfies min(i, i') < P(j) <= max(i, i').
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s). -/
theorem spec_6 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (i i' : Nat) (hi : i < s.val.length) (hi' : i' < s.val.length),
        ((s.val[i]'hi).val : Int) = ((s.val[i']'hi').val : Int) →
        ¬ ∃ (j : Nat), 0 < j ∧ j < r.val.length ∧
          (min i i' : Int) < prefixSum r.val j ∧ prefixSum r.val j ≤ (max i i' : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (i i' : Nat) (hi : i < s.val.length) (hi' : i' < s.val.length),
        ((s.val[i]'hi).val : Int) = ((s.val[i']'hi').val : Int) →
        ¬ ∃ (j : Nat), 0 < j ∧ j < r.val.length ∧
          (min i i' : Int) < prefixSum r.val j ∧ prefixSum r.val j ≤ (max i i' : Int)) := by
  sorry

/-- Whenever the function returns a result r, with k = len(r), P(0) = 0 and P(j) = r[0] + ... + r[j-1]: for every j with 0 <= j < k, setting a = P(j) and b = P(j+1), b is the least integer q with a < q <= len(s) such that no byte value c occurs at some index i with a <= i < q and also at some index i' with q <= i' < len(s).
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s). -/
theorem spec_7 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (j : Nat), j < r.val.length →

        prefixSum r.val j < prefixSum r.val (j + 1) ∧
        prefixSum r.val (j + 1) ≤ (s.val.length : Int) ∧
        IsCut s (prefixSum r.val j) (prefixSum r.val (j + 1)) (s.val.length : Int) ∧

        (∀ q : Int, prefixSum r.val j < q → q < prefixSum r.val (j + 1) →
          q ≤ (s.val.length : Int) → ¬ IsCut s (prefixSum r.val j) q (s.val.length : Int)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (j : Nat), j < r.val.length →

        prefixSum r.val j < prefixSum r.val (j + 1) ∧
        prefixSum r.val (j + 1) ≤ (s.val.length : Int) ∧
        IsCut s (prefixSum r.val j) (prefixSum r.val (j + 1)) (s.val.length : Int) ∧

        (∀ q : Int, prefixSum r.val j < q → q < prefixSum r.val (j + 1) →
          q ≤ (s.val.length : Int) → ¬ IsCut s (prefixSum r.val j) q (s.val.length : Int))) := by
  sorry

/-- Whenever the function returns a result r, with k = len(r), P(0) = 0 and P(j) = r[0] + ... + r[j-1]: for every p with 1 <= p < len(s), p = P(j) for some j with 0 < j < k if and only if no byte value c occurs both at an index i with 0 <= i < p and at an index i' with p <= i' < len(s).
  Preconditions: len(s) >= 1, len(s) <= 500, and 97 <= s[i] <= 122 for every i with 0 <= i < len(s). -/
theorem spec_8 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122) :
    ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (p : Nat), 1 ≤ p → p < s.val.length →
        ((∃ (j : Nat), 0 < j ∧ j < r.val.length ∧ prefixSum r.val j = (p : Int)) ↔
          IsCut s 0 (p : Int) (s.val.length : Int)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122), ∀ r : alloc.vec.Vec I64, partition_labels s = ok r →
      ∀ (p : Nat), 1 ≤ p → p < s.val.length →
        ((∃ (j : Nat), 0 < j ∧ j < r.val.length ∧ prefixSum r.val j = (p : Int)) ↔
          IsCut s 0 (p : Int) (s.val.length : Int))) := by
  sorry

/-- The function returns a result r with len(r) = 1 and r[0] = len(s).
  Preconditions: len(s) >= 1, len(s) <= 500, 97 <= s[i] <= 122 for every i with 0 <= i < len(s), and s[0] = s[len(s)-1]. -/
theorem spec_9 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (hfirst_last : ((s.val[0]'hlen_lo).val : Int) = ((s.val[s.val.length - 1]'(by omega)).val : Int)) :
    ∃ r : alloc.vec.Vec I64,
      partition_labels s = ok r ∧
      r.val.length = 1 ∧
      r.val.map (fun x => x.val) = [(s.val.length : Int)] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (hfirst_last : ((s.val[0]'hlen_lo).val : Int) = ((s.val[s.val.length - 1]'(by omega)).val : Int)), ∃ r : alloc.vec.Vec I64,
      partition_labels s = ok r ∧
      r.val.length = 1 ∧
      r.val.map (fun x => x.val) = [(s.val.length : Int)]) := by
  sorry

/-- The function returns a result r with len(r) = len(s) and r[i] = 1 for every i with 0 <= i < len(s).
  Preconditions: len(s) >= 1, len(s) <= 500, 97 <= s[i] <= 122 for every i with 0 <= i < len(s), and s[i] != s[j] for all 0 <= i < j < len(s) (all bytes of s are pairwise distinct). -/
theorem spec_10 (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (hdistinct : PairwiseDistinct s) :
    ∃ r : alloc.vec.Vec I64,
      partition_labels s = ok r ∧
      r.val.length = s.val.length ∧
      r.val.map (fun x => x.val) = List.replicate s.val.length 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500)
    (halpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (hdistinct : PairwiseDistinct s), ∃ r : alloc.vec.Vec I64,
      partition_labels s = ok r ∧
      r.val.length = s.val.length ∧
      r.val.map (fun x => x.val) = List.replicate s.val.length 1) := by
  sorry

/-- Whenever the function returns r on input s and r' on input t, len(r) = len(r') and r[i] = r'[i] for every i with 0 <= i < len(r).
  Preconditions: s and t are byte slices, each satisfying: length between 1 and 500 and all bytes in the range 97..122. Additionally len(s) = len(t) = n and, for all i, j with 0 <= i < n and 0 <= j < n, s[i] = s[j] if and only if t[i] = t[j]. -/
theorem spec_11 (s t : Slice U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 500)
    (hsalpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 500)
    (htalpha : ∀ (i : Nat) (hi : i < t.val.length),
      97 ≤ (t.val[i]'hi).val ∧ (t.val[i]'hi).val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hpattern : SameEqualityPattern s t) :
    ∀ (r r' : alloc.vec.Vec I64),
      partition_labels s = ok r → partition_labels t = ok r' →
      r.val.length = r'.val.length ∧
      (∀ (i : Nat) (hi : i < r.val.length) (hi' : i < r'.val.length),
        ((r.val[i]'hi).val : Int) = ((r'.val[i]'hi').val : Int)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 500)
    (hsalpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 500)
    (htalpha : ∀ (i : Nat) (hi : i < t.val.length),
      97 ≤ (t.val[i]'hi).val ∧ (t.val[i]'hi).val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hpattern : SameEqualityPattern s t), ∀ (r r' : alloc.vec.Vec I64),
      partition_labels s = ok r → partition_labels t = ok r' →
      r.val.length = r'.val.length ∧
      (∀ (i : Nat) (hi : i < r.val.length) (hi' : i < r'.val.length),
        ((r.val[i]'hi).val : Int) = ((r'.val[i]'hi').val : Int))) := by
  sorry

/-- Whenever the function returns r on input s and r' on input t, len(r') <= len(r) and r'[i] = r[i] for every i with 0 <= i < len(r').
  Preconditions: s is a byte slice with 1 <= len(s) <= 500 and all bytes in 97..122; t is a byte slice with len(t) = m where 1 <= m <= len(s), t[i] = s[i] for every 0 <= i < m, and no byte value c occurs both at some index i < m and at some index i' with m <= i' < len(s) (t is a letter-closed prefix of s). -/
theorem spec_12 (s t : Slice U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 500)
    (hsalpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ s.val.length)
    (hprefix : ∀ (i : Nat) (hi : i < t.val.length),
      ((t.val[i]'hi).val : Int) =
        ((s.val[i]'(Nat.lt_of_lt_of_le hi ht_hi)).val : Int))
    (hclosed : IsCut s 0 (t.val.length : Int) (s.val.length : Int)) :
    ∀ (r r' : alloc.vec.Vec I64),
      partition_labels s = ok r → partition_labels t = ok r' →
      r'.val.length ≤ r.val.length ∧
      (∀ (i : Nat) (hi' : i < r'.val.length) (hi : i < r.val.length),
        ((r'.val[i]'hi').val : Int) = ((r.val[i]'hi).val : Int)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 500)
    (hsalpha : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ s.val.length)
    (hprefix : ∀ (i : Nat) (hi : i < t.val.length),
      ((t.val[i]'hi).val : Int) =
        ((s.val[i]'(Nat.lt_of_lt_of_le hi ht_hi)).val : Int))
    (hclosed : IsCut s 0 (t.val.length : Int) (s.val.length : Int)), ∀ (r r' : alloc.vec.Vec I64),
      partition_labels s = ok r → partition_labels t = ok r' →
      r'.val.length ≤ r.val.length ∧
      (∀ (i : Nat) (hi' : i < r'.val.length) (hi : i < r.val.length),
        ((r'.val[i]'hi').val : Int) = ((r.val[i]'hi).val : Int))) := by
  sorry

end AegisSpec.PartitionLabels
