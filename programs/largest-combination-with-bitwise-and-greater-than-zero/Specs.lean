import Aegis.LargestCombination.Code.Funs

/-!
# Specifications of `Aegis.LargestCombination.largest_combination`

LeetCode problem `largest-combination-with-bitwise-and-greater-than-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LargestCombination (largest_combination)

  namespace AegisSpec.LargestCombination

  def iand (a b : ℤ) : ℤ := ((a.toNat &&& b.toNat : ℕ) : ℤ)

  def iandList : List ℤ → ℤ
    | [] => -1
    | v :: vs => vs.foldl (fun a w => iand a w) v

  def valAt (candidates : Slice Std.I64) (i : ℕ) : ℤ := (candidates.val.getD i 0#i64).val

  def andOf (candidates : Slice Std.I64) (S : Finset ℕ) : ℤ :=
    iandList ((List.range candidates.val.length).filter (fun i => i ∈ S) |>.map
      (fun i => valAt candidates i))

  def IndicesBelow (candidates : Slice Std.I64) (S : Finset ℕ) : Prop :=
    ∀ i ∈ S, i < candidates.val.length

  def IsIndexSet (candidates : Slice Std.I64) (S : Finset ℕ) : Prop :=
    S.Nonempty ∧ IndicesBelow candidates S

  def bitIdx (candidates : Slice Std.I64) (b : ℕ) : Finset ℕ :=
    (Finset.range candidates.val.length).filter
      (fun i => iand (valAt candidates i) (2 ^ b) = 2 ^ b)

  def bitCount (candidates : Slice Std.I64) (b : ℕ) : ℕ := (bitIdx candidates b).card

  def maxBitCount (candidates : Slice Std.I64) : ℕ :=
    (Finset.range 63).sup (fun b => bitCount candidates b)

  def countOcc (l : List Std.I64) (v : ℤ) : ℕ := (l.filter (fun x => x.val = v)).length

  def IsPermutation (d candidates : Slice Std.I64) : Prop :=
    d.val.length = candidates.val.length ∧
      ∀ v : ℤ, countOcc d.val v = countOcc candidates.val v

  def IsSubsequence (d candidates : Slice Std.I64) : Prop := d.val.Sublist candidates.val

  /-- Whenever largest_combination(candidates) returns a result r, r is the maximum size of a non-empty set S of indices with 0 <= i < len(candidates) such that the bitwise AND of the values {candidates[i] | i in S} is greater than 0. Equivalently, both: (1) there is a non-empty index set S with |S| = r and the bitwise AND of {candidates[i] | i in S} > 0; and (2) for every non-empty index set T with 0 <= i < len(candidates) for all i in T, if the bitwise AND of {candidates[i] | i in T} > 0 then |T| <= r. An index set uses each index at most once; its indices need not be contiguous; equal values at different indices are distinct elements.
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_1 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      (∃ S : Finset ℕ, IsIndexSet candidates S ∧ (S.card : ℤ) = r.val ∧ 0 < andOf candidates S) ∧
        (∀ S : Finset ℕ, IsIndexSet candidates S → 0 < andOf candidates S → (S.card : ℤ) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), (∃ S : Finset ℕ, IsIndexSet candidates S ∧ (S.card : ℤ) = r.val ∧ 0 < andOf candidates S) ∧
          (∀ S : Finset ℕ, IsIndexSet candidates S → 0 < andOf candidates S → (S.card : ℤ) ≤ r.val)) := by
    sorry

  /-- largest_combination(candidates) returns a result r; it does not fail, panic, go out of bounds, or overflow.
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_2 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647) :
      ∃ r : Std.I64, largest_combination candidates = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647), ∃ r : Std.I64, largest_combination candidates = ok r) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, 1 <= r <= len(candidates).
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_3 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      1 ≤ r.val ∧ r.val ≤ (candidates.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), 1 ≤ r.val ∧ r.val ≤ (candidates.val.length : ℤ)) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, there exists a non-empty set S of indices with 0 <= i < len(candidates) such that |S| = r and the bitwise AND of {candidates[i] | i in S} is greater than 0.
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_4 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      ∃ S : Finset ℕ, IsIndexSet candidates S ∧ (S.card : ℤ) = r.val ∧ 0 < andOf candidates S := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), ∃ S : Finset ℕ, IsIndexSet candidates S ∧ (S.card : ℤ) = r.val ∧ 0 < andOf candidates S) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, for every non-empty set S of indices with 0 <= i < len(candidates), if the bitwise AND of {candidates[i] | i in S} is greater than 0, then |S| <= r.
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_5 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      ∀ S : Finset ℕ, IsIndexSet candidates S → 0 < andOf candidates S → (S.card : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), ∀ S : Finset ℕ, IsIndexSet candidates S → 0 < andOf candidates S → (S.card : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, r = max { c_b | 0 <= b < 63 }, where c_b is the number of indices i with 0 <= i < len(candidates) whose b-th bit (the bit of weight 2^b) is 1 in candidates[i].
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_6 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      r.val = (maxBitCount candidates : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), r.val = (maxBitCount candidates : ℤ)) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, r = len(candidates) if and only if the bitwise AND of all elements of candidates is greater than 0.
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_7 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      (r.val = (candidates.val.length : ℤ) ↔
        0 < andOf candidates (Finset.range candidates.val.length)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), (r.val = (candidates.val.length : ℤ) ↔
          0 < andOf candidates (Finset.range candidates.val.length))) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r and largest_combination(d) returns a result r', we have r = r'.
    Preconditions: candidates and d are slices of 64-bit integers, each with 1 <= length <= 100000 and all elements between 1 and 2147483647; d is a permutation of candidates (same length, and for every integer v the number of occurrences of v in d equals the number of occurrences of v in candidates). -/
  theorem spec_8 (candidates d : Slice Std.I64)
      (hlenc_lo : 1 ≤ candidates.val.length) (hlenc_hi : candidates.val.length ≤ 100000)
      (hvalc : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (hlend_lo : 1 ≤ d.val.length) (hlend_hi : d.val.length ≤ 100000)
      (hvald : ∀ i, i < d.val.length → 1 ≤ valAt d i ∧ valAt d i ≤ 2147483647)
      (hperm : IsPermutation d candidates)
      (r : Std.I64) (hr : largest_combination candidates = ok r)
      (r' : Std.I64) (hr' : largest_combination d = ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (candidates d : Slice Std.I64)
        (hlenc_lo : 1 ≤ candidates.val.length) (hlenc_hi : candidates.val.length ≤ 100000)
        (hvalc : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (hlend_lo : 1 ≤ d.val.length) (hlend_hi : d.val.length ≤ 100000)
        (hvald : ∀ i, i < d.val.length → 1 ≤ valAt d i ∧ valAt d i ≤ 2147483647)
        (hperm : IsPermutation d candidates)
        (r : Std.I64) (hr : largest_combination candidates = ok r)
        (r' : Std.I64) (hr' : largest_combination d = ok r'), r = r') := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r and largest_combination(d) returns a result r', we have r' <= r.
    Preconditions: candidates and d are slices of 64-bit integers, each with 1 <= length <= 100000 and all elements between 1 and 2147483647; d is obtained from candidates by deleting zero or more elements (so d is a subsequence of candidates, preserving order). -/
  theorem spec_9 (candidates d : Slice Std.I64)
      (hlenc_lo : 1 ≤ candidates.val.length) (hlenc_hi : candidates.val.length ≤ 100000)
      (hvalc : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (hlend_lo : 1 ≤ d.val.length) (hlend_hi : d.val.length ≤ 100000)
      (hvald : ∀ i, i < d.val.length → 1 ≤ valAt d i ∧ valAt d i ≤ 2147483647)
      (hsub : IsSubsequence d candidates)
      (r : Std.I64) (hr : largest_combination candidates = ok r)
      (r' : Std.I64) (hr' : largest_combination d = ok r') :
      r'.val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (candidates d : Slice Std.I64)
        (hlenc_lo : 1 ≤ candidates.val.length) (hlenc_hi : candidates.val.length ≤ 100000)
        (hvalc : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (hlend_lo : 1 ≤ d.val.length) (hlend_hi : d.val.length ≤ 100000)
        (hvald : ∀ i, i < d.val.length → 1 ≤ valAt d i ∧ valAt d i ≤ 2147483647)
        (hsub : IsSubsequence d candidates)
        (r : Std.I64) (hr : largest_combination candidates = ok r)
        (r' : Std.I64) (hr' : largest_combination d = ok r'), r'.val ≤ r.val) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, r = 1 if and only if for every pair of distinct indices i and j with 0 <= i < j < len(candidates), the bitwise AND of candidates[i] and candidates[j] is equal to 0.
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_10 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      (r.val = 1 ↔ ∀ i j : ℕ, i < j → j < candidates.val.length →
        iand (valAt candidates i) (valAt candidates j) = 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), (r.val = 1 ↔ ∀ i j : ℕ, i < j → j < candidates.val.length →
          iand (valAt candidates i) (valAt candidates j) = 0)) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, for every bit position b with 0 <= b < 63, the number of indices i with 0 <= i < len(candidates) whose b-th bit is 1 in candidates[i] is at most r.
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_11 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      ∀ b : ℕ, b < 63 → (bitCount candidates b : ℤ) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), ∀ b : ℕ, b < 63 → (bitCount candidates b : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever largest_combination(candidates) returns a result r, there exists a bit position b with 0 <= b < 63 such that exactly r indices i with 0 <= i < len(candidates) have the b-th bit set to 1 in candidates[i].
    Preconditions: candidates is a slice of 64-bit integers with 1 <= len(candidates) <= 100000 and, for every i with 0 <= i < len(candidates), 1 <= candidates[i] <= 2147483647. -/
  theorem spec_12 (candidates : Slice Std.I64)
      (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
      (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
      (r : Std.I64) (hr : largest_combination candidates = ok r) :
      ∃ b : ℕ, b < 63 ∧ (bitCount candidates b : ℤ) = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (candidates : Slice Std.I64)
        (hlen_lo : 1 ≤ candidates.val.length) (hlen_hi : candidates.val.length ≤ 100000)
        (hval : ∀ i, i < candidates.val.length → 1 ≤ valAt candidates i ∧ valAt candidates i ≤ 2147483647)
        (r : Std.I64) (hr : largest_combination candidates = ok r), ∃ b : ℕ, b < 63 ∧ (bitCount candidates b : ℤ) = r.val) := by
    sorry

  end AegisSpec.LargestCombination
