import Aegis.MaximumSetSize.Code.Funs

/-!
# Specifications of `Aegis.MaximumSetSize.maximum_set_size`

LeetCode problem `maximum-size-of-a-set-after-removals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumSetSize

  open Aegis.MaximumSetSize

  def values (s : Slice Std.I64) : List Int := s.val.map (fun x : Std.I64 => x.val)

  def distinctVals (s : Slice Std.I64) : Finset Int := (values s).toFinset

  def EntriesInRange (s : Slice Std.I64) : Prop :=
    ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000

  def valuesOutside (s : Slice Std.I64) (I : Finset Nat) : Finset Int :=
    ((s.val.zipIdx.filter (fun p : Std.I64 × Nat => p.2 ∉ I)).map
        (fun p : Std.I64 × Nat => p.1.val)).toFinset

  /-- Let k = n/2, D1 = { nums1[i] | 0 <= i < n }, and D2 = { nums2[i] | 0 <= i < n }. The function returns a result r and r = min(|D1 ∪ D2|, min(k, |D1|) + min(k, |D2|)).
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and 1 <= nums1[i] <= 1000000000 and 1 <= nums2[i] <= 1000000000 for every valid index i. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2) :
      ∃ r : Std.I64,
        maximum_set_size nums1 nums2 = ok r ∧
          r.val =
            Int.ofNat
              (min (distinctVals nums1 ∪ distinctVals nums2).card
                (min (nums1.val.length / 2) (distinctVals nums1).card +
                  min (nums1.val.length / 2) (distinctVals nums2).card)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2), ∃ r : Std.I64,
          maximum_set_size nums1 nums2 = ok r ∧
            r.val =
              Int.ofNat
                (min (distinctVals nums1 ∪ distinctVals nums2).card
                  (min (nums1.val.length / 2) (distinctVals nums1).card +
                    min (nums1.val.length / 2) (distinctVals nums2).card))) := by
    sorry

  /-- For every input satisfying the preconditions, maximum_set_size returns a result r; it never fails, overflows, panics, or accesses out of bounds.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and 1 <= nums1[i] <= 1000000000 and 1 <= nums2[i] <= 1000000000 for every valid index i. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2) :
      ∃ r : Std.I64, maximum_set_size nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2), ∃ r : Std.I64, maximum_set_size nums1 nums2 = ok r) := by
    sorry

  /-- Let n = len(nums1). Whenever maximum_set_size returns r, we have 1 <= r <= n.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r) :
      1 ≤ r.val ∧ r.val ≤ Int.ofNat nums1.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r), 1 ≤ r.val ∧ r.val ≤ Int.ofNat nums1.val.length) := by
    sorry

  /-- Let D1 = { nums1[i] | 0 <= i < n } and D2 = { nums2[i] | 0 <= i < n }. Whenever maximum_set_size returns r, we have r <= |D1 ∪ D2|.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r) :
      r.val ≤ Int.ofNat (distinctVals nums1 ∪ distinctVals nums2).card := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r), r.val ≤ Int.ofNat (distinctVals nums1 ∪ distinctVals nums2).card) := by
    sorry

  /-- Let k = n/2, D1 = { nums1[i] | 0 <= i < n }, and D2 = { nums2[i] | 0 <= i < n }. Whenever maximum_set_size returns r, we have r <= min(k, |D1|) + min(k, |D2|).
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r) :
      r.val ≤
        Int.ofNat
          (min (nums1.val.length / 2) (distinctVals nums1).card +
            min (nums1.val.length / 2) (distinctVals nums2).card) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r), r.val ≤
          Int.ofNat
            (min (nums1.val.length / 2) (distinctVals nums1).card +
              min (nums1.val.length / 2) (distinctVals nums2).card)) := by
    sorry

  /-- Let k = n/2, D1 = { nums1[i] | 0 <= i < n }, and D2 = { nums2[i] | 0 <= i < n }. Whenever maximum_set_size returns r, we have r >= max(min(k, |D1|), min(k, |D2|)).
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r) :
      Int.ofNat
          (max (min (nums1.val.length / 2) (distinctVals nums1).card)
            (min (nums1.val.length / 2) (distinctVals nums2).card)) ≤
        r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r), Int.ofNat
            (max (min (nums1.val.length / 2) (distinctVals nums1).card)
              (min (nums1.val.length / 2) (distinctVals nums2).card)) ≤
          r.val) := by
    sorry

  /-- Let D1 = { nums1[i] | 0 <= i < n } and D2 = { nums2[i] | 0 <= i < n }. Whenever maximum_set_size returns r, we have r >= |D1 ∩ D2|.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r) :
      Int.ofNat (distinctVals nums1 ∩ distinctVals nums2).card ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r), Int.ofNat (distinctVals nums1 ∩ distinctVals nums2).card ≤ r.val) := by
    sorry

  /-- Swapping the two input arrays does not change the answer: maximum_set_size(nums1, nums2) and maximum_set_size(nums2, nums1) return the same result.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2) :
      maximum_set_size nums2 nums1 = maximum_set_size nums1 nums2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2), maximum_set_size nums2 nums1 = maximum_set_size nums1 nums2) := by
    sorry

  /-- If nums1' is any permutation of nums1 and nums2' is any permutation of nums2, then maximum_set_size(nums1', nums2') returns the same result as maximum_set_size(nums1, nums2).
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_9 (nums1 nums2 nums1' nums2' : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (h_perm1 : List.Perm nums1'.val nums1.val)
      (h_perm2 : List.Perm nums2'.val nums2.val) :
      maximum_set_size nums1' nums2' = maximum_set_size nums1 nums2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (h_perm1 : List.Perm nums1'.val nums1.val)
        (h_perm2 : List.Perm nums2'.val nums2.val), maximum_set_size nums1' nums2' = maximum_set_size nums1 nums2) := by
    sorry

  /-- Whenever maximum_set_size returns r, there exist subsets I1 and I2 of {0, 1, ..., n-1}, each of size k = n/2, such that |{ nums1[i] | 0 <= i < n and i not in I1 } ∪ { nums2[i] | 0 <= i < n and i not in I2 }| = r.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_10 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r) :
      ∃ I1 I2 : Finset Nat,
        I1 ⊆ Finset.range nums1.val.length ∧
          I2 ⊆ Finset.range nums1.val.length ∧
            I1.card = nums1.val.length / 2 ∧
              I2.card = nums1.val.length / 2 ∧
                Int.ofNat (valuesOutside nums1 I1 ∪ valuesOutside nums2 I2).card =
                  r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r), ∃ I1 I2 : Finset Nat,
          I1 ⊆ Finset.range nums1.val.length ∧
            I2 ⊆ Finset.range nums1.val.length ∧
              I1.card = nums1.val.length / 2 ∧
                I2.card = nums1.val.length / 2 ∧
                  Int.ofNat (valuesOutside nums1 I1 ∪ valuesOutside nums2 I2).card =
                    r.val) := by
    sorry

  /-- Whenever maximum_set_size returns r, for every pair of subsets I1 and I2 of {0, 1, ..., n-1} with |I1| = |I2| = k = n/2, we have |{ nums1[i] | 0 <= i < n and i not in I1 } ∪ { nums2[i] | 0 <= i < n and i not in I2 }| <= r.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all array entries are between 1 and 1000000000. -/
  theorem spec_11 (nums1 nums2 : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r) :
      ∀ I1 I2 : Finset Nat,
        I1 ⊆ Finset.range nums1.val.length →
          I2 ⊆ Finset.range nums1.val.length →
            I1.card = nums1.val.length / 2 →
              I2.card = nums1.val.length / 2 →
                Int.ofNat (valuesOutside nums1 I1 ∪ valuesOutside nums2 I2).card ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (r : Std.I64) (h_ret : maximum_set_size nums1 nums2 = ok r), ∀ I1 I2 : Finset Nat,
          I1 ⊆ Finset.range nums1.val.length →
            I2 ⊆ Finset.range nums1.val.length →
              I1.card = nums1.val.length / 2 →
                I2.card = nums1.val.length / 2 →
                  Int.ofNat (valuesOutside nums1 I1 ∪ valuesOutside nums2 I2).card ≤ r.val) := by
    sorry

  /-- Then maximum_set_size(nums1', nums2') and maximum_set_size(nums1, nums2) return the same result; changing multiplicities without changing the two distinct-value sets does not change the answer.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all entries are between 1 and 1000000000. Let D1 = { nums1[i] | 0 <= i < n } and D2 = { nums2[i] | 0 <= i < n }. Let nums1' and nums2' be arrays of length n with entries in the same range and with distinct-value sets D1' = D1 and D2' = D2. -/
  theorem spec_12 (nums1 nums2 nums1' nums2' : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (h_len1' : nums1'.val.length = nums1.val.length)
      (h_len2' : nums2'.val.length = nums2.val.length)
      (h_in1' : EntriesInRange nums1')
      (h_in2' : EntriesInRange nums2')
      (h_D1 : distinctVals nums1' = distinctVals nums1)
      (h_D2 : distinctVals nums2' = distinctVals nums2) :
      maximum_set_size nums1' nums2' = maximum_set_size nums1 nums2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (h_len1' : nums1'.val.length = nums1.val.length)
        (h_len2' : nums2'.val.length = nums2.val.length)
        (h_in1' : EntriesInRange nums1')
        (h_in2' : EntriesInRange nums2')
        (h_D1 : distinctVals nums1' = distinctVals nums1)
        (h_D2 : distinctVals nums2' = distinctVals nums2), maximum_set_size nums1' nums2' = maximum_set_size nums1 nums2) := by
    sorry

  /-- If maximum_set_size(nums1, nums2) returns r and maximum_set_size(nums1', nums2') returns r', then r <= r'.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, n is even, 1 <= n <= 20000, and all entries are between 1 and 1000000000. Let D1, D2 be the distinct-value sets of nums1, nums2. Let nums1', nums2' be arrays of length n with entries in the same range and distinct-value sets D1', D2'. Assume D1 ⊆ D1' and D2 ⊆ D2'. -/
  theorem spec_13 (nums1 nums2 nums1' nums2' : Slice Std.I64)
      (h_len : nums2.val.length = nums1.val.length)
      (h_even : Even nums1.val.length)
      (h_pos : 1 ≤ nums1.val.length)
      (h_n : nums1.val.length ≤ 20000)
      (h_in1 : EntriesInRange nums1)
      (h_in2 : EntriesInRange nums2)
      (h_len1' : nums1'.val.length = nums1.val.length)
      (h_len2' : nums2'.val.length = nums2.val.length)
      (h_in1' : EntriesInRange nums1')
      (h_in2' : EntriesInRange nums2')
      (h_D1 : distinctVals nums1 ⊆ distinctVals nums1')
      (h_D2 : distinctVals nums2 ⊆ distinctVals nums2')
      (r r' : Std.I64)
      (h_ret : maximum_set_size nums1 nums2 = ok r)
      (h_ret' : maximum_set_size nums1' nums2' = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64)
        (h_len : nums2.val.length = nums1.val.length)
        (h_even : Even nums1.val.length)
        (h_pos : 1 ≤ nums1.val.length)
        (h_n : nums1.val.length ≤ 20000)
        (h_in1 : EntriesInRange nums1)
        (h_in2 : EntriesInRange nums2)
        (h_len1' : nums1'.val.length = nums1.val.length)
        (h_len2' : nums2'.val.length = nums2.val.length)
        (h_in1' : EntriesInRange nums1')
        (h_in2' : EntriesInRange nums2')
        (h_D1 : distinctVals nums1 ⊆ distinctVals nums1')
        (h_D2 : distinctVals nums2 ⊆ distinctVals nums2')
        (r r' : Std.I64)
        (h_ret : maximum_set_size nums1 nums2 = ok r)
        (h_ret' : maximum_set_size nums1' nums2' = ok r'), r.val ≤ r'.val) := by
    sorry

  end AegisSpec.MaximumSetSize
