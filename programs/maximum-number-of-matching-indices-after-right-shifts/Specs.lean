import Aegis.MaximumMatchingIndices.Code.Funs

/-!
# Specifications of `Aegis.MaximumMatchingIndices.maximum_matching_indices`

LeetCode problem `maximum-number-of-matching-indices-after-right-shifts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumMatchingIndices

def getI (s : Slice Std.I64) (i : ℕ) : ℤ :=
  match s.val[i]? with
  | some x => x.val
  | none => 0

def modIdx (n k j : ℕ) : ℕ := (j + n - k) % n

def matchCount (nums1 nums2 : Slice Std.I64) (k : ℕ) : ℕ :=
  ((Finset.range nums1.val.length).filter
      (fun j => getI nums1 (modIdx nums1.val.length k j) = getI nums2 j)).card

def maxMatchCount (nums1 nums2 : Slice Std.I64) : ℕ :=
  (Finset.range nums1.val.length).sup (fun k => matchCount nums1 nums2 k)

def OccursIn (s : Slice Std.I64) (v : ℤ) : Prop :=
  ∃ i, i < s.val.length ∧ getI s i = v

def values (s : Slice Std.I64) : Finset ℤ :=
  (Finset.range s.val.length).image (fun i => getI s i)

/-- The function returns a result r and r equals the maximum, over all integers k with 0 <= k < n, of C(k), where C(k) is the number of indices j with 0 <= j < n such that nums1[(j - k) mod n] = nums2[j], and x mod n denotes the unique integer in [0,n) congruent to x modulo n.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and for every i with 0 <= i < n, nums1[i] > 0 and nums2[i] > 0. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i) :
    ∃ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r ∧
        r.val = (maxMatchCount nums1 nums2 : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i), ∃ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r ∧
        r.val = (maxMatchCount nums1 nums2 : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and for every i with 0 <= i < n, nums1[i] > 0 and nums2[i] > 0. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i) :
    ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums1.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i), ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums1.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if nums1[0] = nums2[0], and r = 0 otherwise.
  Preconditions: len(nums1) = len(nums2) = 1, nums1[0] > 0, and nums2[0] > 0. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (h1 : nums1.val.length = 1) (h2 : nums2.val.length = 1)
    (hpos1 : 0 < getI nums1 0) (hpos2 : 0 < getI nums2 0) :
    ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        r.val = if getI nums1 0 = getI nums2 0 then 1 else 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : nums1.val.length = 1) (h2 : nums2.val.length = 1)
    (hpos1 : 0 < getI nums1 0) (hpos2 : 0 < getI nums2 0), ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        r.val = if getI nums1 0 = getI nums2 0 then 1 else 0) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k < n, the number of indices j with 0 <= j < n such that nums1[(j - k) mod n] = nums2[j] is at most r, where x mod n denotes the unique integer in [0,n) congruent to x modulo n.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and for every i with 0 <= i < n, nums1[i] > 0 and nums2[i] > 0. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i) :
    ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        ∀ k : ℕ, k < nums1.val.length → (matchCount nums1 nums2 k : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i), ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        ∀ k : ℕ, k < nums1.val.length → (matchCount nums1 nums2 k : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k with 0 <= k < n such that r equals the number of indices j with 0 <= j < n for which nums1[(j - k) mod n] = nums2[j], where x mod n denotes the unique integer in [0,n) congruent to x modulo n.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and for every i with 0 <= i < n, nums1[i] > 0 and nums2[i] > 0. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i) :
    ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        ∃ k : ℕ, k < nums1.val.length ∧ r.val = (matchCount nums1 nums2 k : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i), ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        ∃ k : ℕ, k < nums1.val.length ∧ r.val = (matchCount nums1 nums2 k : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, all entries of nums1 and nums2 are positive, and for every i and j with 0 <= i < n and 0 <= j < n, nums1[i] != nums2[j]. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (hdisj : ∀ i, i < nums1.val.length → ∀ j, j < nums1.val.length →
      getI nums1 i ≠ getI nums2 j) :
    ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (hdisj : ∀ i, i < nums1.val.length → ∀ j, j < nums1.val.length →
      getI nums1 i ≠ getI nums2 j), ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r → r.val = 0) := by
  sorry

/-- Whenever the function called with arguments nums1 and nums2 returns r, and the function called with arguments nums2 and nums1 returns r', we have r = r'.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and for every i with 0 <= i < n, nums1[i] > 0 and nums2[i] > 0. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i) :
    ∀ r r' : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        Aegis.MaximumMatchingIndices.maximum_matching_indices nums2 nums1 = ok r' →
          r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i), ∀ r r' : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        Aegis.MaximumMatchingIndices.maximum_matching_indices nums2 nums1 = ok r' →
          r = r') := by
  sorry

/-- Whenever the function called with arguments nums1 and nums2 returns r, and the function called with arguments nums1' and nums2 returns r', we have r = r'.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and all entries of nums1 and nums2 are positive. Let t be an integer with 0 <= t < n, and let nums1' be the length-n array defined by nums1'[j] = nums1[(j - t) mod n] for every 0 <= j < n, where x mod n denotes the unique integer in [0,n) congruent to x modulo n. -/
theorem spec_8 (nums1 nums2 nums1' : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hlen' : nums1'.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (t : ℕ) (ht : t < nums1.val.length)
    (hrot : ∀ j, j < nums1.val.length →
      getI nums1' j = getI nums1 (modIdx nums1.val.length t j)) :
    ∀ r r' : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        Aegis.MaximumMatchingIndices.maximum_matching_indices nums1' nums2 = ok r' →
          r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 nums1' : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hlen' : nums1'.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (t : ℕ) (ht : t < nums1.val.length)
    (hrot : ∀ j, j < nums1.val.length →
      getI nums1' j = getI nums1 (modIdx nums1.val.length t j)), ∀ r r' : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        Aegis.MaximumMatchingIndices.maximum_matching_indices nums1' nums2 = ok r' →
          r = r') := by
  sorry

/-- Whenever the function called with arguments nums1 and nums2 returns r, and the function called with arguments nums1 and nums2' returns r', we have r = r'.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and all entries of nums1 and nums2 are positive. Let t be an integer with 0 <= t < n, and let nums2' be the length-n array defined by nums2'[j] = nums2[(j - t) mod n] for every 0 <= j < n, where x mod n denotes the unique integer in [0,n) congruent to x modulo n. -/
theorem spec_9 (nums1 nums2 nums2' : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hlen' : nums2'.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (t : ℕ) (ht : t < nums1.val.length)
    (hrot : ∀ j, j < nums1.val.length →
      getI nums2' j = getI nums2 (modIdx nums1.val.length t j)) :
    ∀ r r' : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2' = ok r' →
          r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 nums2' : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hlen' : nums2'.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (t : ℕ) (ht : t < nums1.val.length)
    (hrot : ∀ j, j < nums1.val.length →
      getI nums2' j = getI nums2 (modIdx nums1.val.length t j)), ∀ r r' : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2' = ok r' →
          r = r') := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if there exists an integer k with 0 <= k < n such that for every j with 0 <= j < n, nums1[(j - k) mod n] = nums2[j], where x mod n denotes the unique integer in [0,n) congruent to x modulo n.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and for every i with 0 <= i < n, nums1[i] > 0 and nums2[i] > 0. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i) :
    ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        (r.val = (nums1.val.length : ℤ) ↔
          ∃ k : ℕ, k < nums1.val.length ∧
            ∀ j : ℕ, j < nums1.val.length →
              getI nums1 (modIdx nums1.val.length k j) = getI nums2 j) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i), ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        (r.val = (nums1.val.length : ℤ) ↔
          ∃ k : ℕ, k < nums1.val.length ∧
            ∀ j : ℕ, j < nums1.val.length →
              getI nums1 (modIdx nums1.val.length k j) = getI nums2 j)) := by
  sorry

/-- Whenever the function returns a result r, r is at most the cardinality of the set of integers v for which v occurs in nums1 and v occurs in nums2; that is, r <= |{v : (there exists i with 0 <= i < n and nums1[i] = v) and (there exists j with 0 <= j < n and nums2[j] = v)}|.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, all entries of nums1 and nums2 are positive, and the values nums1[0], ..., nums1[n-1] are pairwise distinct. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (hdistinct : ∀ i, i < nums1.val.length → ∀ j, j < nums1.val.length →
      getI nums1 i = getI nums1 j → i = j) :
    ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        r.val ≤ ((values nums1 ∩ values nums2).card : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i)
    (hdistinct : ∀ i, i < nums1.val.length → ∀ j, j < nums1.val.length →
      getI nums1 i = getI nums1 j → i = j), ∀ r : Std.I64,
      Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r →
        r.val ≤ ((values nums1 ∩ values nums2).card : ℤ)) := by
  sorry

/-- For every nums1 and nums2 satisfying the preconditions, the function returns some result r; it does not fail with overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums1). len(nums2) = n, 1 <= n <= 3000, and for every i with 0 <= i < n, nums1[i] > 0 and nums2[i] > 0. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i) :
    ∃ r : Std.I64, Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : nums2.val.length = nums1.val.length)
    (hn : 1 ≤ nums1.val.length) (hnle : nums1.val.length ≤ 3000)
    (hpos1 : ∀ i, i < nums1.val.length → 0 < getI nums1 i)
    (hpos2 : ∀ i, i < nums1.val.length → 0 < getI nums2 i), ∃ r : Std.I64, Aegis.MaximumMatchingIndices.maximum_matching_indices nums1 nums2 = ok r) := by
  sorry

end AegisSpec.MaximumMatchingIndices
