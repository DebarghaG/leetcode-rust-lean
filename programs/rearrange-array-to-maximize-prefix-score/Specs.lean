import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `rearrange-array-to-maximize-prefix-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxScore

namespace AegisSpec.MaxScore

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def entry (nums : Slice Std.I64) (i : Fin nums.val.length) : ℤ := (nums.val.get i).val

def NonemptySlice (nums : Slice Std.I64) : Prop := 0 < nums.val.length

def LenBound (nums : Slice Std.I64) : Prop := nums.val.length ≤ 100000

def ValueBound (nums : Slice Std.I64) : Prop :=
  ∀ i : Fin nums.val.length, -1000000 ≤ entry nums i ∧ entry nums i ≤ 1000000

def posCount (nums : Slice Std.I64) : ℕ := (vals nums).countP (fun x => decide (0 < x))

def zeroCount (nums : Slice Std.I64) : ℕ := (vals nums).countP (fun x => decide (x = 0))

def posSum (nums : Slice Std.I64) : ℤ :=
  ((vals nums).filter (fun x => decide (0 < x))).sum

def totalSum (nums : Slice Std.I64) : ℤ := (vals nums).sum

def negAbsValues (nums : Slice Std.I64) : List ℤ :=
  ((vals nums).filter (fun x => decide (x < 0))).map (fun x => -x)

def sortedNegAbsValues (nums : Slice Std.I64) : List ℤ :=
  (negAbsValues nums).mergeSort (fun a b => decide (a ≤ b))

def kOf (S : ℤ) (b : List ℤ) : ℕ :=
  List.foldr Nat.max 0
    ((List.range (b.length + 1)).filter
      (fun k => decide (k = 0 ∨ (b.take k).sum < S)))

def prefixes (l : List ℤ) : List ℤ :=
  (List.range l.length).map (fun i => (l.take (i + 1)).sum)

def prefixPositiveCount (l : List ℤ) : ℕ :=
  (prefixes l).countP (fun x => decide (0 < x))

def permuted (nums : Slice Std.I64) (p : Equiv.Perm (Fin nums.val.length)) : List ℤ :=
  (List.finRange nums.val.length).map (fun i => entry nums (p i))

def sortedDesc (nums : Slice Std.I64) : List ℤ :=
  (vals nums).mergeSort (fun a b => decide (b ≤ a))

/-- Let P be the number of indices i with 0 <= i < len(nums) and nums[i] > 0. Let Z be the number of indices i with 0 <= i < len(nums) and nums[i] = 0. Let S be the sum of nums[i] over all i with nums[i] > 0. Let b be the list obtained by taking all values -nums[i] for indices with nums[i] < 0, then sorting them in nondecreasing order; write m = len(b). Let k be the largest integer with 0 <= k <= m such that either k = 0 or the sum over t = 0 to k-1 of b[t] is strictly less than S, where the sum is the empty sum 0 when k=0. Then max_score(nums) returns a result r and r = P + k + (if S > 0 then Z else 0).
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∃ r, max_score nums = ok r ∧
      r.val = (posCount nums : ℤ) + (kOf (posSum nums) (sortedNegAbsValues nums) : ℤ)
        + (if 0 < posSum nums then (zeroCount nums : ℤ) else 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∃ r, max_score nums = ok r ∧
      r.val = (posCount nums : ℤ) + (kOf (posSum nums) (sortedNegAbsValues nums) : ℤ)
        + (if 0 < posSum nums then (zeroCount nums : ℤ) else 0)) := by
  sorry

/-- For every input satisfying the constraints, max_score(nums) returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∃ r, max_score nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∃ r, max_score nums = ok r) := by
  sorry

/-- Whenever max_score(nums) returns a result r, we have 0 <= r <= len(nums).
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∀ r, max_score nums = ok r → 0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∀ r, max_score nums = ok r → 0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Let P be the number of indices i with 0 <= i < len(nums) and nums[i] > 0. Whenever max_score(nums) returns a result r, we have r >= P.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∀ r, max_score nums = ok r → (posCount nums : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∀ r, max_score nums = ok r → (posCount nums : ℤ) ≤ r.val) := by
  sorry

/-- Let P be the number of indices i with nums[i] > 0, let Z be the number of indices i with nums[i] = 0, and let S be the sum of all positive entries nums[i]. If S > 0, then whenever max_score(nums) returns a result r, we have r >= P + Z.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    0 < posSum nums →
      ∀ r, max_score nums = ok r → (posCount nums : ℤ) + (zeroCount nums : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), 0 < posSum nums →
      ∀ r, max_score nums = ok r → (posCount nums : ℤ) + (zeroCount nums : ℤ) ≤ r.val) := by
  sorry

/-- If nums[0] > 0, then max_score(nums) returns 1; if nums[0] <= 0, then max_score(nums) returns 0.
  Preconditions: nums is a nonempty slice of 64-bit integers satisfying the constraints, and len(nums) = 1. -/
theorem spec_6 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) (h1 : nums.val.length = 1) :
    (0 < entry nums ⟨0, by omega⟩ → max_score nums = ok 1#i64) ∧
      (entry nums ⟨0, by omega⟩ ≤ 0 → max_score nums = ok 0#i64) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) (h1 : nums.val.length = 1), (0 < entry nums ⟨0, by omega⟩ → max_score nums = ok 1#i64) ∧
      (entry nums ⟨0, by omega⟩ ≤ 0 → max_score nums = ok 0#i64)) := by
  sorry

/-- max_score(nums) returns a result r and r = 0.
  Preconditions: nums is a nonempty slice of 64-bit integers satisfying the constraints, and for every i with 0 <= i < len(nums), nums[i] <= 0. -/
theorem spec_7 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) (hnp : ∀ i : Fin nums.val.length, entry nums i ≤ 0) :
    ∃ r, max_score nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) (hnp : ∀ i : Fin nums.val.length, entry nums i ≤ 0), ∃ r, max_score nums = ok r ∧ r.val = 0) := by
  sorry

/-- Let T be the sum of all entries nums[i] for 0 <= i < len(nums). Then max_score(nums) returns a result r, and r = len(nums) if and only if T > 0.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_8 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∃ r, max_score nums = ok r ∧
      (r.val = (nums.val.length : ℤ) ↔ 0 < totalSum nums) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∃ r, max_score nums = ok r ∧
      (r.val = (nums.val.length : ℤ) ↔ 0 < totalSum nums)) := by
  sorry

/-- Let n = len(nums) and let r be the result of max_score(nums). There exists a bijection p from {0,1,...,n-1} to {0,1,...,n-1} such that the number of indices i with 0 <= i < n and the sum over j = 0 to i of nums[p(j)] > 0 is exactly r.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_9 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∀ r, max_score nums = ok r →
      ∃ p : Equiv.Perm (Fin nums.val.length),
        (prefixPositiveCount (permuted nums p) : ℤ) = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∀ r, max_score nums = ok r →
      ∃ p : Equiv.Perm (Fin nums.val.length),
        (prefixPositiveCount (permuted nums p) : ℤ) = r.val) := by
  sorry

/-- Let n = len(nums) and let r be the result of max_score(nums). For every bijection p from {0,1,...,n-1} to {0,1,...,n-1}, the number of indices i with 0 <= i < n and the sum over j = 0 to i of nums[p(j)] > 0 is at most r.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_10 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∀ r, max_score nums = ok r →
      ∀ p : Equiv.Perm (Fin nums.val.length),
        (prefixPositiveCount (permuted nums p) : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∀ r, max_score nums = ok r →
      ∀ p : Equiv.Perm (Fin nums.val.length),
        (prefixPositiveCount (permuted nums p) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever max_score(nums) returns r and max_score(nums2) returns r2, we have r = r2.
  Preconditions: nums and nums2 are nonempty slices of 64-bit integers satisfying the constraints, and nums2 is a permutation of nums: len(nums2) = len(nums) and there is a bijection p from {0,1,...,len(nums)-1} to {0,1,...,len(nums)-1} with nums2[i] = nums[p(i)] for all i. -/
theorem spec_11 (nums nums2 : Slice Std.I64)
    (hne : NonemptySlice nums) (hlen : LenBound nums) (hb : ValueBound nums)
    (hne2 : NonemptySlice nums2) (hlen2 : LenBound nums2) (hb2 : ValueBound nums2)
    (hperm : (vals nums2).Perm (vals nums)) :
    ∀ r r2, max_score nums = ok r → max_score nums2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64)
    (hne : NonemptySlice nums) (hlen : LenBound nums) (hb : ValueBound nums)
    (hne2 : NonemptySlice nums2) (hlen2 : LenBound nums2) (hb2 : ValueBound nums2)
    (hperm : (vals nums2).Perm (vals nums)), ∀ r r2, max_score nums = ok r → max_score nums2 = ok r2 → r.val = r2.val) := by
  sorry

/-- Let P be the number of positive entries of nums, Z the number of zero entries, S the sum of positive entries, and b the nondecreasing list of the absolute values of the negative entries of nums. Let k be the largest integer with 0 <= k <= len(b) such that either k = 0 or the sum of the first k entries of b is strictly less than S, with the empty sum equal to 0. Then whenever max_score(nums) returns a result r, r - P - (if S > 0 then Z else 0) = k.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_12 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∀ r, max_score nums = ok r →
      r.val - (posCount nums : ℤ)
          - (if 0 < posSum nums then (zeroCount nums : ℤ) else 0)
        = (kOf (posSum nums) (sortedNegAbsValues nums) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∀ r, max_score nums = ok r →
      r.val - (posCount nums : ℤ)
          - (if 0 < posSum nums then (zeroCount nums : ℤ) else 0)
        = (kOf (posSum nums) (sortedNegAbsValues nums) : ℤ)) := by
  sorry

/-- Let r be the result returned by max_score(nums) and r2 the result returned by max_score(nums2). Then r2 >= r + 1.
  Preconditions: nums and nums2 are nonempty slices of 64-bit integers satisfying the constraints. nums2 has length len(nums)+1, its multiset of entries is the multiset of nums together with one additional integer c, and c > 0. -/
theorem spec_13 (nums nums2 : Slice Std.I64)
    (hne : NonemptySlice nums) (hlen : LenBound nums) (hb : ValueBound nums)
    (hne2 : NonemptySlice nums2) (hlen2 : LenBound nums2) (hb2 : ValueBound nums2)
    (hlen2' : nums2.val.length = nums.val.length + 1)
    (hmult : ∃ c : ℤ, 0 < c ∧ (vals nums2).Perm (c :: vals nums)) :
    ∀ r r2, max_score nums = ok r → max_score nums2 = ok r2 → r.val + 1 ≤ r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64)
    (hne : NonemptySlice nums) (hlen : LenBound nums) (hb : ValueBound nums)
    (hne2 : NonemptySlice nums2) (hlen2 : LenBound nums2) (hb2 : ValueBound nums2)
    (hlen2' : nums2.val.length = nums.val.length + 1)
    (hmult : ∃ c : ℤ, 0 < c ∧ (vals nums2).Perm (c :: vals nums)), ∀ r r2, max_score nums = ok r → max_score nums2 = ok r2 → r.val + 1 ≤ r2.val) := by
  sorry

/-- Let T be the sum of all entries of nums. If T <= 0, then whenever max_score(nums) returns r, r <= len(nums) - 1.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_14 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    totalSum nums ≤ 0 →
      ∀ r, max_score nums = ok r → r.val ≤ (nums.val.length : ℤ) - 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), totalSum nums ≤ 0 →
      ∀ r, max_score nums = ok r → r.val ≤ (nums.val.length : ℤ) - 1) := by
  sorry

/-- Let a be the list obtained by sorting the entries of nums in nonincreasing order, and let pref[i] = sum_{j=0}^i a[j] for 0 <= i < len(nums). Then max_score(nums) returns a result r, and r is the number of indices i with 0 <= i < len(nums) and pref[i] > 0.
  Preconditions: nums is a nonempty slice of 64-bit integers, 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000. -/
theorem spec_15 (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums) :
    ∃ r, max_score nums = ok r ∧
      r.val = (prefixPositiveCount (sortedDesc nums) : ℤ) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (hne : NonemptySlice nums) (hlen : LenBound nums)
    (hb : ValueBound nums), ∃ r, max_score nums = ok r ∧
      r.val = (prefixPositiveCount (sortedDesc nums) : ℤ)) := by
  sorry

end AegisSpec.MaxScore
