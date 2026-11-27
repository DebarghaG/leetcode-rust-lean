import Aegis.CountSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountSubarrays.count_subarrays`

LeetCode problem `count-subarrays-with-fixed-bounds`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSubarrays

noncomputable section

open Classical

open Aegis.CountSubarrays (count_subarrays)

def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def nlen (nums : Slice I64) : Nat := (vals nums).length

def nth (a : List Int) (i : Nat) : Int := (a[i]?).getD 0

def seg (a : List Int) (l r : Nat) : List Int := (a.drop l).take (r + 1 - l)

def segMin (a : List Int) (l r : Nat) : Int :=
  match seg a l r with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => min acc y) x

def segMax (a : List Int) (l r : Nat) : Int :=
  match seg a l r with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => max acc y) x

def subMin (nums : Slice I64) (l r : Nat) : Int := segMin (vals nums) l r

def subMax (nums : Slice I64) (l r : Nat) : Int := segMax (vals nums) l r

def countPairs (lo hi : Nat) (p : Nat → Nat → Prop) : Nat :=
  ((List.range hi).product (List.range hi)).countP
    (fun q => decide (lo ≤ q.1 ∧ q.1 ≤ q.2 ∧ p q.1 q.2))

def countExactBetween (nums : Slice I64) (minK maxK : I64) (lo hi : Nat) : Nat :=
  countPairs lo hi (fun l r => subMin nums l r = minK.val ∧ subMax nums l r = maxK.val)

def countExact (nums : Slice I64) (minK maxK : I64) : Nat :=
  countExactBetween nums minK maxK 0 (nlen nums)

def inBounds (nums : Slice I64) (minK maxK : I64) (l r : Nat) : Prop :=
  ∀ i, l ≤ i → i ≤ r → minK.val ≤ nth (vals nums) i ∧ nth (vals nums) i ≤ maxK.val

def countInBounds (nums : Slice I64) (minK maxK : I64) : Nat :=
  countPairs 0 (nlen nums) (inBounds nums minK maxK)

def allEq (nums : Slice I64) (v : Int) (l r : Nat) : Prop :=
  ∀ i, l ≤ i → i ≤ r → nth (vals nums) i = v

def countAllEq (nums : Slice I64) (v : Int) : Nat :=
  countPairs 0 (nlen nums) (allEq nums v)

def hasVal (nums : Slice I64) (v : Int) (l r : Nat) : Prop :=
  ∃ i, l ≤ i ∧ i ≤ r ∧ nth (vals nums) i = v

def ValidSeg (nums : Slice I64) (minK maxK : I64) (s e : Nat) : Prop :=
  s ≤ e ∧ e < nlen nums ∧ inBounds nums minK maxK s e

def MaximalSeg (nums : Slice I64) (minK maxK : I64) (s e : Nat) : Prop :=
  ValidSeg nums minK maxK s e ∧
  (∀ s', s' ≤ s → ValidSeg nums minK maxK s' e → s' = s) ∧
  (∀ e', e ≤ e' → ValidSeg nums minK maxK s e' → e' = e)

def maximalSegs (nums : Slice I64) (minK maxK : I64) : List (Nat × Nat) :=
  ((List.range (nlen nums)).product (List.range (nlen nums))).filter
    (fun q => decide (MaximalSeg nums minK maxK q.1 q.2))

def maximalSegTotal (nums : Slice I64) (minK maxK : I64) : Nat :=
  ((maximalSegs nums minK maxK).map
    (fun q => countExactBetween nums minK maxK q.1 (q.2 + 1))).sum

/-- Let n = len(nums). For 0 <= l <= r < n define mn(l,r) = min{nums[i] | l <= i <= r} and mx(l,r) = max{nums[i] | l <= i <= r}. Let F be the number of pairs (l,r) with 0 <= l <= r < n such that mn(l,r) = minK and mx(l,r) = maxK. Whenever count_subarrays(nums, minK, maxK) returns a result r, the integer r is equal to F.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_1 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = (countExact nums minK maxK : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000), ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = (countExact nums minK maxK : Int)) := by
  sorry

/-- For every nums, minK, and maxK satisfying the preconditions, count_subarrays(nums, minK, maxK) returns a result r (it does not fail, panic, overflow, or index outside the slice).
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_2 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000) :
    ∃ r : I64, count_subarrays nums minK maxK = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000), ∃ r : I64, count_subarrays nums minK maxK = ok r) := by
  sorry

/-- Whenever count_subarrays(nums, minK, maxK) returns a result r, we have 0 <= r.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_3 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000), ∀ r : I64, count_subarrays nums minK maxK = ok r → 0 ≤ r.val) := by
  sorry

/-- Let n = len(nums). Whenever count_subarrays(nums, minK, maxK) returns a result r, we have r <= n*(n+1)/2, the total number of non-empty contiguous subarrays of nums.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_4 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val ≤ ((nlen nums * (nlen nums + 1) / 2 : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000), ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val ≤ ((nlen nums * (nlen nums + 1) / 2 : Nat) : Int)) := by
  sorry

/-- Let n = len(nums). Let C be the number of pairs (l,r) with 0 <= l <= r < n such that for every i with l <= i <= r, minK <= nums[i] <= maxK. Whenever count_subarrays(nums, minK, maxK) returns a result r, we have r <= C.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_5 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val ≤ (countInBounds nums minK maxK : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000), ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val ≤ (countInBounds nums minK maxK : Int)) := by
  sorry

/-- If minK > maxK, then whenever count_subarrays(nums, minK, maxK) returns a result r, we have r = 0.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_6 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hlt : maxK.val < minK.val) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hlt : maxK.val < minK.val), ∀ r : I64, count_subarrays nums minK maxK = ok r → r.val = 0) := by
  sorry

/-- If either there is no index i with 0 <= i < len(nums) and nums[i] = minK, or there is no index i with 0 <= i < len(nums) and nums[i] = maxK, then whenever count_subarrays(nums, minK, maxK) returns a result r, we have r = 0.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_7 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hmiss : (∀ i, i < nlen nums → nth (vals nums) i ≠ minK.val) ∨
      (∀ i, i < nlen nums → nth (vals nums) i ≠ maxK.val)) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hmiss : (∀ i, i < nlen nums → nth (vals nums) i ≠ minK.val) ∨
      (∀ i, i < nlen nums → nth (vals nums) i ≠ maxK.val)), ∀ r : I64, count_subarrays nums minK maxK = ok r → r.val = 0) := by
  sorry

/-- Assume minK = maxK, and let v = minK. Whenever count_subarrays(nums, minK, maxK) returns a result r, r is equal to the number of pairs (l,r) with 0 <= l <= r < len(nums) such that nums[i] = v for every i with l <= i <= r.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_8 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (heq : minK.val = maxK.val) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = (countAllEq nums minK.val : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (heq : minK.val = maxK.val), ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = (countAllEq nums minK.val : Int)) := by
  sorry

/-- Assume minK <= maxK, every element nums[i] satisfies minK <= nums[i] <= maxK, and there exist indices i and j with nums[i] = minK and nums[j] = maxK. Whenever count_subarrays(nums, minK, maxK) returns a result r, we have r >= 1.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_9 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hle : minK.val ≤ maxK.val)
    (hin : ∀ x ∈ vals nums, minK.val ≤ x ∧ x ≤ maxK.val)
    (hocc_min : ∃ i, i < nlen nums ∧ nth (vals nums) i = minK.val)
    (hocc_max : ∃ j, j < nlen nums ∧ nth (vals nums) j = maxK.val) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r → 1 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hle : minK.val ≤ maxK.val)
    (hin : ∀ x ∈ vals nums, minK.val ≤ x ∧ x ≤ maxK.val)
    (hocc_min : ∃ i, i < nlen nums ∧ nth (vals nums) i = minK.val)
    (hocc_max : ∃ j, j < nlen nums ∧ nth (vals nums) j = maxK.val), ∀ r : I64, count_subarrays nums minK maxK = ok r → 1 ≤ r.val) := by
  sorry

/-- Assume minK != maxK. Let n = len(nums). Whenever count_subarrays(nums, minK, maxK) returns a result r, we have r <= n*(n-1)/2.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_10 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hne : minK.val ≠ maxK.val) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val ≤ ((nlen nums * (nlen nums - 1) / 2 : Nat) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hne : minK.val ≠ maxK.val), ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val ≤ ((nlen nums * (nlen nums - 1) / 2 : Nat) : Int)) := by
  sorry

/-- Let rev be the array of length len(nums) with rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Whenever count_subarrays(nums, minK, maxK) returns a result r, and count_subarrays(rev, minK, maxK) returns a result r', we have r = r'.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_11 (nums rev : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hrev : vals rev = (vals nums).reverse) :
    ∀ r r' : I64, count_subarrays nums minK maxK = ok r →
      count_subarrays rev minK maxK = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums rev : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hrev : vals rev = (vals nums).reverse), ∀ r r' : I64, count_subarrays nums minK maxK = ok r →
      count_subarrays rev minK maxK = ok r' → r.val = r'.val) := by
  sorry

/-- Let c be any integer such that for every i with 0 <= i < len(nums), 1 <= nums[i] + c <= 1000000, and also 1 <= minK + c <= 1000000 and 1 <= maxK + c <= 1000000. Define nums2 by nums2[i] = nums[i] + c for all i. Whenever count_subarrays(nums, minK, maxK) returns a result r, and count_subarrays(nums2, minK + c, maxK + c) returns a result r', we have r = r'.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_12 (nums nums2 : Slice I64) (minK maxK minK2 maxK2 : I64) (c : Int)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hshift : ∀ x ∈ vals nums, 1 ≤ x + c ∧ x + c ≤ 1000000)
    (hminK_shift : 1 ≤ minK.val + c ∧ minK.val + c ≤ 1000000)
    (hmaxK_shift : 1 ≤ maxK.val + c ∧ maxK.val + c ≤ 1000000)
    (hnums2 : vals nums2 = (vals nums).map (fun x => x + c))
    (hminK2 : minK2.val = minK.val + c) (hmaxK2 : maxK2.val = maxK.val + c) :
    ∀ r r' : I64, count_subarrays nums minK maxK = ok r →
      count_subarrays nums2 minK2 maxK2 = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums2 : Slice I64) (minK maxK minK2 maxK2 : I64) (c : Int)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hshift : ∀ x ∈ vals nums, 1 ≤ x + c ∧ x + c ≤ 1000000)
    (hminK_shift : 1 ≤ minK.val + c ∧ minK.val + c ≤ 1000000)
    (hmaxK_shift : 1 ≤ maxK.val + c ∧ maxK.val + c ≤ 1000000)
    (hnums2 : vals nums2 = (vals nums).map (fun x => x + c))
    (hminK2 : minK2.val = minK.val + c) (hmaxK2 : maxK2.val = maxK.val + c), ∀ r r' : I64, count_subarrays nums minK maxK = ok r →
      count_subarrays nums2 minK2 maxK2 = ok r' → r.val = r'.val) := by
  sorry

/-- Let n = len(nums). Fix an index s with 0 <= s < n such that nums[s] < minK or nums[s] > maxK. Let L be the number of pairs (l,r) with 0 <= l <= r < s such that min{nums[i] | l <= i <= r} = minK and max{nums[i] | l <= i <= r} = maxK. Let R be the number of pairs (u,v) with s+1 <= u <= v < n such that min{nums[i] | u <= i <= v} = minK and max{nums[i] | u <= i <= v} = maxK. Whenever count_subarrays(nums, minK, maxK) returns a result r, we have r = L + R.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_13 (nums : Slice I64) (minK maxK : I64) (s : Nat)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hs : s < nlen nums)
    (hsbad : nth (vals nums) s < minK.val ∨ maxK.val < nth (vals nums) s) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = ((countExactBetween nums minK maxK 0 s +
        countExactBetween nums minK maxK (s + 1) (nlen nums) : Nat) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64) (s : Nat)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000)
    (hs : s < nlen nums)
    (hsbad : nth (vals nums) s < minK.val ∨ maxK.val < nth (vals nums) s), ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = ((countExactBetween nums minK maxK 0 s +
        countExactBetween nums minK maxK (s + 1) (nlen nums) : Nat) : Int)) := by
  sorry

/-- Let n = len(nums). Call an interval [a,b] with 0 <= a <= b < n a maximal valid segment if minK <= nums[i] <= maxK for every i with a <= i <= b, and the interval cannot be extended left or right while keeping this property. Whenever count_subarrays(nums, minK, maxK) returns a result r, r is equal to the sum over all maximal valid segments [a,b] of the number of pairs (l,r) with a <= l <= r <= b such that min{nums[i] | l <= i <= r} = minK and max{nums[i] | l <= i <= r} = maxK.
  Preconditions: nums is a slice of I64 with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= minK <= 1000000; 1 <= maxK <= 1000000. -/
theorem spec_14 (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000) :
    ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = (maximalSegTotal nums minK maxK : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (minK maxK : I64)
    (hlen_lower : 2 ≤ nlen nums) (hlen_upper : nlen nums ≤ 100000)
    (hentries : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hminK : 1 ≤ minK.val ∧ minK.val ≤ 1000000)
    (hmaxK : 1 ≤ maxK.val ∧ maxK.val ≤ 1000000), ∀ r : I64, count_subarrays nums minK maxK = ok r →
      r.val = (maximalSegTotal nums minK maxK : Int)) := by
  sorry

end

end AegisSpec.CountSubarrays
