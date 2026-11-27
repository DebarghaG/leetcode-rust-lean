import Aegis.SubarraysWithMoreZerosThanOnes.Code.Funs

/-!
# Specifications of `Aegis.SubarraysWithMoreZerosThanOnes.subarrays_with_more_zeros_than_ones`

LeetCode problem `count-subarrays-with-more-ones-than-zeros`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubarraysWithMoreZerosThanOnes

open Aegis.SubarraysWithMoreZerosThanOnes

def elemVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def valAt (nums : Slice Std.I64) (i : Nat) : Int := (elemVals nums).getD i 0

def AllBits (nums : Slice Std.I64) : Prop :=
  ∀ i, i < nums.val.length → valAt nums i = 0 ∨ valAt nums i = 1

noncomputable def ones (nums : Slice Std.I64) (l r : Nat) : Nat :=
  ((Finset.Icc l r).filter (fun i => valAt nums i = 1)).card

noncomputable def zeros (nums : Slice Std.I64) (l r : Nat) : Nat :=
  ((Finset.Icc l r).filter (fun i => valAt nums i = 0)).card

@[reducible] def HasMoreOnes (nums : Slice Std.I64) (l r : Nat) : Prop :=
  ones nums l r > zeros nums l r

@[reducible] def Balanced (nums : Slice Std.I64) (l r : Nat) : Prop :=
  ones nums l r = zeros nums l r

noncomputable def countMoreOnes (nums : Slice Std.I64) : Nat :=
  (Finset.range nums.val.length).sum
    (fun l => ((Finset.Icc l (nums.val.length - 1)).filter
      (fun r => HasMoreOnes nums l r)).card)

noncomputable def countUnbalanced (nums : Slice Std.I64) : Nat :=
  (Finset.range nums.val.length).sum
    (fun l => ((Finset.Icc l (nums.val.length - 1)).filter
      (fun r => ¬ Balanced nums l r)).card)

def IsModRepInt (C : Int) (r : Std.I64) : Prop :=
  0 ≤ r.val ∧ r.val < 1000000007 ∧ Int.ModEq 1000000007 C r.val

def IsModRep (C : Nat) (r : Std.I64) : Prop := IsModRepInt (C : Int) r

/-- For 0 <= l <= r < len(nums), let ones(l,r) be the number of i with l <= i <= r and nums[i] = 1, and let zeros(l,r) be the number of i with l <= i <= r and nums[i] = 0. Let C be the number of pairs (l,r) with 0 <= l <= r < len(nums) such that ones(l,r) > zeros(l,r). Whenever the function returns a result r, r is the unique integer in the range 0 <= r < 1000000007 that is congruent to C modulo 1000000007.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → IsModRep (countMoreOnes nums) r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → IsModRep (countMoreOnes nums) r) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result and does not fail.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums) :
    ∃ r : Std.I64, subarrays_with_more_zeros_than_ones nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums), ∃ r : Std.I64, subarrays_with_more_zeros_than_ones nums = ok r) := by
  sorry

/-- Let C be the number of pairs (l,r) with 0 <= l <= r < len(nums) such that the contiguous subarray nums[l], nums[l+1], ..., nums[r] has more 1 entries than 0 entries. Whenever the function returns a result r, 0 <= r <= C.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (countMoreOnes nums : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (countMoreOnes nums : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = nums[0].
  Preconditions: len(nums) = 1, and nums[0] is either 0 or 1. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : nums.val.length = 1) (hbit : valAt nums 0 = 0 ∨ valAt nums 0 = 1) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = valAt nums 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 1) (hbit : valAt nums 0 = 0 ∨ valAt nums 0 = 1), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = valAt nums 0) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] = 0. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hzero : ∀ i, i < nums.val.length → valAt nums i = 0) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hzero : ∀ i, i < nums.val.length → valAt nums i = 0), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = 0) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, r is the unique integer in the range 0 <= r < 1000000007 that is congruent to n*(n+1)/2 modulo 1000000007.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] = 1. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hone : ∀ i, i < nums.val.length → valAt nums i = 1) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      IsModRepInt (((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2) r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hone : ∀ i, i < nums.val.length → valAt nums i = 1), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      IsModRepInt (((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2) r) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: len(nums) is between 1 and 100000 inclusive, nums contains only 0s and 1s, and there is exactly one index i with 0 <= i < len(nums) and nums[i] = 1. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums)
    (hunique : ∃ i, i < nums.val.length ∧ valAt nums i = 1 ∧
      ∀ j, j < nums.val.length → valAt nums j = 1 → j = i) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums)
    (hunique : ∃ i, i < nums.val.length ∧ valAt nums i = 1 ∧
      ∀ j, j < nums.val.length → valAt nums j = 1 → j = i), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = 1) := by
  sorry

/-- Let rev be the slice of length len(nums) defined by rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Whenever the function returns r on nums and r_rev on rev, r = r_rev.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_8 (nums rev : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums)
    (hrevLen : rev.val.length = nums.val.length)
    (hrev : ∀ i, i < rev.val.length → valAt rev i = valAt nums (nums.val.length - 1 - i)) :
    ∀ r rrev : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      subarrays_with_more_zeros_than_ones rev = ok rrev → r.val = rrev.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums)
    (hrevLen : rev.val.length = nums.val.length)
    (hrev : ∀ i, i < rev.val.length → valAt rev i = valAt nums (nums.val.length - 1 - i)), ∀ r rrev : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      subarrays_with_more_zeros_than_ones rev = ok rrev → r.val = rrev.val) := by
  sorry

/-- Let C be the number of pairs (l,r) with 0 <= l <= r < len(nums) such that the contiguous subarray nums[l], nums[l+1], ..., nums[r] has more 1 entries than 0 entries. Whenever the function returns a result r, r = C.
  Preconditions: len(nums) is between 1 and 44720 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 44720)
    (hbits : AllBits nums) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = (countMoreOnes nums : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 44720)
    (hbits : AllBits nums), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = (countMoreOnes nums : Int)) := by
  sorry

/-- Whenever the function returns a result r with r != 0, there exists at least one pair (l,rr) with 0 <= l <= rr < len(nums) such that the contiguous subarray nums[l], nums[l+1], ..., nums[rr] has more 1 entries than 0 entries.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val ≠ 0 →
      ∃ l rr, l ≤ rr ∧ rr < nums.val.length ∧ HasMoreOnes nums l rr := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val ≠ 0 →
      ∃ l rr, l ≤ rr ∧ rr < nums.val.length ∧ HasMoreOnes nums l rr) := by
  sorry

/-- If the function returns a result r with r = 0, then there is no pair (l,rr) with 0 <= l <= rr < len(nums) such that the contiguous subarray nums[l], nums[l+1], ..., nums[rr] has more 1 entries than 0 entries.
  Preconditions: len(nums) is between 1 and 44720 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 44720)
    (hbits : AllBits nums) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = 0 →
      ¬ ∃ l rr, l ≤ rr ∧ rr < nums.val.length ∧ HasMoreOnes nums l rr := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 44720)
    (hbits : AllBits nums), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val = 0 →
      ¬ ∃ l rr, l ≤ rr ∧ rr < nums.val.length ∧ HasMoreOnes nums l rr) := by
  sorry

/-- Whenever the function returns a result r, r > 0.
  Preconditions: len(nums) is between 1 and 44720 inclusive, for every i with 0 <= i < len(nums), nums[i] is either 0 or 1, and there exists an index i with 0 <= i < len(nums) and nums[i] = 1. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 44720)
    (hbits : AllBits nums)
    (hone : ∃ i, i < nums.val.length ∧ valAt nums i = 1) :
    ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val > 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 44720)
    (hbits : AllBits nums)
    (hone : ∃ i, i < nums.val.length ∧ valAt nums i = 1), ∀ r : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r → r.val > 0) := by
  sorry

/-- Let comp be the slice of length len(nums) defined by comp[i] = 1 - nums[i] for 0 <= i < len(nums). Let D be the number of pairs (l,r) with 0 <= l <= r < len(nums) such that the contiguous subarray nums[l], nums[l+1], ..., nums[r] does not have equal numbers of 1s and 0s. Whenever the function returns r on nums and r_comp on comp, r + r_comp is congruent to D modulo 1000000007.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_13 (nums comp : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums)
    (hcompLen : comp.val.length = nums.val.length)
    (hcomp : ∀ i, i < comp.val.length → valAt comp i = 1 - valAt nums i) :
    ∀ r rcomp : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      subarrays_with_more_zeros_than_ones comp = ok rcomp →
      Int.ModEq 1000000007 (countUnbalanced nums : Int) (r.val + rcomp.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums comp : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbits : AllBits nums)
    (hcompLen : comp.val.length = nums.val.length)
    (hcomp : ∀ i, i < comp.val.length → valAt comp i = 1 - valAt nums i), ∀ r rcomp : Std.I64,
      subarrays_with_more_zeros_than_ones nums = ok r →
      subarrays_with_more_zeros_than_ones comp = ok rcomp →
      Int.ModEq 1000000007 (countUnbalanced nums : Int) (r.val + rcomp.val)) := by
  sorry

end AegisSpec.SubarraysWithMoreZerosThanOnes
