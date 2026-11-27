import Aegis.ArithmeticTriplets.Code.Funs

/-!
# Specifications of `Aegis.ArithmeticTriplets.arithmetic_triplets`

LeetCode problem `number-of-arithmetic-triplets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ArithmeticTriplets (arithmetic_triplets)

namespace AegisSpec.ArithmeticTriplets

def vals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def AllBetween (l : List Int) (lo hi : Int) : Prop := ∀ i : Fin l.length, lo ≤ l[i] ∧ l[i] ≤ hi

def StrictIncr (l : List Int) : Prop := ∀ i j : Fin l.length, i < j → l[i] < l[j]

def headVal (l : List Int) : Int := l.headD 0

def lastVal (l : List Int) : Int := l.getLastD 0

def tripleCount (l : List Int) (d : Int) : Nat :=
  ((Finset.univ : Finset (Fin l.length × Fin l.length × Fin l.length)).filter
    (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      l[p.2.1] - l[p.1] = d ∧ l[p.2.2] - l[p.2.1] = d)).card

def startCount (l : List Int) (d : Int) : Nat :=
  ((Finset.univ : Finset (Fin l.length)).filter
    (fun i => l[i] + d ∈ l ∧ l[i] + 2 * d ∈ l)).card

def IsMid (l : List Int) (d : Int) (j : Fin l.length) : Prop :=
  (∃ i : Fin l.length, i < j ∧ l[j] - l[i] = d) ∧
    (∃ k : Fin l.length, j < k ∧ l[k] - l[j] = d)

instance instDecidableIsMid (l : List Int) (d : Int) (j : Fin l.length) :
    Decidable (IsMid l d j) :=
  inferInstanceAs (Decidable ((∃ i : Fin l.length, i < j ∧ l[j] - l[i] = d) ∧
    (∃ k : Fin l.length, j < k ∧ l[k] - l[j] = d)))

def midCount (l : List Int) (d : Int) : Nat :=
  ((Finset.univ : Finset (Fin l.length)).filter
    (fun j => 1 ≤ j.val ∧ j.val < l.length - 1 ∧ IsMid l d j)).card

def Embeds (l₁ l₂ : List Int) : Prop :=
  ∃ f : Fin l₁.length → Fin l₂.length,
    (∀ i j : Fin l₁.length, i < j → f i < f j) ∧
      ∀ i : Fin l₁.length, l₂[f i] = l₁[i]

/-- The function returns a result r (it does not fail), and r, interpreted as a mathematical integer, is exactly the number of index triples (i,j,k) such that 0 <= i < j < k < len(nums), nums[j] - nums[i] = diff, and nums[k] - nums[j] = diff. Distinct index triples are counted separately, so each such (i,j,k) contributes 1 to r.
  Preconditions: len(nums) is an integer with 3 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 200; 1 <= diff <= 50; and for every i, j with 0 <= i < j < len(nums), nums[i] < nums[j]. -/
theorem spec_1 (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)) :
    ∃ r : Std.I64,
      arithmetic_triplets nums diff = ok r ∧ r.val = (tripleCount (vals nums) diff.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)), ∃ r : Std.I64,
      arithmetic_triplets nums diff = ok r ∧ r.val = (tripleCount (vals nums) diff.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as a mathematical integer, r <= len(nums) - 2.
  Preconditions: len(nums) is an integer with 3 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 200; 1 <= diff <= 50; and nums is strictly increasing. -/
theorem spec_2 (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)) :
    ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r → r.val ≤ ((vals nums).length : Int) - 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)), ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r → r.val ≤ ((vals nums).length : Int) - 2) := by
  sorry

/-- Whenever the function returns a result r, r is equal to the number of indices i with 0 <= i < len(nums) for which both values nums[i] + diff and nums[i] + 2*diff occur as elements of nums. Equivalently, for such an i there exist p, q with 0 <= i < p < q < len(nums), nums[p] = nums[i] + diff, and nums[q] = nums[i] + 2*diff.
  Preconditions: len(nums) is an integer with 3 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 200; 1 <= diff <= 50; and nums is strictly increasing. -/
theorem spec_3 (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)) :
    ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r → r.val = (startCount (vals nums) diff.val : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)), ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r → r.val = (startCount (vals nums) diff.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, if nums[len(nums)-1] - nums[0] < 2*diff, then r = 0.
  Preconditions: len(nums) is an integer with 3 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 200; 1 <= diff <= 50; and nums is strictly increasing. -/
theorem spec_4 (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)) :
    ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r →
        lastVal (vals nums) - headVal (vals nums) < 2 * diff.val → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)), ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r →
        lastVal (vals nums) - headVal (vals nums) < 2 * diff.val → r.val = 0) := by
  sorry

/-- The function returns a result r on (nums, diff) and a result r2 on (nums2, diff), and r = r2.
  Preconditions: nums and diff satisfy the constraints of spec_1: 3 <= len(nums) <= 200, every nums[i] satisfies 0 <= nums[i] <= 200, 1 <= diff <= 50, and nums is strictly increasing. Let c be an integer and let nums2 be a slice of the same length such that nums2[i] = nums[i] + c for every i and 0 <= nums2[i] <= 200 for every i. -/
theorem spec_5 (nums nums2 : Slice Std.I64) (diff : Std.I64) (c : Int)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums))
    (hshift : vals nums2 = (vals nums).map (fun v => v + c))
    (hbounds2 : AllBetween (vals nums2) 0 200) :
    ∃ r r2 : Std.I64,
      arithmetic_triplets nums diff = ok r ∧
        arithmetic_triplets nums2 diff = ok r2 ∧ r.val = r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (diff : Std.I64) (c : Int)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums))
    (hshift : vals nums2 = (vals nums).map (fun v => v + c))
    (hbounds2 : AllBetween (vals nums2) 0 200), ∃ r r2 : Std.I64,
      arithmetic_triplets nums diff = ok r ∧
        arithmetic_triplets nums2 diff = ok r2 ∧ r.val = r2.val) := by
  sorry

/-- The function returns a result r on (nums, diff) and a result r2 on (nums2, diff2), and r = r2.
  Preconditions: nums and diff satisfy the constraints of spec_1: 3 <= len(nums) <= 200, every nums[i] satisfies 0 <= nums[i] <= 200, 1 <= diff <= 50, and nums is strictly increasing. Let k be a positive integer, let nums2[i] = k * nums[i] for every i, and let diff2 = k * diff. Assume nums2 satisfies 0 <= nums2[i] <= 200 for every i and that 1 <= diff2 <= 50. -/
theorem spec_6 (nums nums2 : Slice Std.I64) (diff diff2 : Std.I64) (k : Int)
    (hk : 0 < k)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums))
    (hscale : vals nums2 = (vals nums).map (fun v => k * v))
    (hdiff2 : diff2.val = k * diff.val)
    (hbounds2 : AllBetween (vals nums2) 0 200)
    (hdiff2_range : 1 ≤ diff2.val ∧ diff2.val ≤ 50) :
    ∃ r r2 : Std.I64,
      arithmetic_triplets nums diff = ok r ∧
        arithmetic_triplets nums2 diff2 = ok r2 ∧ r.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (diff diff2 : Std.I64) (k : Int)
    (hk : 0 < k)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums))
    (hscale : vals nums2 = (vals nums).map (fun v => k * v))
    (hdiff2 : diff2.val = k * diff.val)
    (hbounds2 : AllBetween (vals nums2) 0 200)
    (hdiff2_range : 1 ≤ diff2.val ∧ diff2.val ≤ 50), ∃ r r2 : Std.I64,
      arithmetic_triplets nums diff = ok r ∧
        arithmetic_triplets nums2 diff2 = ok r2 ∧ r.val = r2.val) := by
  sorry

/-- The function returns a result r on (nums, diff) and a result r2 on (nums2, diff), and r <= r2.
  Preconditions: nums and nums2 are slices satisfying the constraints of spec_1 with the same diff: 3 <= len <= 200 for each, all elements are between 0 and 200, 1 <= diff <= 50, and each slice is strictly increasing. In addition, nums is a subsequence of nums2: there are indices f(0) < f(1) < ... < f(len(nums)-1) < len(nums2) with nums2[f(i)] = nums[i] for every 0 <= i < len(nums). -/
theorem spec_7 (nums nums2 : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums))
    (hlen2 : 3 ≤ (vals nums2).length ∧ (vals nums2).length ≤ 200)
    (hbounds2 : AllBetween (vals nums2) 0 200)
    (hsorted2 : StrictIncr (vals nums2))
    (hsub : Embeds (vals nums) (vals nums2)) :
    ∃ r r2 : Std.I64,
      arithmetic_triplets nums diff = ok r ∧
        arithmetic_triplets nums2 diff = ok r2 ∧ r.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums))
    (hlen2 : 3 ≤ (vals nums2).length ∧ (vals nums2).length ≤ 200)
    (hbounds2 : AllBetween (vals nums2) 0 200)
    (hsorted2 : StrictIncr (vals nums2))
    (hsub : Embeds (vals nums) (vals nums2)), ∃ r r2 : Std.I64,
      arithmetic_triplets nums diff = ok r ∧
        arithmetic_triplets nums2 diff = ok r2 ∧ r.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns a result r, for each j with 1 <= j < len(nums)-1 let b(j) = 1 if there exists i with 0 <= i < j and nums[j] - nums[i] = diff and there exists k with j < k < len(nums) and nums[k] - nums[j] = diff, and let b(j) = 0 otherwise. Then r = b(1) + b(2) + ... + b(len(nums)-2).
  Preconditions: len(nums) is an integer with 3 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 200; 1 <= diff <= 50; and nums is strictly increasing. -/
theorem spec_8 (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)) :
    ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r → r.val = (midCount (vals nums) diff.val : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (diff : Std.I64)
    (hlen : 3 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (hbounds : AllBetween (vals nums) 0 200)
    (hdiff : 1 ≤ diff.val ∧ diff.val ≤ 50)
    (hsorted : StrictIncr (vals nums)), ∀ r : Std.I64,
      arithmetic_triplets nums diff = ok r → r.val = (midCount (vals nums) diff.val : Int)) := by
  sorry

end AegisSpec.ArithmeticTriplets
