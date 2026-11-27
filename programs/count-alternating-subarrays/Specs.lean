import Aegis.CountAlternatingSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountAlternatingSubarrays.count_alternating_subarrays`

LeetCode problem `count-alternating-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountAlternatingSubarrays

open Aeneas Aeneas.Std Result

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def get (a : List Int) (i : Nat) : Int := (a[i]?).getD 0

def IsAlternatingBetween (a : List Int) (l u : Nat) : Prop :=
  ∀ k, l ≤ k → k < u → get a k ≠ get a (k + 1)

def IsAlternatingSubarray (a : List Int) (l u : Nat) : Prop :=
  l ≤ u ∧ u < a.length ∧ IsAlternatingBetween a l u

def isAlternatingSubarrayB (a : List Int) (l u : Nat) : Bool :=
  decide (l ≤ u ∧ u < a.length) &&
    (List.range (u - l)).all (fun j => get a (l + j) != get a (l + j + 1))

def countAlternatingPairs (a : List Int) : Nat :=
  ((List.range a.length).product (List.range a.length)).countP
    (fun p => isAlternatingSubarrayB a p.1 p.2)

def tri (m : Nat) : Nat := m * (m + 1) / 2

def rev (a : List Int) : List Int :=
  (List.range a.length).map (fun i => get a (a.length - 1 - i))

def comp (a : List Int) : List Int := a.map (fun x => 1 - x)

def countChanges (a : List Int) : Nat :=
  (List.range (a.length - 1)).countP (fun k => get a k != get a (k + 1))

def IsCut (a : List Int) (k : Nat) : Prop := k + 1 < a.length ∧ get a k = get a (k + 1)

def IsCutPartition (a : List Int) (segs : List (Nat × Nat)) : Prop :=
  segs ≠ [] ∧
  (∀ p ∈ segs, p.1 ≤ p.2 ∧ p.2 < a.length) ∧
  (∃ e, segs.head? = some (0, e)) ∧
  (∃ s, segs.getLast? = some (s, a.length - 1)) ∧
  (∀ j, j + 1 < segs.length →
      ∃ s e s' e', segs[j]? = some (s, e) ∧ segs[j+1]? = some (s', e') ∧ s' = e + 1) ∧
  (∀ p ∈ segs, IsAlternatingBetween a p.1 p.2) ∧
  (∀ j, j + 1 < segs.length → ∃ s e, segs[j]? = some (s, e) ∧ IsCut a e)

def AdmissibleRun (a : List Int) (l m : Nat) : Prop :=
  1 ≤ m ∧ m ≤ a.length - l ∧ IsAlternatingBetween a l (l + m - 1)

def IsMaxRun (a : List Int) (l m : Nat) : Prop :=
  AdmissibleRun a l m ∧ ∀ m', AdmissibleRun a l m' → m' ≤ m

/-- The function returns a result r, and r equals the number of integer pairs (l, u) with 0 <= l <= u < len(nums) such that the subarray nums[l..u] is alternating: for every k with l <= k < u, nums[k] != nums[k+1]. Here nums[l..u] is the nonempty contiguous subarray from index l through index u inclusive.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((countAlternatingPairs (vals nums) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((countAlternatingPairs (vals nums) : Nat) : Int)) := by
  sorry

/-- The function returns a result r; it does not fail because of panic, out-of-bounds indexing, or arithmetic overflow.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64, Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64, Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r) := by
  sorry

/-- The function returns a result r, and r >= len(nums).
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ((vals nums).length : Int) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ((vals nums).length : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r <= len(nums)*(len(nums)+1)/2.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val ≤ ((tri (vals nums).length : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val ≤ ((tri (vals nums).length : Nat) : Int)) := by
  sorry

/-- The function returns a result r. If nums[0] != nums[1], then r = 3; otherwise nums[0] = nums[1] and r = 2.
  Preconditions: 1 <= len(nums) <= 100000, len(nums) = 2, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_len2 : (vals nums).length = 2)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      (get (vals nums) 0 ≠ get (vals nums) 1 → r.val = 3) ∧
      (get (vals nums) 0 = get (vals nums) 1 → r.val = 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_len2 : (vals nums).length = 2)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      (get (vals nums) 0 ≠ get (vals nums) 1 → r.val = 3) ∧
      (get (vals nums) 0 = get (vals nums) 1 → r.val = 2)) := by
  sorry

/-- The function returns a result r, and r = len(nums)*(len(nums)+1)/2.
  Preconditions: 1 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), nums[i] is either 0 or 1, and for every k with 0 <= k < len(nums)-1, nums[k] != nums[k+1]. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1)
    (h_alt : IsAlternatingBetween (vals nums) 0 ((vals nums).length - 1)) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((tri (vals nums).length : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1)
    (h_alt : IsAlternatingBetween (vals nums) 0 ((vals nums).length - 1)), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((tri (vals nums).length : Nat) : Int)) := by
  sorry

/-- The function returns a result r, and r = len(nums).
  Preconditions: 1 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), nums[i] is either 0 or 1, and for every i with 0 <= i < len(nums), nums[i] = nums[0]. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1)
    (h_const : ∀ i, i < (vals nums).length → get (vals nums) i = get (vals nums) 0) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((vals nums).length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1)
    (h_const : ∀ i, i < (vals nums).length → get (vals nums) i = get (vals nums) 0), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((vals nums).length : Int)) := by
  sorry

/-- Let rev be the array of length len(nums) with rev[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). The function returns a result r, and r equals the number of integer pairs (l, u) with 0 <= l <= u < len(nums) such that for every k with l <= k < u, rev[k] != rev[k+1].
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((countAlternatingPairs (rev (vals nums)) : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((countAlternatingPairs (rev (vals nums)) : Nat) : Int)) := by
  sorry

/-- Let comp be the array of length len(nums) with comp[i] = 1 - nums[i] for every i with 0 <= i < len(nums). The function returns a result r, and r equals the number of integer pairs (l, u) with 0 <= l <= u < len(nums) such that for every k with l <= k < u, comp[k] != comp[k+1].
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((countAlternatingPairs (comp (vals nums)) : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      r.val = ((countAlternatingPairs (comp (vals nums)) : Nat) : Int)) := by
  sorry

/-- Let the cut indices be exactly those k with 0 <= k < len(nums)-1 and nums[k] = nums[k+1]. These cuts partition the index range 0..len(nums)-1 into consecutive maximal intervals [a_1,b_1], ..., [a_m,b_m] with 0 = a_1, b_m = len(nums)-1, a_{j+1} = b_j+1, and with nums[k] != nums[k+1] for every j and every k with a_j <= k < b_j. The function returns a result r, and r = sum over j from 1 to m of (b_j - a_j + 1)*(b_j - a_j + 2)/2.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_10 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ∃ segs : List (Nat × Nat),
        IsCutPartition (vals nums) segs ∧
        r.val = (((segs.map (fun p => tri (p.2 - p.1 + 1))).sum : Nat) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ∃ segs : List (Nat × Nat),
        IsCutPartition (vals nums) segs ∧
        r.val = (((segs.map (fun p => tri (p.2 - p.1 + 1))).sum : Nat) : Int)) := by
  sorry

/-- For each l with 0 <= l < len(nums), let f(l) be the largest integer m with 1 <= m <= len(nums)-l such that for every k with l <= k < l+m-1, nums[k] != nums[k+1]. The function returns a result r, and r = sum from l=0 to len(nums)-1 of f(l).
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_11 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ∃ fl : Nat → Nat,
        (∀ l, l < (vals nums).length → IsMaxRun (vals nums) l (fl l)) ∧
        r.val = ((((List.range (vals nums).length).map fl).sum : Nat) : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ∃ fl : Nat → Nat,
        (∀ l, l < (vals nums).length → IsMaxRun (vals nums) l (fl l)) ∧
        r.val = ((((List.range (vals nums).length).map fl).sum : Nat) : Int)) := by
  sorry

/-- The function returns a result r, and r > len(nums) if and only if there exists an index k with 0 <= k < len(nums)-1 and nums[k] != nums[k+1].
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_12 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      (r.val > ((vals nums).length : Int) ↔
        ∃ k, k + 1 < (vals nums).length ∧ get (vals nums) k ≠ get (vals nums) (k + 1)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      (r.val > ((vals nums).length : Int) ↔
        ∃ k, k + 1 < (vals nums).length ∧ get (vals nums) k ≠ get (vals nums) (k + 1))) := by
  sorry

/-- Let t be the number of indices k with 0 <= k < len(nums)-1 and nums[k] != nums[k+1]. The function returns a result r, and r >= len(nums) + t.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
theorem spec_13 (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1) :
    ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ((vals nums).length : Int) + ((countChanges (vals nums) : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ (vals nums).length) (h_len_ub : (vals nums).length ≤ 100000)
    (h_bin : ∀ i, i < (vals nums).length → get (vals nums) i = 0 ∨ get (vals nums) i = 1), ∃ r : Std.I64,
      Aegis.CountAlternatingSubarrays.count_alternating_subarrays nums = ok r ∧
      ((vals nums).length : Int) + ((countChanges (vals nums) : Nat) : Int) ≤ r.val) := by
  sorry

end AegisSpec.CountAlternatingSubarrays
