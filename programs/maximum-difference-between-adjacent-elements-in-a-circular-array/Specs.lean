import Aegis.MaxAdjacentDistance.Code.Funs

/-!
# Specifications of `Aegis.MaxAdjacentDistance.max_adjacent_distance`

LeetCode problem `maximum-difference-between-adjacent-elements-in-a-circular-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxAdjacentDistance

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def nth (l : List Int) (i : Nat) : Int := (l[i]?).getD 0

  def absCyclicDiff (l : List Int) (i : Nat) : Int :=
    |nth l ((i + 1) % l.length) - nth l i|

  def cyclicDiffs (l : List Int) : List Int :=
    (List.range l.length).map (absCyclicDiff l)

  def maxAdjacentDistance (l : List Int) : Int :=
    (cyclicDiffs l).foldr max 0

  def rotate (l : List Int) (k : Nat) : List Int :=
    (List.range l.length).map (fun i => nth l ((i + k) % l.length))

  def reverse (l : List Int) : List Int :=
    (List.range l.length).map (fun i => nth l (l.length - 1 - i))

  def shiftAll (l : List Int) (c : Int) : List Int := l.map (fun x => x + c)

  def scaleAll (l : List Int) (k : Int) : List Int := l.map (fun x => k * x)

  def negateAll (l : List Int) : List Int := l.map (fun x => -x)

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, r is the maximum, over all i with 0 <= i < len(nums), of |nums[(i+1) mod len(nums)] - nums[i]|. Here |x| is the absolute value of the integer x, and (i+1) mod len(nums) uses the usual nonnegative remainder.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        r.val = maxAdjacentDistance (vals nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          r.val = maxAdjacentDistance (vals nums)) := by
    sorry

  /-- For every nums satisfying the preconditions, the function max_adjacent_distance(nums) returns Result.ok r for some 64-bit integer r; it does not fail.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100) :
      ∃ r : Std.I64, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100), ∃ r : Std.I64, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r) := by
    sorry

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, we have 0 <= r.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, we have r <= 200.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r → r.val ≤ 200 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r → r.val ≤ 200) := by
    sorry

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, there exists an index i with 0 <= i < len(nums) such that r = |nums[(i+1) mod len(nums)] - nums[i]|.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        ∃ i, i < (vals nums).length ∧ r.val = absCyclicDiff (vals nums) i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          ∃ i, i < (vals nums).length ∧ r.val = absCyclicDiff (vals nums) i) := by
    sorry

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, for every i with 0 <= i < len(nums), we have |nums[(i+1) mod len(nums)] - nums[i]| <= r.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        ∀ i, i < (vals nums).length → absCyclicDiff (vals nums) i ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          ∀ i, i < (vals nums).length → absCyclicDiff (vals nums) i ≤ r.val) := by
    sorry

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] = nums[0].
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        (r.val = 0 ↔ ∀ i, i < (vals nums).length → nth (vals nums) i = nth (vals nums) 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          (r.val = 0 ↔ ∀ i, i < (vals nums).length → nth (vals nums) i = nth (vals nums) 0)) := by
    sorry

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, r = nums[len(nums)-1] - nums[0].
    Preconditions: len(nums) >= 2, len(nums) <= 100, for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100, and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
      (hsorted : ∀ i, i + 1 < (vals nums).length → nth (vals nums) i ≤ nth (vals nums) (i + 1)) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        r.val = nth (vals nums) ((vals nums).length - 1) - nth (vals nums) 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
        (hsorted : ∀ i, i + 1 < (vals nums).length → nth (vals nums) i ≤ nth (vals nums) (i + 1)), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          r.val = nth (vals nums) ((vals nums).length - 1) - nth (vals nums) 0) := by
    sorry

  /-- Whenever max_adjacent_distance(nums) returns Result.ok r, r = nums[0] - nums[len(nums)-1].
    Preconditions: len(nums) >= 2, len(nums) <= 100, for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100, and for every i with 0 <= i < len(nums)-1, nums[i] >= nums[i+1]. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
      (hanti : ∀ i, i + 1 < (vals nums).length → nth (vals nums) (i + 1) ≤ nth (vals nums) i) :
      ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        r.val = nth (vals nums) 0 - nth (vals nums) ((vals nums).length - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
        (hanti : ∀ i, i + 1 < (vals nums).length → nth (vals nums) (i + 1) ≤ nth (vals nums) i), ∀ r, Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          r.val = nth (vals nums) 0 - nth (vals nums) ((vals nums).length - 1)) := by
    sorry

  /-- For every integer k with 0 <= k < len(nums), let rot be the slice of length len(nums) defined by rot[i] = nums[(i+k) mod len(nums)] for 0 <= i < len(nums). Whenever max_adjacent_distance(nums) returns Result.ok r and max_adjacent_distance(rot) returns Result.ok r', we have r = r'.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_10 (nums rot : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
      (k : Nat) (hk : k < (vals nums).length)
      (hrot : vals rot = rotate (vals nums) k) :
      ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        Aegis.MaxAdjacentDistance.max_adjacent_distance rot = ok r' → r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums rot : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
        (k : Nat) (hk : k < (vals nums).length)
        (hrot : vals rot = rotate (vals nums) k), ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          Aegis.MaxAdjacentDistance.max_adjacent_distance rot = ok r' → r.val = r'.val) := by
    sorry

  /-- Let rev be the slice of length len(nums) defined by rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Whenever max_adjacent_distance(nums) returns Result.ok r and max_adjacent_distance(rev) returns Result.ok r', we have r = r'.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_11 (nums rev : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
      (hrev : vals rev = reverse (vals nums)) :
      ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        Aegis.MaxAdjacentDistance.max_adjacent_distance rev = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums rev : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
        (hrev : vals rev = reverse (vals nums)), ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          Aegis.MaxAdjacentDistance.max_adjacent_distance rev = ok r' → r.val = r'.val) := by
    sorry

  /-- For every integer c satisfying -100 <= nums[i] + c <= 100 for every i with 0 <= i < len(nums), let shift be the slice of length len(nums) with shift[i] = nums[i] + c. Whenever max_adjacent_distance(nums) returns Result.ok r and max_adjacent_distance(shift) returns Result.ok r', we have r = r'.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_12 (nums shift : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
      (c : Int) (hc : ∀ x ∈ vals nums, -100 ≤ x + c ∧ x + c ≤ 100)
      (hshift : vals shift = shiftAll (vals nums) c) :
      ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        Aegis.MaxAdjacentDistance.max_adjacent_distance shift = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums shift : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
        (c : Int) (hc : ∀ x ∈ vals nums, -100 ≤ x + c ∧ x + c ≤ 100)
        (hshift : vals shift = shiftAll (vals nums) c), ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          Aegis.MaxAdjacentDistance.max_adjacent_distance shift = ok r' → r.val = r'.val) := by
    sorry

  /-- For every integer k with k >= 0 and with -100 <= k * nums[i] <= 100 for every i with 0 <= i < len(nums), let scaled be the slice of length len(nums) with scaled[i] = k * nums[i]. Whenever max_adjacent_distance(nums) returns Result.ok r and max_adjacent_distance(scaled) returns Result.ok r', we have r' = k * r.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_13 (nums scaled : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
      (k : Int) (hk : 0 ≤ k) (hkrange : ∀ x ∈ vals nums, -100 ≤ k * x ∧ k * x ≤ 100)
      (hscaled : vals scaled = scaleAll (vals nums) k) :
      ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        Aegis.MaxAdjacentDistance.max_adjacent_distance scaled = ok r' →
        r'.val = k * r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums scaled : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
        (k : Int) (hk : 0 ≤ k) (hkrange : ∀ x ∈ vals nums, -100 ≤ k * x ∧ k * x ≤ 100)
        (hscaled : vals scaled = scaleAll (vals nums) k), ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          Aegis.MaxAdjacentDistance.max_adjacent_distance scaled = ok r' →
          r'.val = k * r.val) := by
    sorry

  /-- Let neg be the slice of length len(nums) defined by neg[i] = -nums[i] for 0 <= i < len(nums). Whenever max_adjacent_distance(nums) returns Result.ok r and max_adjacent_distance(neg) returns Result.ok r', we have r = r'.
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_14 (nums neg : Slice Std.I64)
      (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
      (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
      (hneg : vals neg = negateAll (vals nums)) :
      ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
        Aegis.MaxAdjacentDistance.max_adjacent_distance neg = ok r' → r.val = r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums neg : Slice Std.I64)
        (hlen_ge : 2 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100)
        (hbounds : ∀ x ∈ vals nums, -100 ≤ x ∧ x ≤ 100)
        (hneg : vals neg = negateAll (vals nums)), ∀ r r', Aegis.MaxAdjacentDistance.max_adjacent_distance nums = ok r →
          Aegis.MaxAdjacentDistance.max_adjacent_distance neg = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.MaxAdjacentDistance
