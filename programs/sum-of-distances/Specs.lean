import Aegis.Distance.Code.Funs

/-!
# Specifications of `Aegis.Distance.distance`

LeetCode problem `sum-of-distances`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Distance

def valAt (l : List Std.I64) (i : ℕ) : ℤ := ((l[i]?).map (fun x => x.val)).getD 0

def positions (l : List Std.I64) (v : ℤ) : List ℕ :=
  (List.range l.length).filter (fun k => decide (valAt l k = v))

def pget (l : List Std.I64) (v : ℤ) (t : ℕ) : ℕ := (positions l v).getD t 0

def mult (l : List Std.I64) (i : ℕ) : ℕ := (positions l (valAt l i)).length

def totalDistance (l : List Std.I64) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range l.length, |(i : ℤ) - (j : ℤ)|

/-- The function returns a result r such that len(r) = len(nums) and, for every i with 0 <= i < len(nums), r[i] = (the sum of |i - j| over all j with 0 <= j < len(nums), j != i, and nums[j] = nums[i]); this sum is 0 when there is no such j.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.Distance.distance nums = ok r ∧
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length →
        valAt r.val i =
          ∑ j ∈ Finset.range nums.val.length,
            (if j ≠ i ∧ valAt nums.val j = valAt nums.val i then |(i : ℤ) - (j : ℤ)| else 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.Distance.distance nums = ok r ∧
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length →
        valAt r.val i =
          ∑ j ∈ Finset.range nums.val.length,
            (if j ≠ i ∧ valAt nums.val j = valAt nums.val i then |(i : ℤ) - (j : ℤ)| else 0)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    r.val.length = nums.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), r.val.length = nums.val.length) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.Distance.distance nums = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9), ∃ r : alloc.vec.Vec Std.I64, Aegis.Distance.distance nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] >= 0.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ i, i < nums.val.length → 0 ≤ valAt r.val i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ i, i < nums.val.length → 0 ≤ valAt r.val i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] <= (the sum of |i - j| over all j with 0 <= j < len(nums)).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ i, i < nums.val.length → valAt r.val i ≤ totalDistance nums.val i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ i, i < nums.val.length → valAt r.val i ≤ totalDistance nums.val i) := by
  sorry

/-- Whenever the function returns a result r and len(nums) = 1, r[0] = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r)
    (h1 : nums.val.length = 1) :
    valAt r.val 0 = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r)
    (h1 : nums.val.length = 1), valAt r.val 0 = 0) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums) such that nums[j] != nums[i] for all j with 0 <= j < len(nums) and j != i, we have r[i] = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ i, i < nums.val.length →
      (∀ j, j < nums.val.length → j ≠ i → valAt nums.val j ≠ valAt nums.val i) →
      valAt r.val i = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ i, i < nums.val.length →
      (∀ j, j < nums.val.length → j ≠ i → valAt nums.val j ≠ valAt nums.val i) →
      valAt r.val i = 0) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if there exists j with 0 <= j < len(nums), j != i, and nums[j] = nums[i], then r[i] >= 1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ i, i < nums.val.length →
      (∃ j, j < nums.val.length ∧ j ≠ i ∧ valAt nums.val j = valAt nums.val i) →
      1 ≤ valAt r.val i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ i, i < nums.val.length →
      (∃ j, j < nums.val.length ∧ j ≠ i ∧ valAt nums.val j = valAt nums.val i) →
      1 ≤ valAt r.val i) := by
  sorry

/-- Whenever the function returns a result r, for all i, j with 0 <= i < len(nums), 0 <= j < len(nums), i != j, nums[j] = nums[i], and nums[k] != nums[i] for every k with 0 <= k < len(nums), k != i, k != j, we have r[i] = |i - j|.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ i, i < nums.val.length → ∀ j, j < nums.val.length → i ≠ j →
      valAt nums.val j = valAt nums.val i →
      (∀ k, k < nums.val.length → k ≠ i → k ≠ j → valAt nums.val k ≠ valAt nums.val i) →
      valAt r.val i = |(i : ℤ) - (j : ℤ)| := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ i, i < nums.val.length → ∀ j, j < nums.val.length → i ≠ j →
      valAt nums.val j = valAt nums.val i →
      (∀ k, k < nums.val.length → k ≠ i → k ≠ j → valAt nums.val k ≠ valAt nums.val i) →
      valAt r.val i = |(i : ℤ) - (j : ℤ)|) := by
  sorry

/-- Whenever the function returns a result r, the sum of r[i] over all i with 0 <= i < len(nums) equals 2 * (the sum of (j - i) over all pairs (i, j) with 0 <= i < j < len(nums) and nums[i] = nums[j]).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    (∑ i ∈ Finset.range nums.val.length, valAt r.val i) =
      2 * ∑ i ∈ Finset.range nums.val.length,
            ∑ j ∈ Finset.range nums.val.length,
              (if i < j ∧ valAt nums.val i = valAt nums.val j then (j : ℤ) - (i : ℤ) else 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), (∑ i ∈ Finset.range nums.val.length, valAt r.val i) =
      2 * ∑ i ∈ Finset.range nums.val.length,
            ∑ j ∈ Finset.range nums.val.length,
              (if i < j ∧ valAt nums.val i = valAt nums.val j then (j : ℤ) - (i : ℤ) else 0)) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, let p_1 < p_2 < ... < p_m be the increasing list of all indices k with 0 <= k < len(nums) and nums[k] = v (so m is the number of such indices, possibly 0); then for every k with 1 <= k < m, r[p_{k+1}] - r[p_k] = (2*k - m) * (p_{k+1} - p_k).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ v : ℤ, ∀ k : ℕ, 1 ≤ k → k < (positions nums.val v).length →
      valAt r.val (pget nums.val v k) - valAt r.val (pget nums.val v (k - 1)) =
        (2 * (k : ℤ) - ((positions nums.val v).length : ℤ)) *
          ((pget nums.val v k : ℤ) - (pget nums.val v (k - 1) : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ v : ℤ, ∀ k : ℕ, 1 ≤ k → k < (positions nums.val v).length →
      valAt r.val (pget nums.val v k) - valAt r.val (pget nums.val v (k - 1)) =
        (2 * (k : ℤ) - ((positions nums.val v).length : ℤ)) *
          ((pget nums.val v k : ℤ) - (pget nums.val v (k - 1) : ℤ))) := by
  sorry

/-- Whenever the function returns a result r and nums[i] = nums[0] for every i with 0 <= i < len(nums), then for every i with 0 <= i < len(nums), r[i] = i*(i+1)/2 + (len(nums)-1-i)*(len(nums)-i)/2.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r)
    (hall : ∀ i, i < nums.val.length → valAt nums.val i = valAt nums.val 0) :
    ∀ i, i < nums.val.length →
      valAt r.val i =
        (i : ℤ) * ((i : ℤ) + 1) / 2 +
          (((nums.val.length : ℤ) - 1 - (i : ℤ)) * ((nums.val.length : ℤ) - (i : ℤ))) / 2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r)
    (hall : ∀ i, i < nums.val.length → valAt nums.val i = valAt nums.val 0), ∀ i, i < nums.val.length →
      valAt r.val i =
        (i : ℤ) * ((i : ℤ) + 1) / 2 +
          (((nums.val.length : ℤ) - 1 - (i : ℤ)) * ((nums.val.length : ℤ) - (i : ℤ))) / 2) := by
  sorry

/-- For every array nums satisfying the preconditions, let rev be the array of the same length with rev[k] = nums[len(nums)-1-k] for every k with 0 <= k < len(nums). If the function returns r on input nums and returns r' on input rev, then for every k with 0 <= k < len(nums), r'[k] = r[len(nums)-1-k].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_13 (nums rev : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hrev : rev.val = nums.val.reverse)
    (r r' : alloc.vec.Vec Std.I64)
    (hr : Aegis.Distance.distance nums = ok r)
    (hr' : Aegis.Distance.distance rev = ok r') :
    ∀ k, k < nums.val.length → valAt r'.val k = valAt r.val (nums.val.length - 1 - k) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hrev : rev.val = nums.val.reverse)
    (r r' : alloc.vec.Vec Std.I64)
    (hr : Aegis.Distance.distance nums = ok r)
    (hr' : Aegis.Distance.distance rev = ok r'), ∀ k, k < nums.val.length → valAt r'.val k = valAt r.val (nums.val.length - 1 - k)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] <= (c_i - 1) * (len(nums) - 1), where c_i is the number of indices j with 0 <= j < len(nums) and nums[j] = nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ i, i < nums.val.length →
      valAt r.val i ≤ ((mult nums.val i : ℤ) - 1) * ((nums.val.length : ℤ) - 1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ i, i < nums.val.length →
      valAt r.val i ≤ ((mult nums.val i : ℤ) - 1) * ((nums.val.length : ℤ) - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, let p_1 < p_2 < ... < p_m be the increasing list of all indices k with 0 <= k < len(nums) and nums[k] = v (with m = 0 when there are none). Then the sum of r[p_t] over 1 <= t <= m equals 2 * (the sum of (p_b - p_a) over all pairs (a, b) with 1 <= a < b <= m).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_15 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r) :
    ∀ v : ℤ,
      (∑ t ∈ Finset.range (positions nums.val v).length, valAt r.val (pget nums.val v t)) =
        2 * ∑ a ∈ Finset.range (positions nums.val v).length,
              ∑ b ∈ Finset.range (positions nums.val v).length,
                (if a < b then (pget nums.val v b : ℤ) - (pget nums.val v a : ℤ) else 0) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (hbounds : ∀ i, i < nums.val.length → 0 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (r : alloc.vec.Vec Std.I64) (hr : Aegis.Distance.distance nums = ok r), ∀ v : ℤ,
      (∑ t ∈ Finset.range (positions nums.val v).length, valAt r.val (pget nums.val v t)) =
        2 * ∑ a ∈ Finset.range (positions nums.val v).length,
              ∑ b ∈ Finset.range (positions nums.val v).length,
                (if a < b then (pget nums.val v b : ℤ) - (pget nums.val v a : ℤ) else 0)) := by
  sorry

end AegisSpec.Distance
