import Aegis.RearrangeArray.Code.Funs

/-!
# Specifications of `Aegis.RearrangeArray.rearrange_array`

LeetCode problem `array-with-elements-not-equal-to-average-of-neighbors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RearrangeArray (rearrange_array)

namespace AegisSpec.RearrangeArray

def ints (l : List Std.I64) : List Int := l.map (fun x => x.val)

def countOcc (l : List Int) (x : Int) : Nat := l.count x

def IsRearrangement (l₁ l₂ : List Int) : Prop :=
  l₁.length = l₂.length ∧ ∀ x : Int, countOcc l₁ x = countOcc l₂ x

def listMin (l : List Int) : Int := l.foldr min (l.headD 0)

def listMax (l : List Int) : Int := l.foldr max (l.headD 0)

def NoAvgNeighbours (l : List Int) : Prop :=
  ∀ (i : Nat) (h₁ : 1 ≤ i) (h₂ : i + 1 < l.length), 2 * l[i] ≠ l[i-1] + l[i+1]

/-- The function returns a result r such that r is a rearrangement of nums (the same length and the same multiset of values), and for every i with 1 <= i < len(r) - 1, 2 * r[i] != r[i-1] + r[i+1].
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∃ r : alloc.vec.Vec Std.I64,
      rearrange_array nums = ok r ∧
      IsRearrangement (ints r.val) (ints nums.val) ∧
      NoAvgNeighbours (ints r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∃ r : alloc.vec.Vec Std.I64,
      rearrange_array nums = ok r ∧
      IsRearrangement (ints r.val) (ints nums.val) ∧
      NoAvgNeighbours (ints r.val)) := by
  sorry

/-- The function returns a result r (it does not fail) for every nums satisfying the preconditions.
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∃ r : alloc.vec.Vec Std.I64, rearrange_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∃ r : alloc.vec.Vec Std.I64, rearrange_array nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r → r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r → r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every integer x, the number of indices j with 0 <= j < len(r) and r[j] = x equals the number of indices i with 0 <= i < len(nums) and nums[i] = x.
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ x : Int, countOcc (ints r.val) x = countOcc (ints nums.val) x := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ x : Int, countOcc (ints r.val) x = countOcc (ints nums.val) x) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (i j : Nat) (hij : i < j) (hj : j < (ints r.val).length),
        (ints r.val)[i] ≠ (ints r.val)[j] := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (i j : Nat) (hij : i < j) (hj : j < (ints r.val).length),
        (ints r.val)[i] ≠ (ints r.val)[j]) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), there exists i with 0 <= i < len(nums) such that r[j] = nums[i].
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (j : Nat) (hj : j < (ints r.val).length),
        ∃ (i : Nat) (hi : i < (ints nums.val).length), (ints r.val)[j] = (ints nums.val)[i] := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (j : Nat) (hj : j < (ints r.val).length),
        ∃ (i : Nat) (hi : i < (ints nums.val).length), (ints r.val)[j] = (ints nums.val)[i]) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), there exists j with 0 <= j < len(r) such that r[j] = nums[i].
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (i : Nat) (hi : i < (ints nums.val).length),
        ∃ (j : Nat) (hj : j < (ints r.val).length), (ints r.val)[j] = (ints nums.val)[i] := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (i : Nat) (hi : i < (ints nums.val).length),
        ∃ (j : Nat) (hj : j < (ints r.val).length), (ints r.val)[j] = (ints nums.val)[i]) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), min(nums) <= r[j] <= max(nums), where min(nums) and max(nums) are the minimum and maximum values occurring in nums.
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (j : Nat) (hj : j < (ints r.val).length),
        listMin (ints nums.val) ≤ (ints r.val)[j] ∧
        (ints r.val)[j] ≤ listMax (ints nums.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      ∀ (j : Nat) (hj : j < (ints r.val).length),
        listMin (ints nums.val) ≤ (ints r.val)[j] ∧
        (ints r.val)[j] ≤ listMax (ints nums.val)) := by
  sorry

/-- Whenever the function returns a result r, the sum of all entries of r equals the sum of all entries of nums: sum over j with 0 <= j < len(r) of r[j] equals sum over i with 0 <= i < len(nums) of nums[i], using integer arithmetic.
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      (ints r.val).sum = (ints nums.val).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      (ints r.val).sum = (ints nums.val).sum) := by
  sorry

/-- Whenever the function returns a result r, for every i with 1 <= i < len(r) - 1, the middle value r[i] is not the average of its two neighbors: 2 * r[i] != r[i-1] + r[i+1].
  Preconditions: 3 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_10 (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val) :
    ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      NoAvgNeighbours (ints r.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 3 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_distinct : ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≠ (nums.val[j]).val), ∀ (r : alloc.vec.Vec Std.I64), rearrange_array nums = ok r →
      NoAvgNeighbours (ints r.val)) := by
  sorry

end AegisSpec.RearrangeArray
