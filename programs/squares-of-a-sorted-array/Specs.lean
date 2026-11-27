import Aegis.SortedSquares.Code.Funs

/-!
# Specifications of `Aegis.SortedSquares.sorted_squares`

LeetCode problem `squares-of-a-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SortedSquares

def sliceVals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def vecVals (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

def squares (l : List ℤ) : List ℤ := l.map (fun x => x * x)

def absVals (l : List ℤ) : List ℤ := l.map (fun x => |x|)

def countOcc (l : List ℤ) (v : ℤ) : ℕ := (l.filter (fun x => x = v)).length

def SortedNondec (l : List ℤ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < l.length), l.get ⟨i, by omega⟩ ≤ l.get ⟨i + 1, h⟩

def IsMinOf (v : ℤ) (l : List ℤ) : Prop := (∀ x ∈ l, v ≤ x) ∧ v ∈ l

def IsMaxOf (v : ℤ) (l : List ℤ) : Prop := (∀ x ∈ l, x ≤ v) ∧ v ∈ l

def SortedPerm (l' l : List ℤ) : Prop :=
  l'.length = l.length ∧ SortedNondec l' ∧ ∀ v : ℤ, countOcc l' v = countOcc l v

/-- The function returns a result r such that len(r) = len(nums), r is sorted in non-decreasing order (for every i with 0 <= i < len(r)-1, r[i] <= r[i+1]), and for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(nums) and nums[j] * nums[j] = v.
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortedSquares.sorted_squares nums = ok r ∧
      r.val.length = nums.val.length ∧
      SortedNondec (vecVals r) ∧
      ∀ v : ℤ, countOcc (vecVals r) v = countOcc (squares (sliceVals nums)) v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortedSquares.sorted_squares nums = ok r ∧
      r.val.length = nums.val.length ∧
      SortedNondec (vecVals r) ∧
      ∀ v : ℤ, countOcc (vecVals r) v = countOcc (squares (sliceVals nums)) v) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail.
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∃ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortedSquares.sorted_squares nums = ok r → r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortedSquares.sorted_squares nums = ok r → r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, r is sorted in non-decreasing order: for every i with 0 <= i < len(r)-1, r[i] <= r[i+1].
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortedSquares.sorted_squares nums = ok r → SortedNondec (vecVals r) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortedSquares.sorted_squares nums = ok r → SortedNondec (vecVals r)) := by
  sorry

/-- Whenever the function returns a result r, every element of r is non-negative: for every i with 0 <= i < len(r), r[i] >= 0.
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ x ∈ vecVals r, 0 ≤ x := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ x ∈ vecVals r, 0 ≤ x) := by
  sorry

/-- Whenever the function returns a result r, every element of r is at most 100000000: for every i with 0 <= i < len(r), r[i] <= 100000000.
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ x ∈ vecVals r, x ≤ 100000000 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ x ∈ vecVals r, x ≤ 100000000) := by
  sorry

/-- Whenever the function returns a result r, the multiset of values in r is exactly the multiset of squares of nums: for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(nums) and nums[j] * nums[j] = v.
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ v : ℤ, countOcc (vecVals r) v = countOcc (squares (sliceVals nums)) v := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ v : ℤ, countOcc (vecVals r) v = countOcc (squares (sliceVals nums)) v) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and r[0] is the smallest value among all nums[j] * nums[j] for 0 <= j < len(nums).
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      1 ≤ r.val.length ∧
        ∃ m : ℤ, (vecVals r).head? = some m ∧ IsMinOf m (squares (sliceVals nums)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      1 ≤ r.val.length ∧
        ∃ m : ℤ, (vecVals r).head? = some m ∧ IsMinOf m (squares (sliceVals nums))) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and r[len(r)-1] is the largest value among all nums[j] * nums[j] for 0 <= j < len(nums).
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      1 ≤ r.val.length ∧
        ∃ m : ℤ, (vecVals r).getLast? = some m ∧ IsMaxOf m (squares (sliceVals nums)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      1 ≤ r.val.length ∧
        ∃ m : ℤ, (vecVals r).getLast? = some m ∧ IsMaxOf m (squares (sliceVals nums))) := by
  sorry

/-- Whenever the function returns a result r, the number of zero elements in r equals the number of zero elements in nums: the number of indices i with 0 <= i < len(r) and r[i] = 0 equals the number of indices j with 0 <= j < len(nums) and nums[j] = 0.
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      countOcc (vecVals r) 0 = countOcc (sliceVals nums) 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      countOcc (vecVals r) 0 = countOcc (sliceVals nums) 0) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums) and for every i with 0 <= i < len(nums), r[i] is the square of the (i+1)-th smallest absolute value among nums[0], nums[1], ..., nums[len(nums)-1], counting duplicates.
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      r.val.length = nums.val.length ∧
        ∃ a : List ℤ, SortedPerm a (absVals (sliceVals nums)) ∧
          ∀ i : ℕ, i < r.val.length →
            ∃ x : ℤ, a[i]? = some x ∧ (vecVals r)[i]? = some (x * x) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      r.val.length = nums.val.length ∧
        ∃ a : List ℤ, SortedPerm a (absVals (sliceVals nums)) ∧
          ∀ i : ℕ, i < r.val.length →
            ∃ x : ℤ, a[i]? = some x ∧ (vecVals r)[i]? = some (x * x)) := by
  sorry

/-- Whenever the function returns a result r, every element of r is the square of some input element: for every i with 0 <= i < len(r), there exists j with 0 <= j < len(nums) such that r[i] = nums[j] * nums[j].
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ i : ℕ, i < r.val.length →
        ∃ j : ℕ, j < nums.val.length ∧ ∃ x : ℤ,
          (sliceVals nums)[j]? = some x ∧ (vecVals r)[i]? = some (x * x) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ i : ℕ, i < r.val.length →
        ∃ j : ℕ, j < nums.val.length ∧ ∃ x : ℤ,
          (sliceVals nums)[j]? = some x ∧ (vecVals r)[i]? = some (x * x)) := by
  sorry

/-- Whenever the function returns a result r, every input element contributes its square to r: for every j with 0 <= j < len(nums), there exists i with 0 <= i < len(r) such that r[i] = nums[j] * nums[j].
  Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; and for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ j : ℕ, j < nums.val.length →
        ∃ i : ℕ, i < r.val.length ∧ ∃ x : ℤ,
          (sliceVals nums)[j]? = some x ∧ (vecVals r)[i]? = some (x * x) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hsorted : SortedNondec (sliceVals nums)), ∀ r : alloc.vec.Vec Std.I64, Aegis.SortedSquares.sorted_squares nums = ok r →
      ∀ j : ℕ, j < nums.val.length →
        ∃ i : ℕ, i < r.val.length ∧ ∃ x : ℤ,
          (sliceVals nums)[j]? = some x ∧ (vecVals r)[i]? = some (x * x)) := by
  sorry

end AegisSpec.SortedSquares
