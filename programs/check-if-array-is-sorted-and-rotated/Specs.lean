import Aegis.Check.Code.Funs

/-!
# Specifications of `Aegis.Check.check`

LeetCode problem `check-if-array-is-sorted-and-rotated`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Check

def elt (nums : Slice Std.I64) (i : ℕ) : ℤ :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def eltMod (nums : Slice Std.I64) (i : ℤ) : ℤ :=
  elt nums ((i % (nums.val.length : ℤ)).toNat)

abbrev DescendingAt (nums : Slice Std.I64) (i : ℕ) : Prop :=
  elt nums i > elt nums ((i + 1) % nums.val.length)

def descentCount (nums : Slice Std.I64) : ℕ :=
  ((List.range nums.val.length).filter (fun i => DescendingAt nums i)).length

def CycSortedFrom (nums : Slice Std.I64) (s : ℕ) : Prop :=
  ∀ j, j < nums.val.length - 1 →
    elt nums ((s + j) % nums.val.length) ≤ elt nums ((s + j + 1) % nums.val.length)

/-- Let n = len(nums). The function returns a result r (i.e., it does not fail) and r = true if and only if there exists an integer s with 0 <= s < n such that for every j with 0 <= j < n-1, nums[(s+j) mod n] <= nums[(s+j+1) mod n]. (This says nums is a rotation of a non-decreasing array.)
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∃ r, Aegis.Check.check nums = ok r ∧
      (r = true ↔ ∃ s, s < nums.val.length ∧ CycSortedFrom nums s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∃ r, Aegis.Check.check nums = ok r ∧
      (r = true ↔ ∃ s, s < nums.val.length ∧ CycSortedFrom nums s)) := by
  sorry

/-- Let n = len(nums). The function returns a result r (i.e., it does not fail).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∃ r, Aegis.Check.check nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∃ r, Aegis.Check.check nums = ok r) := by
  sorry

/-- Let n = len(nums). The function returns true if and only if the number of indices i with 0 <= i < n such that nums[i] > nums[(i+1) mod n] is at most 1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∃ r, Aegis.Check.check nums = ok r ∧ (r = true ↔ descentCount nums ≤ 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∃ r, Aegis.Check.check nums = ok r ∧ (r = true ↔ descentCount nums ≤ 1)) := by
  sorry

/-- Let n = len(nums). For every integer k, let nums' be the slice of length n defined by nums'[i] = nums[(i+k) mod n] for 0 <= i < n. Then the function returns the same boolean result on nums' as it does on nums (i.e., check(nums') = check(nums)).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∀ (k : ℤ) (nums' : Slice Std.I64),
      nums'.val.length = nums.val.length →
      (∀ i, i < nums.val.length → elt nums' i = eltMod nums ((i : ℤ) + k)) →
      Aegis.Check.check nums' = Aegis.Check.check nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∀ (k : ℤ) (nums' : Slice Std.I64),
      nums'.val.length = nums.val.length →
      (∀ i, i < nums.val.length → elt nums' i = eltMod nums ((i : ℤ) + k)) →
      Aegis.Check.check nums' = Aegis.Check.check nums) := by
  sorry

/-- Let n = len(nums). Whenever the function returns true, there exists an integer s with 0 <= s < n such that for every j with 0 <= j < n-1, nums[(s+j) mod n] <= nums[(s+j+1) mod n].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∀ r, Aegis.Check.check nums = ok r → r = true →
      ∃ s, s < nums.val.length ∧ CycSortedFrom nums s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∀ r, Aegis.Check.check nums = ok r → r = true →
      ∃ s, s < nums.val.length ∧ CycSortedFrom nums s) := by
  sorry

/-- Let n = len(nums). Whenever the function returns true, there exists an integer s with 0 <= s < n such that: (1) nums[s] <= nums[i] for every i with 0 <= i < n (i.e., nums[s] is a minimum element), and (2) for every j with 0 <= j < n-1, nums[(s+j) mod n] <= nums[(s+j+1) mod n].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∀ r, Aegis.Check.check nums = ok r → r = true →
      ∃ s, s < nums.val.length ∧
        (∀ i, i < nums.val.length → elt nums s ≤ elt nums i) ∧
        CycSortedFrom nums s := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∀ r, Aegis.Check.check nums = ok r → r = true →
      ∃ s, s < nums.val.length ∧
        (∀ i, i < nums.val.length → elt nums s ≤ elt nums i) ∧
        CycSortedFrom nums s) := by
  sorry

/-- Let n = len(nums). Whenever the function returns false, there exist two distinct indices i and j with 0 <= i < n, 0 <= j < n, i != j, such that nums[i] > nums[(i+1) mod n] and nums[j] > nums[(j+1) mod n].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∀ r, Aegis.Check.check nums = ok r → r = false →
      ∃ i, ∃ j, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
        DescendingAt nums i ∧ DescendingAt nums j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∀ r, Aegis.Check.check nums = ok r → r = false →
      ∃ i, ∃ j, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
        DescendingAt nums i ∧ DescendingAt nums j) := by
  sorry

/-- Let n = len(nums). Whenever the function returns false, for every integer s with 0 <= s < n there exists an index j with 0 <= j < n-1 such that nums[(s+j) mod n] > nums[(s+j+1) mod n].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∀ r, Aegis.Check.check nums = ok r → r = false →
      ∀ s, s < nums.val.length →
        ∃ j, j < nums.val.length - 1 ∧
          elt nums ((s + j) % nums.val.length) > elt nums ((s + j + 1) % nums.val.length) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∀ r, Aegis.Check.check nums = ok r → r = false →
      ∀ s, s < nums.val.length →
        ∃ j, j < nums.val.length - 1 ∧
          elt nums ((s + j) % nums.val.length) > elt nums ((s + j + 1) % nums.val.length)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns true and not all elements of nums are equal (i.e., there exist i and j with 0 <= i < n, 0 <= j < n such that nums[i] != nums[j]), there is exactly one index i with 0 <= i < n such that nums[i] > nums[(i+1) mod n].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    ∀ r, Aegis.Check.check nums = ok r → r = true →
      (∃ i, ∃ j, i < nums.val.length ∧ j < nums.val.length ∧ elt nums i ≠ elt nums j) →
      ∃! i, i < nums.val.length ∧ DescendingAt nums i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), ∀ r, Aegis.Check.check nums = ok r → r = true →
      (∃ i, ∃ j, i < nums.val.length ∧ j < nums.val.length ∧ elt nums i ≠ elt nums j) →
      ∃! i, i < nums.val.length ∧ DescendingAt nums i) := by
  sorry

/-- Let n = len(nums). If there exists an integer s with 0 <= s < n such that for every j with 0 <= j < n-1, nums[(s+j) mod n] <= nums[(s+j+1) mod n], then the function returns true.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100) :
    (∃ s, s < nums.val.length ∧ CycSortedFrom nums s) →
      Aegis.Check.check nums = ok true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elt nums i ∧ elt nums i ≤ 100), (∃ s, s < nums.val.length ∧ CycSortedFrom nums s) →
      Aegis.Check.check nums = ok true) := by
  sorry

end AegisSpec.Check
