import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `find-minimum-operations-to-make-all-elements-divisible-by-three`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumOperations (minimum_operations)

namespace AegisSpec.MinimumOperations

def cost (a : ℤ) : ℤ := if (3 : ℤ) ∣ a then 0 else 1

def totalCost (nums : Slice Std.I64) : ℤ :=
  (nums.val.map (fun x => cost x.val)).sum

def countNotDivisible (nums : Slice Std.I64) : ℕ :=
  (nums.val.filter (fun x => ¬ (3 : ℤ) ∣ x.val)).length

def notDivisibleIndices (nums : Slice Std.I64) : Finset (Fin nums.val.length) :=
  Finset.univ.filter (fun i => ¬ (3 : ℤ) ∣ (nums.val.get i).val)

def changeSetWorks (nums : Slice Std.I64) (S : Finset (Fin nums.val.length)) : Prop :=
  ∃ δ : Fin nums.val.length → ℤ,
    (∀ i, i ∉ S → δ i = 0) ∧
      (∀ i, i ∈ S → δ i = 1 ∨ δ i = -1) ∧
        (∀ i, (3 : ℤ) ∣ (nums.val.get i).val + δ i)

/-- The function returns a result r, and r equals the number of indices i with 0 <= i < len(nums) such that nums[i] is not divisible by 3. Equivalently, r = sum over i of cost(nums[i]), where cost(a)=0 if 3 divides a and cost(a)=1 otherwise. This r is the minimum total number of add-1 or subtract-1 operations on array elements needed to make every element divisible by 3.
  Preconditions: len(nums) is between 1 and 50 inclusive, and for every i with 0 <= i < len(nums), nums[i] is between 1 and 50 inclusive. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50) :
    ∃ r : Std.I64,
      minimum_operations nums = ok r ∧
        r.val = totalCost nums ∧ r.val = (countNotDivisible nums : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50), ∃ r : Std.I64,
      minimum_operations nums = ok r ∧
        r.val = totalCost nums ∧ r.val = (countNotDivisible nums : ℤ)) := by
  sorry

/-- The function returns a result r and does not fail (no arithmetic overflow, out-of-bounds access, or panic) for every input satisfying the preconditions.
  Preconditions: len(nums) is between 1 and 50 inclusive, and for every i with 0 <= i < len(nums), nums[i] is between 1 and 50 inclusive. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50) :
    ∃ r : Std.I64, minimum_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50), ∃ r : Std.I64, minimum_operations nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums).
  Preconditions: len(nums) is between 1 and 50 inclusive, and for every i with 0 <= i < len(nums), nums[i] is between 1 and 50 inclusive. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (r : Std.I64) (hr : minimum_operations nums = ok r) :
    r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (r : Std.I64) (hr : minimum_operations nums = ok r), r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns results r and s for nums and alt respectively, r = s.
  Preconditions: nums and alt are slices of i64, each with length between 1 and 50 inclusive and entries between 1 and 50 inclusive, and alt is a permutation of nums (same length and same multiset of elements). -/
theorem spec_4 (nums alt : Slice Std.I64)
    (hnums_len : 1 ≤ nums.val.length) (hnums_len' : nums.val.length ≤ 50)
    (halt_len : 1 ≤ alt.val.length) (halt_len' : alt.val.length ≤ 50)
    (hnums_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (halt_range : ∀ x ∈ alt.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (hperm : nums.val.Perm alt.val)
    (r s : Std.I64) (hr : minimum_operations nums = ok r)
    (hs : minimum_operations alt = ok s) :
    r.val = s.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums alt : Slice Std.I64)
    (hnums_len : 1 ≤ nums.val.length) (hnums_len' : nums.val.length ≤ 50)
    (halt_len : 1 ≤ alt.val.length) (halt_len' : alt.val.length ≤ 50)
    (hnums_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (halt_range : ∀ x ∈ alt.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (hperm : nums.val.Perm alt.val)
    (r s : Std.I64) (hr : minimum_operations nums = ok r)
    (hs : minimum_operations alt = ok s), r.val = s.val) := by
  sorry

/-- Whenever the function returns results r, rx, and ry for xs ++ ys, xs, and ys respectively, r = rx + ry.
  Preconditions: xs and ys are nonempty slices of i64 with entries between 1 and 50 inclusive and len(xs) + len(ys) <= 50. -/
theorem spec_5 (z xs ys : Slice Std.I64)
    (hxs_len : 1 ≤ xs.val.length) (hys_len : 1 ≤ ys.val.length)
    (hxs_range : ∀ x ∈ xs.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (hys_range : ∀ x ∈ ys.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (hlen : xs.val.length + ys.val.length ≤ 50)
    (hz : z.val = xs.val ++ ys.val)
    (r rx ry : Std.I64) (hr : minimum_operations z = ok r)
    (hrx : minimum_operations xs = ok rx) (hry : minimum_operations ys = ok ry) :
    r.val = rx.val + ry.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (z xs ys : Slice Std.I64)
    (hxs_len : 1 ≤ xs.val.length) (hys_len : 1 ≤ ys.val.length)
    (hxs_range : ∀ x ∈ xs.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (hys_range : ∀ x ∈ ys.val, 1 ≤ x.val ∧ x.val ≤ 50)
    (hlen : xs.val.length + ys.val.length ≤ 50)
    (hz : z.val = xs.val ++ ys.val)
    (r rx ry : Std.I64) (hr : minimum_operations z = ok r)
    (hrx : minimum_operations xs = ok rx) (hry : minimum_operations ys = ok ry), r.val = rx.val + ry.val) := by
  sorry

/-- The function returns a result r, and there exists a set S of exactly r indices with 0 <= i < len(nums) such that changing each nums[i] for i in S by either -1 or +1 and leaving all other elements unchanged makes every element divisible by 3, and no set of fewer than r indices has this property.
  Preconditions: len(nums) is between 1 and 50 inclusive, and for every i with 0 <= i < len(nums), nums[i] is between 1 and 50 inclusive. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50) :
    ∃ r : Std.I64,
      minimum_operations nums = ok r ∧
        ∃ S : Finset (Fin nums.val.length),
          (S.card : ℤ) = r.val ∧
            changeSetWorks nums S ∧
              ∀ T : Finset (Fin nums.val.length), changeSetWorks nums T → S.card ≤ T.card := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50)
    (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50), ∃ r : Std.I64,
      minimum_operations nums = ok r ∧
        ∃ S : Finset (Fin nums.val.length),
          (S.card : ℤ) = r.val ∧
            changeSetWorks nums S ∧
              ∀ T : Finset (Fin nums.val.length), changeSetWorks nums T → S.card ≤ T.card) := by
  sorry

end AegisSpec.MinimumOperations
