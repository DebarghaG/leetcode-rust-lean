import Aegis.MinAbsDifference.Code.Funs

/-!
# Specifications of `Aegis.MinAbsDifference.min_abs_difference`

LeetCode problem `closest-subsequence-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.MinAbsDifference

open Aegis.MinAbsDifference

def ivals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def entry (nums : Slice Std.I64) (i : Nat) : Int := (ivals nums).getD i 0

def subsetSum (nums : Slice Std.I64) (S : Finset (Fin nums.val.length)) : Int :=
  ∑ i ∈ S, entry nums i.val

def totalSum (nums : Slice Std.I64) : Int := (ivals nums).sum

def posSum (nums : Slice Std.I64) : Int := ((ivals nums).filter (fun x => 0 < x)).sum

def negSum (nums : Slice Std.I64) : Int := ((ivals nums).filter (fun x => x < 0)).sum

def negVals (nums : Slice Std.I64) : List Int := (ivals nums).map (fun x => -x)

def revVals (nums : Slice Std.I64) : List Int := (ivals nums).reverse

def permVals (nums : Slice Std.I64) (p : Equiv.Perm (Fin nums.val.length)) : List Int :=
  List.ofFn (fun i : Fin nums.val.length => (nums.val.get (p i)).val)

def delVals (nums : Slice Std.I64) (k : Fin nums.val.length) : List Int :=
  (ivals nums).eraseIdx k.val

def minAbsDiff (nums : Slice Std.I64) (g : Int) : Int :=
  (Finset.univ.image (fun S : Finset (Fin nums.val.length) => |subsetSum nums S - g|)).min'
    ⟨|subsetSum nums (∅ : Finset (Fin nums.val.length)) - g|,
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

def IsMinAbsDiff (nums : Slice Std.I64) (g r : Int) : Prop :=
  (∃ S : Finset (Fin nums.val.length), |subsetSum nums S - g| = r) ∧
    ∀ S : Finset (Fin nums.val.length), r ≤ |subsetSum nums S - g|

/-- Whenever min_abs_difference(nums, goal) returns a result r, r = min over all subsets S of {0,1,...,len(nums)-1} of |(sum of nums[i] for i in S) - goal|. The empty subset S is allowed and its sum is 0. This is the minimum possible absolute difference between goal and the sum of a subsequence of nums.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r → r.val = minAbsDiff nums goal.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r → r.val = minAbsDiff nums goal.val) := by
  sorry

/-- For every nums and goal satisfying the preconditions, min_abs_difference(nums, goal) returns a result r (an Ok result); it never fails, panics, overflows, or accesses out of bounds.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∃ r, min_abs_difference nums goal = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∃ r, min_abs_difference nums goal = ok r) := by
  sorry

/-- Whenever min_abs_difference(nums, goal) returns a result r, there exists a subset S of {0,1,...,len(nums)-1} (possibly empty) such that |(sum of nums[i] for i in S) - goal| = r.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      ∃ S : Finset (Fin nums.val.length), |subsetSum nums S - goal.val| = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      ∃ S : Finset (Fin nums.val.length), |subsetSum nums S - goal.val| = r.val) := by
  sorry

/-- Whenever min_abs_difference(nums, goal) returns a result r, for every subset S of {0,1,...,len(nums)-1} (possibly empty), r <= |(sum of nums[i] for i in S) - goal|.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      ∀ S : Finset (Fin nums.val.length), r.val ≤ |subsetSum nums S - goal.val| := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      ∀ S : Finset (Fin nums.val.length), r.val ≤ |subsetSum nums S - goal.val|) := by
  sorry

/-- Whenever min_abs_difference(nums, goal) returns a result r, r = 0 if and only if there exists a subset S of {0,1,...,len(nums)-1} (possibly empty) such that the sum of nums[i] for i in S equals goal.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      (r.val = 0 ↔ ∃ S : Finset (Fin nums.val.length), subsetSum nums S = goal.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      (r.val = 0 ↔ ∃ S : Finset (Fin nums.val.length), subsetSum nums S = goal.val)) := by
  sorry

/-- For every two goals g1 and g2 with -10^9 <= g1 <= 10^9 and -10^9 <= g2 <= 10^9, whenever min_abs_difference(nums, g1) returns r1 and min_abs_difference(nums, g2) returns r2, we have |r1 - r2| <= |g1 - g2|.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7. -/
theorem spec_6 (nums : Slice Std.I64) (g1 g2 : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_g1_lo : -1000000000 ≤ g1.val) (h_g1_hi : g1.val ≤ 1000000000)
    (h_g2_lo : -1000000000 ≤ g2.val) (h_g2_hi : g2.val ≤ 1000000000) :
    ∀ r1 r2, min_abs_difference nums g1 = ok r1 → min_abs_difference nums g2 = ok r2 →
      |r1.val - r2.val| ≤ |g1.val - g2.val| := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (g1 g2 : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_g1_lo : -1000000000 ≤ g1.val) (h_g1_hi : g1.val ≤ 1000000000)
    (h_g2_lo : -1000000000 ≤ g2.val) (h_g2_hi : g2.val ≤ 1000000000), ∀ r1 r2, min_abs_difference nums g1 = ok r1 → min_abs_difference nums g2 = ok r2 →
      |r1.val - r2.val| ≤ |g1.val - g2.val|) := by
  sorry

/-- Define neg(nums) to be the slice of length len(nums) with neg(nums)[i] = -nums[i] for each i. Whenever min_abs_difference(nums, goal) returns r and min_abs_difference(neg(nums), -goal) returns r', we have r = r'.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_7 (nums nums' : Slice Std.I64) (goal goal' : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_nums' : ivals nums' = negVals nums)
    (h_goal' : goal'.val = -goal.val) :
    ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal' = ok r' → r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (goal goal' : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_nums' : ivals nums' = negVals nums)
    (h_goal' : goal'.val = -goal.val), ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal' = ok r' → r.val = r'.val) := by
  sorry

/-- Let total = sum of nums[i] for 0 <= i < len(nums). Whenever min_abs_difference(nums, goal) returns a result r, r = min over all subsets S of {0,1,...,len(nums)-1} of |(sum of nums[i] for i in S) - (total - goal)|; the empty subset is allowed.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      r.val = minAbsDiff nums (totalSum nums - goal.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      r.val = minAbsDiff nums (totalSum nums - goal.val)) := by
  sorry

/-- Define rev(nums) to be the slice of length len(nums) with rev(nums)[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Whenever min_abs_difference(nums, goal) returns r and min_abs_difference(rev(nums), goal) returns r', we have r = r'.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_9 (nums nums' : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_nums' : ivals nums' = revVals nums) :
    ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_nums' : ivals nums' = revVals nums), ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever min_abs_difference(nums, goal) returns a result r, if len(nums) = 1 then r = min(|goal|, |nums[0] - goal|).
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_10 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r → nums.val.length = 1 →
      r.val = min |goal.val| |entry nums 0 - goal.val| := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r → nums.val.length = 1 →
      r.val = min |goal.val| |entry nums 0 - goal.val|) := by
  sorry

/-- Whenever min_abs_difference(nums, goal) returns a result r, if every element nums[i] is 0, then r = |goal|.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_11 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      (∀ i : Fin nums.val.length, (nums.val.get i).val = 0) → r.val = |goal.val| := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      (∀ i : Fin nums.val.length, (nums.val.get i).val = 0) → r.val = |goal.val|) := by
  sorry

/-- Whenever min_abs_difference(nums, goal) returns a result r, if every nums[i] >= 0 and goal >= total, where total = sum of nums[i] for 0 <= i < len(nums), then r = goal - total.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_12 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      (∀ i : Fin nums.val.length, 0 ≤ (nums.val.get i).val) →
      totalSum nums ≤ goal.val → r.val = goal.val - totalSum nums := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      (∀ i : Fin nums.val.length, 0 ≤ (nums.val.get i).val) →
      totalSum nums ≤ goal.val → r.val = goal.val - totalSum nums) := by
  sorry

/-- Whenever min_abs_difference(nums, goal) returns a result r, if every nums[i] >= 0 and goal <= 0, then r = -goal.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_13 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      (∀ i : Fin nums.val.length, 0 ≤ (nums.val.get i).val) →
      goal.val ≤ 0 → r.val = -goal.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      (∀ i : Fin nums.val.length, 0 ≤ (nums.val.get i).val) →
      goal.val ≤ 0 → r.val = -goal.val) := by
  sorry

/-- For any permutation p of {0,1,...,len(nums)-1}, define perm(nums) by perm(nums)[i] = nums[p(i)] for 0 <= i < len(nums). Whenever min_abs_difference(nums, goal) returns r and min_abs_difference(perm(nums), goal) returns r', we have r = r'.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_14 (nums nums' : Slice Std.I64) (goal : Std.I64)
    (p : Equiv.Perm (Fin nums.val.length))
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_perm : ivals nums' = permVals nums p) :
    ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal = ok r' → r.val = r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (goal : Std.I64)
    (p : Equiv.Perm (Fin nums.val.length))
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_perm : ivals nums' = permVals nums p), ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal = ok r' → r.val = r'.val) := by
  sorry

/-- Let P be the sum of all positive nums[i], and let N be the sum of all negative nums[i] (so N <= 0). Whenever min_abs_difference(nums, goal) returns a result r, if goal >= P then r = goal - P, and if goal <= N then r = N - goal.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_15 (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000) :
    ∀ r, min_abs_difference nums goal = ok r →
      (posSum nums ≤ goal.val → r.val = goal.val - posSum nums) ∧
      (goal.val ≤ negSum nums → r.val = negSum nums - goal.val) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (goal : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000), ∀ r, min_abs_difference nums goal = ok r →
      (posSum nums ≤ goal.val → r.val = goal.val - posSum nums) ∧
      (goal.val ≤ negSum nums → r.val = negSum nums - goal.val)) := by
  sorry

/-- For any index k with 0 <= k < len(nums) and nums[k] = 0, if len(nums) > 1 let nums' be the slice obtained by deleting index k. Whenever min_abs_difference(nums, goal) returns r and min_abs_difference(nums', goal) returns r', we have r = r'.
  Preconditions: len(nums) >= 1; len(nums) <= 40; for every i with 0 <= i < len(nums), -10^7 <= nums[i] <= 10^7; -10^9 <= goal <= 10^9. -/
theorem spec_16 (nums nums' : Slice Std.I64) (goal : Std.I64)
    (k : Fin nums.val.length)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_zero : (nums.val.get k).val = 0)
    (h_len_gt : 1 < nums.val.length)
    (h_del : ivals nums' = delVals nums k) :
    ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal = ok r' → r.val = r'.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (goal : Std.I64)
    (k : Fin nums.val.length)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 40)
    (h_elems : ∀ i : Fin nums.val.length,
      -10000000 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000000)
    (h_goal_lo : -1000000000 ≤ goal.val) (h_goal_hi : goal.val ≤ 1000000000)
    (h_zero : (nums.val.get k).val = 0)
    (h_len_gt : 1 < nums.val.length)
    (h_del : ivals nums' = delVals nums k), ∀ r r', min_abs_difference nums goal = ok r →
      min_abs_difference nums' goal = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.MinAbsDifference
