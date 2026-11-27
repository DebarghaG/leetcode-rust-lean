import Aegis.MinMoves2.Code.Funs

/-!
# Specifications of `Aegis.MinMoves2.min_moves2`

LeetCode problem `minimum-moves-to-equal-array-elements-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinMoves2

namespace AegisSpec.MinMoves2

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def InRange (xs : List ℤ) : Prop := ∀ a ∈ xs, -(10 : ℤ) ^ 9 ≤ a ∧ a ≤ (10 : ℤ) ^ 9

def Nondecreasing (xs : List ℤ) : Prop := xs.Pairwise (· ≤ ·)

def cost (xs : List ℤ) (x : ℤ) : ℤ := (xs.map (fun a => |a - x|)).sum

def IsMinCost (xs : List ℤ) (r : ℤ) : Prop :=
  (∀ x : ℤ, r ≤ cost xs x) ∧ ∃ x : ℤ, cost xs x = r

def countLt (xs : List ℤ) (x : ℤ) : ℕ := (xs.filter (fun a => decide (a < x))).length

def countGt (xs : List ℤ) (x : ℤ) : ℕ := (xs.filter (fun a => decide (x < a))).length

def listMin : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl (fun acc a => if a < acc then a else acc) x

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl (fun acc a => if acc < a then a else acc) x

def halfSum (sn : List ℤ) : ℤ :=
  ((List.range (sn.length / 2)).map
      (fun i => sn.getD (sn.length - 1 - i) 0 - sn.getD i 0)).sum

/-- Let C(x) = sum_{i=0}^{len(nums)-1} |nums[i] - x|, with ordinary integer absolute value. The function returns a result r and r = min_{x is an integer} C(x).
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and the minimum over all integers x of sum_{i=0}^{len(nums)-1} |nums[i] - x| is at most 2^31 - 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums))
    (hmin_le : ∃ x : ℤ, cost (vals nums) x ≤ (2 : ℤ) ^ 31 - 1) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧ IsMinCost (vals nums) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums))
    (hmin_le : ∃ x : ℤ, cost (vals nums) x ≤ (2 : ℤ) ^ 31 - 1), ∃ r : Std.I64, min_moves2 nums = ok r ∧ IsMinCost (vals nums) r.val) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, overflow, or out-of-bounds access).
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and, for every j with 0 <= j < len(nums), r <= sum_{i=0}^{len(nums)-1} |nums[i] - nums[j]|.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ (j : ℕ) (hj : j < (vals nums).length),
        r.val ≤ cost (vals nums) ((vals nums).get ⟨j, hj⟩) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ (j : ℕ) (hj : j < (vals nums).length),
        r.val ≤ cost (vals nums) ((vals nums).get ⟨j, hj⟩)) := by
  sorry

/-- Let lo = min_{0 <= i < len(nums)} nums[i] and hi = max_{0 <= i < len(nums)} nums[i]. The function returns a result r and r >= hi - lo.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      r.val ≥ listMax (vals nums) - listMin (vals nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      r.val ≥ listMax (vals nums) - listMin (vals nums)) := by
  sorry

/-- The function returns a result r and there exists an index k with 0 <= k < len(nums) such that r = sum_{i=0}^{len(nums)-1} |nums[i] - nums[k]|.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∃ (k : ℕ) (hk : k < (vals nums).length),
        r.val = cost (vals nums) ((vals nums).get ⟨k, hk⟩) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∃ (k : ℕ) (hk : k < (vals nums).length),
        r.val = cost (vals nums) ((vals nums).get ⟨k, hk⟩)) := by
  sorry

/-- Let L(x) = #{i : 0 <= i < len(nums) and nums[i] < x} and G(x) = #{i : 0 <= i < len(nums) and nums[i] > x}. The function returns a result r and, for every integer x, r = sum_{i=0}^{len(nums)-1} |nums[i] - x| if and only if L(x) <= floor(len(nums)/2) and G(x) <= floor(len(nums)/2).
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ x : ℤ, (r.val = cost (vals nums) x) ↔
        (countLt (vals nums) x ≤ (vals nums).length / 2 ∧
          countGt (vals nums) x ≤ (vals nums).length / 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ x : ℤ, (r.val = cost (vals nums) x) ↔
        (countLt (vals nums) x ≤ (vals nums).length / 2 ∧
          countGt (vals nums) x ≤ (vals nums).length / 2)) := by
  sorry

/-- The function returns a result r on nums. For every slice ys of length len(nums) that is a permutation of nums (that is, ys has the same multiset of entries as nums), the function returns a result r_y on ys and r_y = r.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ ys : Slice Std.I64, List.Perm (vals ys) (vals nums) →
        ∃ r_y : Std.I64, min_moves2 ys = ok r_y ∧ r_y.val = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ ys : Slice Std.I64, List.Perm (vals ys) (vals nums) →
        ∃ r_y : Std.I64, min_moves2 ys = ok r_y ∧ r_y.val = r.val) := by
  sorry

/-- The function returns a result r on nums. Let neg(nums) be the slice of length len(nums) with neg(nums)[i] = -nums[i]. The function returns a result r_neg on neg(nums) and r_neg = r.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ ys : Slice Std.I64, vals ys = (vals nums).map (fun a => -a) →
        ∃ r_neg : Std.I64, min_moves2 ys = ok r_neg ∧ r_neg.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ ys : Slice Std.I64, vals ys = (vals nums).map (fun a => -a) →
        ∃ r_neg : Std.I64, min_moves2 ys = ok r_neg ∧ r_neg.val = r.val) := by
  sorry

/-- The function returns a result r on nums. For every integer c such that -10^9 <= nums[i] + c <= 10^9 for all i with 0 <= i < len(nums), let shifted(nums,c) be the slice with shifted(nums,c)[i] = nums[i] + c. The function returns a result r_c on shifted(nums,c) and r_c = r.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ (c : ℤ) (ys : Slice Std.I64),
        (∀ a ∈ vals nums, -(10 : ℤ) ^ 9 ≤ a + c ∧ a + c ≤ (10 : ℤ) ^ 9) →
        vals ys = (vals nums).map (fun a => a + c) →
        ∃ r_c : Std.I64, min_moves2 ys = ok r_c ∧ r_c.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ (c : ℤ) (ys : Slice Std.I64),
        (∀ a ∈ vals nums, -(10 : ℤ) ^ 9 ≤ a + c ∧ a + c ≤ (10 : ℤ) ^ 9) →
        vals ys = (vals nums).map (fun a => a + c) →
        ∃ r_c : Std.I64, min_moves2 ys = ok r_c ∧ r_c.val = r.val) := by
  sorry

/-- The function returns a result r on nums. For every positive integer k such that -10^9 <= k*nums[i] <= 10^9 for all i with 0 <= i < len(nums), let scaled(nums,k) be the slice with scaled(nums,k)[i] = k*nums[i]. The function returns a result r_k on scaled(nums,k) and r_k = k*r.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ (k : ℤ) (ys : Slice Std.I64), 0 < k →
        (∀ a ∈ vals nums, -(10 : ℤ) ^ 9 ≤ k * a ∧ k * a ≤ (10 : ℤ) ^ 9) →
        vals ys = (vals nums).map (fun a => k * a) →
        ∃ r_k : Std.I64, min_moves2 ys = ok r_k ∧ r_k.val = k * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ (k : ℤ) (ys : Slice Std.I64), 0 < k →
        (∀ a ∈ vals nums, -(10 : ℤ) ^ 9 ≤ k * a ∧ k * a ≤ (10 : ℤ) ^ 9) →
        vals ys = (vals nums).map (fun a => k * a) →
        ∃ r_k : Std.I64, min_moves2 ys = ok r_k ∧ r_k.val = k * r.val) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j]. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums))
    (hall : ∀ a ∈ vals nums, ∀ b ∈ vals nums, a = b) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums))
    (hall : ∀ a ∈ vals nums, ∀ b ∈ vals nums, a = b), ∃ r : Std.I64, min_moves2 nums = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r > 0.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; and there exist i and j with 0 <= i < len(nums), 0 <= j < len(nums), and nums[i] != nums[j]. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums))
    (hne : ∃ a ∈ vals nums, ∃ b ∈ vals nums, a ≠ b) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧ 0 < r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums))
    (hne : ∃ a ∈ vals nums, ∃ b ∈ vals nums, a ≠ b), ∃ r : Std.I64, min_moves2 nums = ok r ∧ 0 < r.val) := by
  sorry

/-- Let sn be a nondecreasing rearrangement of nums and n = len(nums). The function returns a result r and r = sum_{i=0}^{floor(n/2)-1} (sn[n-1-i] - sn[i]).
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)) :
    ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ sn : List ℤ, List.Perm sn (vals nums) → Nondecreasing sn →
        r.val = halfSum sn := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (vals nums).length)
    (hlen_le : (vals nums).length ≤ 10 ^ 5)
    (hrange : InRange (vals nums)), ∃ r : Std.I64, min_moves2 nums = ok r ∧
      ∀ sn : List ℤ, List.Perm sn (vals nums) → Nondecreasing sn →
        r.val = halfSum sn) := by
  sorry

end AegisSpec.MinMoves2
