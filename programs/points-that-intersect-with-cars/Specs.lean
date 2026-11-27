import Aegis.NumberOfPoints.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPoints.number_of_points`

LeetCode problem `points-that-intersect-with-cars`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfPoints

noncomputable section

def start (nums : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
  (nums.val[i]!).val[0]!.val

def stop (nums : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
  (nums.val[i]!).val[1]!.val

def totalLength (nums : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
  ∑ i ∈ Finset.range nums.val.length, (stop nums i - start nums i + 1)

def Covered (nums : Slice (alloc.vec.Vec Std.I64)) (x : ℤ) : Prop :=
  ∃ i : ℕ, i < nums.val.length ∧ start nums i ≤ x ∧ x ≤ stop nums i

def coveredSet (nums : Slice (alloc.vec.Vec Std.I64)) : Set ℤ :=
  {x | Covered nums x}

def minStart (nums : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
  match (List.range nums.val.length).map (start nums) with
  | [] => 0
  | a :: l => l.foldl min a

def maxStop (nums : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
  match (List.range nums.val.length).map (stop nums) with
  | [] => 0
  | a :: l => l.foldl max a

/-- Let a point x (an integer) be covered by nums if there exists an index i with 0 ≤ i < len(nums) and nums[i][0] ≤ x ≤ nums[i][1]. The function returns a result r and r is the number of distinct integers x that are covered by nums. Equivalently, r = |{ x ∈ ℤ : ∃ i, 0 ≤ i < len(nums) ∧ nums[i][0] ≤ x ≤ nums[i][1] }|. Endpoints are included, and a point covered by several cars is counted once.
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_1 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100) :
    ∃ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r ∧
      r.val = ((coveredSet nums).ncard : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100), ∃ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r ∧
      r.val = ((coveredSet nums).ncard : ℤ)) := by
  sorry

/-- For every input nums satisfying the precondition, the function returns a result r; it does not fail by arithmetic overflow, out-of-bounds indexing, or panic.
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_2 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100) :
    ∃ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100), ∃ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, 1 ≤ r ≤ 100.
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_3 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100) :
    ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      1 ≤ r.val ∧ r.val ≤ 100 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100), ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      1 ≤ r.val ∧ r.val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, for every index i with 0 ≤ i < len(nums), the integer nums[i][0] is covered by nums, and r ≥ nums[i][1] - nums[i][0] + 1.
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_4 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100) :
    ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      ∀ (i : ℕ), i < nums.val.length →
        Covered nums (start nums i) ∧ stop nums i - start nums i + 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100), ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      ∀ (i : ℕ), i < nums.val.length →
        Covered nums (start nums i) ∧ stop nums i - start nums i + 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, r ≤ Σ_{i=0}^{len(nums)-1} (nums[i][1] - nums[i][0] + 1).
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_5 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100) :
    ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val ≤ totalLength nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100), ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val ≤ totalLength nums) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, r ≤ (max_{0 ≤ i < len(nums)} nums[i][1]) - (min_{0 ≤ i < len(nums)} nums[i][0]) + 1.
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_6 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100) :
    ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val ≤ maxStop nums - minStart nums + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100), ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val ≤ maxStop nums - minStart nums + 1) := by
  sorry

/-- Suppose that for every two distinct indices i and j with 0 ≤ i < len(nums) and 0 ≤ j < len(nums), either nums[i][1] < nums[j][0] or nums[j][1] < nums[i][0]. Then whenever the function returns a result r, r = Σ_{i=0}^{len(nums)-1} (nums[i][1] - nums[i][0] + 1).
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_7 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hdisjoint : ∀ (i j : ℕ), i < nums.val.length → j < nums.val.length → i ≠ j →
      stop nums i < start nums j ∨ stop nums j < start nums i) :
    ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val = totalLength nums := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hdisjoint : ∀ (i j : ℕ), i < nums.val.length → j < nums.val.length → i ≠ j →
      stop nums i < start nums j ∨ stop nums j < start nums i), ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val = totalLength nums) := by
  sorry

/-- Suppose there exists an integer p such that for every index i with 0 ≤ i < len(nums), nums[i][0] ≤ p ≤ nums[i][1]. Then whenever the function returns a result r, r = (max_{0 ≤ i < len(nums)} nums[i][1]) - (min_{0 ≤ i < len(nums)} nums[i][0]) + 1.
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_8 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hcommon : ∃ p : ℤ, ∀ (i : ℕ), i < nums.val.length → start nums i ≤ p ∧ p ≤ stop nums i) :
    ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val = maxStop nums - minStart nums + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hcommon : ∃ p : ℤ, ∀ (i : ℕ), i < nums.val.length → start nums i ≤ p ∧ p ≤ stop nums i), ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val = maxStop nums - minStart nums + 1) := by
  sorry

/-- Whenever the function returns a result r on nums and a result r' on nums', we have r = r'.
  Preconditions: Both nums and nums' satisfy: 1 ≤ len(nums) ≤ 100 and 1 ≤ len(nums') ≤ 100; for every i in the appropriate range, len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100, and similarly for nums'. For an integer x and a list z, say x is covered by z if there is an index i with 0 ≤ i < len(z) and z[i][0] ≤ x ≤ z[i][1]. Require that for every integer x, x is covered by nums if and only if x is covered by nums'. -/
theorem spec_9 (nums nums' : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hlen_lower' : 1 ≤ nums'.val.length) (hlen_upper' : nums'.val.length ≤ 100)
    (hcar_len' : ∀ (i : ℕ) (hi : i < nums'.val.length), (nums'.val[i]).val.length = 2)
    (hcar_range' : ∀ (i : ℕ), i < nums'.val.length →
      1 ≤ start nums' i ∧ start nums' i ≤ stop nums' i ∧ stop nums' i ≤ 100)
    (hsame : ∀ x : ℤ, Covered nums x ↔ Covered nums' x) :
    ∀ r r' : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      Aegis.NumberOfPoints.number_of_points nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hlen_lower' : 1 ≤ nums'.val.length) (hlen_upper' : nums'.val.length ≤ 100)
    (hcar_len' : ∀ (i : ℕ) (hi : i < nums'.val.length), (nums'.val[i]).val.length = 2)
    (hcar_range' : ∀ (i : ℕ), i < nums'.val.length →
      1 ≤ start nums' i ∧ start nums' i ≤ stop nums' i ∧ stop nums' i ≤ 100)
    (hsame : ∀ x : ℤ, Covered nums x ↔ Covered nums' x), ∀ r r' : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      Aegis.NumberOfPoints.number_of_points nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r on nums and a result r' on nums', r' = r + |{ x ∈ ℤ : a ≤ x ≤ b and x is not covered by nums }|, where x is covered by nums if there exists i with 0 ≤ i < len(nums) and nums[i][0] ≤ x ≤ nums[i][1].
  Preconditions: nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. Also len(nums) < 100. Let a and b be integers with 1 ≤ a ≤ b ≤ 100. Let nums' be the input satisfying the same preconditions obtained by appending the interval [a,b] to nums: len(nums') = len(nums)+1, nums'[i] = nums[i] for 0 ≤ i < len(nums), and nums'[len(nums)] = [a,b]. -/
theorem spec_10 (nums nums' : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hlen_lt : nums.val.length < 100)
    (ha_lower : 1 ≤ a) (hab : a ≤ b) (hb_upper : b ≤ 100)
    (hlen_lower' : 1 ≤ nums'.val.length) (hlen_upper' : nums'.val.length ≤ 100)
    (hcar_len' : ∀ (i : ℕ) (hi : i < nums'.val.length), (nums'.val[i]).val.length = 2)
    (hcar_range' : ∀ (i : ℕ), i < nums'.val.length →
      1 ≤ start nums' i ∧ start nums' i ≤ stop nums' i ∧ stop nums' i ≤ 100)
    (happend : ∃ v : alloc.vec.Vec Std.I64,
      nums'.val = nums.val ++ [v] ∧ v.val.map IScalar.val = [a, b]) :
    ∀ r r' : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      Aegis.NumberOfPoints.number_of_points nums' = ok r' →
        r'.val = r.val + (({x : ℤ | a ≤ x ∧ x ≤ b ∧ ¬ Covered nums x}).ncard : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hlen_lt : nums.val.length < 100)
    (ha_lower : 1 ≤ a) (hab : a ≤ b) (hb_upper : b ≤ 100)
    (hlen_lower' : 1 ≤ nums'.val.length) (hlen_upper' : nums'.val.length ≤ 100)
    (hcar_len' : ∀ (i : ℕ) (hi : i < nums'.val.length), (nums'.val[i]).val.length = 2)
    (hcar_range' : ∀ (i : ℕ), i < nums'.val.length →
      1 ≤ start nums' i ∧ start nums' i ≤ stop nums' i ∧ stop nums' i ≤ 100)
    (happend : ∃ v : alloc.vec.Vec Std.I64,
      nums'.val = nums.val ++ [v] ∧ v.val.map IScalar.val = [a, b]), ∀ r r' : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      Aegis.NumberOfPoints.number_of_points nums' = ok r' →
        r'.val = r.val + (({x : ℤ | a ≤ x ∧ x ≤ b ∧ ¬ Covered nums x}).ncard : ℤ)) := by
  sorry

/-- If for every index i with 0 ≤ i < len(nums), nums[i][0] = nums[i][1], then whenever the function returns a result r, r = |{ nums[i][0] : 0 ≤ i < len(nums) }|, the number of distinct car positions.
  Preconditions: The input nums satisfies: 1 ≤ len(nums) ≤ 100; for every integer i with 0 ≤ i < len(nums), len(nums[i]) = 2 and 1 ≤ nums[i][0] ≤ nums[i][1] ≤ 100. -/
theorem spec_11 (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hpoints : ∀ (i : ℕ), i < nums.val.length → start nums i = stop nums i) :
    ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val = (({x : ℤ | ∃ i : ℕ, i < nums.val.length ∧ start nums i = x}).ncard : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
    (hcar_len : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val.length = 2)
    (hcar_range : ∀ (i : ℕ), i < nums.val.length →
      1 ≤ start nums i ∧ start nums i ≤ stop nums i ∧ stop nums i ≤ 100)
    (hpoints : ∀ (i : ℕ), i < nums.val.length → start nums i = stop nums i), ∀ r : Std.I64, Aegis.NumberOfPoints.number_of_points nums = ok r →
      r.val = (({x : ℤ | ∃ i : ℕ, i < nums.val.length ∧ start nums i = x}).ncard : ℤ)) := by
  sorry

end

end AegisSpec.NumberOfPoints
