import Aegis.MaxArrayValue.Code.Funs

/-!
# Specifications of `Aegis.MaxArrayValue.max_array_value`

LeetCode problem `largest-element-in-an-array-after-merge-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxArrayValue

namespace AegisSpec.MaxArrayValue

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def elem (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def segSum (nums : Slice Std.I64) (a b : Nat) : Int := ((vals nums).drop a).take (b + 1 - a) |>.sum

def Mergeable (nums : Slice Std.I64) (k : Nat) : Prop :=
  k < (Slice.len nums).val ∧ ∀ i : Nat, i < k → elem nums i ≤ segSum nums (i + 1) k

noncomputable def maxMergeable (nums : Slice Std.I64) : Nat :=
  @Nat.findGreatest (fun k => Mergeable nums k) (Classical.decPred _) (Slice.len nums).val

def MergeStep (l₁ l₂ : List Int) : Prop :=
  ∃ (pre post : List Int) (a b : Int),
    a ≤ b ∧ l₁ = pre ++ a :: b :: post ∧ l₂ = pre ++ (a + b) :: post

def Reaches : List Int → List Int → Prop := Relation.ReflTransGen MergeStep

def CanAppear (nums : Slice Std.I64) (v : Int) : Prop :=
  ∃ l : List Int, Reaches (vals nums) l ∧ v ∈ l

def IsMaxAppearing (nums : Slice Std.I64) (v : Int) : Prop :=
  CanAppear nums v ∧ ∀ w : Int, CanAppear nums w → w ≤ v

/-- Let n = len(nums). Say that a prefix ending at k is mergeable when 0 <= k < n and for every i with 0 <= i < k, nums[i] <= sum_{t=i+1}^{k} nums[t] (this condition is vacuous for k = 0). Let k0 be the largest such index k. The function returns a result r, and r = sum_{t=0}^{k0} nums[t]. Equivalently, r is the largest value of an element that can appear in the array after any finite sequence of the allowed merge operations.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∃ r : Std.I64, max_array_value nums = ok r ∧ r.val = segSum nums 0 (maxMergeable nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∃ r : Std.I64, max_array_value nums = ok r ∧ r.val = segSum nums 0 (maxMergeable nums)) := by
  sorry

/-- The function returns a result r on every input satisfying the preconditions; it does not overflow, panic, or access an out-of-bounds index.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∃ r : Std.I64, max_array_value nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∃ r : Std.I64, max_array_value nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r >= nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      ∀ i : Nat, i < (Slice.len nums).val → elem nums i ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      ∀ i : Nat, i < (Slice.len nums).val → elem nums i ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{t=0}^{len(nums)-1} nums[t].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      r.val ≤ segSum nums 0 ((Slice.len nums).val - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      r.val ≤ segSum nums 0 ((Slice.len nums).val - 1)) := by
  sorry

/-- Whenever the function returns a result r, there exists an index k with 0 <= k < len(nums) such that r = sum_{t=0}^{k} nums[t].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      ∃ k : Nat, k < (Slice.len nums).val ∧ r.val = segSum nums 0 k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      ∃ k : Nat, k < (Slice.len nums).val ∧ r.val = segSum nums 0 k) := by
  sorry

/-- Whenever the function returns a result r, there exists an index k with 0 <= k < len(nums) such that: (1) for every i with 0 <= i < k, nums[i] <= sum_{t=i+1}^{k} nums[t]; (2) r = sum_{t=0}^{k} nums[t]; and (3) applying the allowed operation repeatedly inside the prefix 0..k collapses that prefix into a single element equal to r while leaving all elements after position k unchanged.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      ∃ k : Nat, k < (Slice.len nums).val ∧
        Mergeable nums k ∧
        r.val = segSum nums 0 k ∧
        Reaches (vals nums) (r.val :: (vals nums).drop (k + 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      ∃ k : Nat, k < (Slice.len nums).val ∧
        Mergeable nums k ∧
        r.val = segSum nums 0 k ∧
        Reaches (vals nums) (r.val :: (vals nums).drop (k + 1))) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(nums) such that for all i with 0 <= i < k, nums[i] <= sum_{t=i+1}^{k} nums[t], we have sum_{t=0}^{k} nums[t] <= r.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      ∀ k : Nat, k < (Slice.len nums).val →
        (∀ i : Nat, i < k → elem nums i ≤ segSum nums (i + 1) k) →
        segSum nums 0 k ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      ∀ k : Nat, k < (Slice.len nums).val →
        (∀ i : Nat, i < k → elem nums i ≤ segSum nums (i + 1) k) →
        segSum nums 0 k ≤ r.val) := by
  sorry

/-- Whenever len(nums) = 1 and the function returns a result r, r = nums[0].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      (Slice.len nums).val = 1 → r.val = elem nums 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      (Slice.len nums).val = 1 → r.val = elem nums 0) := by
  sorry

/-- Whenever len(nums) = 2 and the function returns a result r, if nums[0] <= nums[1] then r = nums[0] + nums[1], otherwise r = nums[0].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      (Slice.len nums).val = 2 →
        (elem nums 0 ≤ elem nums 1 → r.val = elem nums 0 + elem nums 1) ∧
        (elem nums 1 < elem nums 0 → r.val = elem nums 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      (Slice.len nums).val = 2 →
        (elem nums 0 ≤ elem nums 1 → r.val = elem nums 0 + elem nums 1) ∧
        (elem nums 1 < elem nums 0 → r.val = elem nums 0)) := by
  sorry

/-- Whenever for every i with 0 <= i < len(nums)-1, nums[i] <= sum_{t=i+1}^{len(nums)-1} nums[t], the returned result r equals sum_{t=0}^{len(nums)-1} nums[t].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      (∀ i : Nat, i < (Slice.len nums).val - 1 →
        elem nums i ≤ segSum nums (i + 1) ((Slice.len nums).val - 1)) →
      r.val = segSum nums 0 ((Slice.len nums).val - 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      (∀ i : Nat, i < (Slice.len nums).val - 1 →
        elem nums i ≤ segSum nums (i + 1) ((Slice.len nums).val - 1)) →
      r.val = segSum nums 0 ((Slice.len nums).val - 1)) := by
  sorry

/-- Whenever len(nums) >= 2 and nums[0] > sum_{t=1}^{len(nums)-1} nums[t], the returned result r equals nums[0].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      2 ≤ (Slice.len nums).val →
        segSum nums 1 ((Slice.len nums).val - 1) < elem nums 0 → r.val = elem nums 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      2 ≤ (Slice.len nums).val →
        segSum nums 1 ((Slice.len nums).val - 1) < elem nums 0 → r.val = elem nums 0) := by
  sorry

/-- Whenever for every i with 0 <= i < len(nums)-1, nums[i] > nums[i+1], the returned result r equals nums[0].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000) :
    ∀ r : Std.I64, max_array_value nums = ok r →
      (∀ i : Nat, i < (Slice.len nums).val - 1 → elem nums (i + 1) < elem nums i) →
      r.val = elem nums 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_le : (Slice.len nums).val ≤ 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000), ∀ r : Std.I64, max_array_value nums = ok r →
      (∀ i : Nat, i < (Slice.len nums).val - 1 → elem nums (i + 1) < elem nums i) →
      r.val = elem nums 0) := by
  sorry

/-- Let nums' be any slice obtained by appending one more element x to nums, where 1 <= x <= 1000000. If the function returns r on nums and returns r' on nums', then r' >= r.
  Preconditions: len(nums) >= 1, len(nums) < 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_13 (nums nums' : Slice Std.I64) (x : Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_lt : (Slice.len nums).val < 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000)
    (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 1000000)
    (happend : nums'.val = nums.val ++ [x]) :
    ∀ r r' : Std.I64, max_array_value nums = ok r → max_array_value nums' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (x : Std.I64)
    (hlen_pos : 1 ≤ (Slice.len nums).val) (hlen_lt : (Slice.len nums).val < 100000)
    (helem : ∀ i : Nat, i < (Slice.len nums).val → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000)
    (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 1000000)
    (happend : nums'.val = nums.val ++ [x]), ∀ r r' : Std.I64, max_array_value nums = ok r → max_array_value nums' = ok r' →
      r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxArrayValue
