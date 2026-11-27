import Aegis.PivotIndex.Code.Funs

/-!
# Specifications of `Aegis.PivotIndex.pivot_index`

LeetCode problem `find-pivot-index`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PivotIndex

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def sumUpTo (nums : Slice Std.I64) (k : Nat) : Int := ((vals nums).take k).sum

def sumFrom (nums : Slice Std.I64) (k : Nat) : Int := ((vals nums).drop k).sum

def leftSum (nums : Slice Std.I64) (i : Nat) : Int := sumUpTo nums i

def rightSum (nums : Slice Std.I64) (i : Nat) : Int := sumFrom nums (i + 1)

def IsPivot (nums : Slice Std.I64) (i : Nat) : Prop :=
  i < (vals nums).length ∧ leftSum nums i = rightSum nums i

def ValidInput (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧
    nums.val.length ≤ 10 ^ 4 ∧
      ∀ j : Nat, j < nums.val.length → -1000 ≤ (nums.val[j]!).val ∧ (nums.val[j]!).val ≤ 1000

/-- Let n = len(nums). For 0 <= i <= n, define L(i) = sum of nums[j] over all j with 0 <= j < i, and R(i) = sum of nums[j] over all j with i < j < n; an empty sum is 0. The function returns a result r (it does not fail), and r is the leftmost pivot index: if P = { i | 0 <= i < n and L(i) = R(i) } is nonempty, then r = min(P); if P is empty, then r = -1.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_1 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∃ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r ∧
        (∀ i : Nat, IsPivot nums i → ∃ i₀ : Nat, IsPivot nums i₀ ∧ i₀ ≤ i ∧ r.val = (i₀ : Int)) ∧
        ((∀ i : Nat, ¬ IsPivot nums i) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∃ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r ∧
        (∀ i : Nat, IsPivot nums i → ∃ i₀ : Nat, IsPivot nums i₀ ∧ i₀ ≤ i ∧ r.val = (i₀ : Int)) ∧
        ((∀ i : Nat, ¬ IsPivot nums i) → r.val = -1)) := by
  sorry

/-- The function returns a result r; that is, the call does not fail for any input satisfying the preconditions.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_2 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∃ r : Std.I64, Aegis.PivotIndex.pivot_index nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∃ r : Std.I64, Aegis.PivotIndex.pivot_index nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r < len(nums).
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_3 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r is a pivot index: 0 <= r < len(nums) and sum_{j=0}^{r-1} nums[j] = sum_{j=r+1}^{len(nums)-1} nums[j], where an empty sum is 0.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_4 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        r.val ≠ -1 →
          0 ≤ r.val ∧
            r.val < (nums.val.length : Int) ∧
              leftSum nums r.val.toNat = rightSum nums r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        r.val ≠ -1 →
          0 ≤ r.val ∧
            r.val < (nums.val.length : Int) ∧
              leftSum nums r.val.toNat = rightSum nums r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if for every i with 0 <= i < len(nums), sum_{j=0}^{i-1} nums[j] != sum_{j=i+1}^{len(nums)-1} nums[j], where an empty sum is 0.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_5 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        (r.val = -1 ↔
          ∀ i : Nat, i < nums.val.length → leftSum nums i ≠ rightSum nums i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        (r.val = -1 ↔
          ∀ i : Nat, i < nums.val.length → leftSum nums i ≠ rightSum nums i)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, no smaller index is a pivot: for every i with 0 <= i < r, sum_{j=0}^{i-1} nums[j] != sum_{j=i+1}^{len(nums)-1} nums[j], where an empty sum is 0.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_6 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        r.val ≠ -1 → ∀ i : Nat, i < r.val.toNat → leftSum nums i ≠ rightSum nums i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        r.val ≠ -1 → ∀ i : Nat, i < r.val.toNat → leftSum nums i ≠ rightSum nums i) := by
  sorry

/-- Whenever the function returns a result r, if sum_{j=1}^{len(nums)-1} nums[j] = 0 (the empty sum when len(nums) = 1 is 0), then r = 0.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_7 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r → sumFrom nums 1 = 0 → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r → sumFrom nums 1 = 0 → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if sum_{j=0}^{len(nums)-2} nums[j] = 0 (the empty sum when len(nums) = 1 is 0) and no i with 0 <= i < len(nums)-1 is a pivot index, then r = len(nums)-1.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_8 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        sumUpTo nums (nums.val.length - 1) = 0 →
          (∀ i : Nat, i < nums.val.length - 1 → leftSum nums i ≠ rightSum nums i) →
            r.val = (nums.val.length : Int) - 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        sumUpTo nums (nums.val.length - 1) = 0 →
          (∀ i : Nat, i < nums.val.length - 1 → leftSum nums i ≠ rightSum nums i) →
            r.val = (nums.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r with 0 <= r < len(nums), let total = sum_{j=0}^{len(nums)-1} nums[j] and let L = sum_{j=0}^{r-1} nums[j], with L = 0 if r = 0. Then 2 * L + nums[r] = total.
  Preconditions: 1 <= len(nums) <= 10^4 and for every j with 0 <= j < len(nums), -1000 <= nums[j] <= 1000. -/
theorem spec_9 (nums : Slice Std.I64) (hvalid : ValidInput nums) :
    ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        0 ≤ r.val →
          r.val < (nums.val.length : Int) →
            2 * leftSum nums r.val.toNat + (nums.val[r.val.toNat]!).val = sumFrom nums 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (hvalid : ValidInput nums), ∀ r : Std.I64,
      Aegis.PivotIndex.pivot_index nums = ok r →
        0 ≤ r.val →
          r.val < (nums.val.length : Int) →
            2 * leftSum nums r.val.toNat + (nums.val[r.val.toNat]!).val = sumFrom nums 0) := by
  sorry

end AegisSpec.PivotIndex
