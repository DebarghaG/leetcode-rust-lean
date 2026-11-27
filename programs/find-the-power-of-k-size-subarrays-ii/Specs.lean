import Aegis.ResultsArray.Code.Funs

/-!
# Specifications of `Aegis.ResultsArray.results_array`

LeetCode problem `find-the-power-of-k-size-subarrays-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ResultsArray

def getI64 (l : List Std.I64) (i : ℕ) : ℤ :=
  match l[i]? with
  | some x => x.val
  | none => 0

def numsGet (nums : Slice Std.I64) (i : ℕ) : ℤ := getI64 nums.val i

def resGet (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ := getI64 r.val i

def windows (nums : Slice Std.I64) (k : Std.I64) : ℕ :=
  nums.val.length + 1 - k.val.toNat

def lastIndex (k : Std.I64) (i : ℕ) : ℕ := i + (k.val.toNat - 1)

def consecutive (nums : Slice Std.I64) (k : Std.I64) (i : ℕ) : Prop :=
  ∀ j : ℕ, (i : ℤ) ≤ (j : ℤ) → (j : ℤ) < (i : ℤ) + k.val - 1 →
    numsGet nums (j + 1) = numsGet nums j + 1

/-- Whenever the function returns a result r, len(r) = n - k + 1 and for every integer i with 0 <= i < n - k + 1, r[i] is the power of the subarray nums[i..i+k-1]: if for every j with i <= j < i+k-1 we have nums[j+1] = nums[j] + 1, then r[i] = nums[i+k-1]; otherwise r[i] = -1.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      r.val.length = windows nums k ∧
      ∀ i : ℕ, i < windows nums k →
        (consecutive nums k i → resGet r i = numsGet nums (lastIndex k i)) ∧
        (¬ consecutive nums k i → resGet r i = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      r.val.length = windows nums k ∧
      ∀ i : ℕ, i < windows nums k →
        (consecutive nums k i → resGet r i = numsGet nums (lastIndex k i)) ∧
        (¬ consecutive nums k i → resGet r i = -1)) := by
  sorry

/-- On every input satisfying the preconditions, the function returns a result r; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∃ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), either r[i] = -1 or 1 <= r[i] <= 10^6.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length →
        resGet r i = -1 ∨ (1 ≤ resGet r i ∧ resGet r i ≤ 10 ^ 6) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length →
        resGet r i = -1 ∨ (1 ≤ resGet r i ∧ resGet r i ≤ 10 ^ 6)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and i < n - k + 1, r[i] != -1 if and only if for every j with i <= j < i+k-1 we have nums[j+1] = nums[j] + 1.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k →
        (resGet r i ≠ -1 ↔ consecutive nums k i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k →
        (resGet r i ≠ -1 ↔ consecutive nums k i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and i < n - k + 1, if r[i] != -1 then r[i] = nums[i+k-1] and for every t with 0 <= t < k we have nums[i+t] <= r[i].
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        resGet r i = numsGet nums (lastIndex k i) ∧
        ∀ t : ℕ, t < k.val.toNat → numsGet nums (i + t) ≤ resGet r i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        resGet r i = numsGet nums (lastIndex k i) ∧
        ∀ t : ℕ, t < k.val.toNat → numsGet nums (i + t) ≤ resGet r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and i < n - k + 1, and every t with 0 <= t < k, if r[i] != -1 then nums[i+t] = r[i] - (k - 1 - t).
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        ∀ t : ℕ, t < k.val.toNat →
          numsGet nums (i + t) = resGet r i - (k.val - 1 - (t : ℤ)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        ∀ t : ℕ, t < k.val.toNat →
          numsGet nums (i + t) = resGet r i - (k.val - 1 - (t : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), i+1 < len(r), i < n - k, and k > 1, if r[i] != -1 and r[i+1] != -1, then r[i+1] = r[i] + 1.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i + 1 < r.val.length →
        (i : ℤ) < (nums.val.length : ℤ) - k.val → 1 < k.val →
        resGet r i ≠ -1 → resGet r (i + 1) ≠ -1 → resGet r (i + 1) = resGet r i + 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i + 1 < r.val.length →
        (i : ℤ) < (nums.val.length : ℤ) - k.val → 1 < k.val →
        resGet r i ≠ -1 → resGet r (i + 1) ≠ -1 → resGet r (i + 1) = resGet r i + 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and i < n - k + 1, if r[i] = -1 then there exists j with i <= j < i+k-1 such that nums[j+1] != nums[j] + 1.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i = -1 →
        ∃ j : ℕ, (i : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) < (i : ℤ) + k.val - 1 ∧
          numsGet nums (j + 1) ≠ numsGet nums j + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i = -1 →
        ∃ j : ℕ, (i : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) < (i : ℤ) + k.val - 1 ∧
          numsGet nums (j + 1) ≠ numsGet nums j + 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and i < n - k + 1, if r[i] != -1 then r[i] >= k.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        k.val ≤ resGet r i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        k.val ≤ resGet r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and i < n - k + 1, if r[i] != -1 then r[i] = nums[i] + k - 1.
  Preconditions: Let n = len(nums). 1 <= n <= 10^5; 1 <= k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 10^6. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        resGet r i = numsGet nums i + k.val - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hv : ∀ j : ℕ, j < nums.val.length → 1 ≤ numsGet nums j ∧ numsGet nums j ≤ 10 ^ 6), ∀ r : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums k = Result.ok r →
      ∀ i : ℕ, i < r.val.length → i < windows nums k → resGet r i ≠ -1 →
        resGet r i = numsGet nums i + k.val - 1) := by
  sorry

end AegisSpec.ResultsArray
