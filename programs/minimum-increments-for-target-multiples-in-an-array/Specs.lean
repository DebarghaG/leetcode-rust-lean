import Aegis.MinimumIncrements.Code.Funs

/-!
# Specifications of `Aegis.MinimumIncrements.minimum_increments`

LeetCode problem `minimum-increments-for-target-multiples-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumIncrements

namespace AegisSpec.MinimumIncrements

def DvdPos (t x : Int) : Prop := ∃ q : Int, 0 < q ∧ x = q * t

def OccursIn (x : Int) (l : List Std.I64) : Prop := x ∈ l.map (fun s => s.val)

def IsLeastInc (t x c : Int) : Prop :=
  0 ≤ c ∧ DvdPos t (x + c) ∧ ∀ c' : Int, 0 ≤ c' → DvdPos t (x + c') → c ≤ c'

def totalIncrement (b : List Int) (nums : List Std.I64) : Int :=
  ((List.range b.length).map (fun i => b[i]! - (nums[i]!).val)).sum

def IsFeasible (nums : List Std.I64) (target : List Std.I64) (b : List Int) : Prop :=
  b.length = nums.length ∧
    (∀ i, i < b.length → (nums[i]!).val ≤ b[i]!) ∧
    ∀ j, j < target.length → ∃ i, i < b.length ∧ DvdPos (target[j]!).val (b[i]!)

/-- Whenever the function returns a result r, r equals the minimum, over all integer arrays b of length len(nums) satisfying (a) b[i] >= nums[i] for every 0 <= i < len(nums), and (b) for every 0 <= j < len(target) there exists 0 <= i < len(nums) such that target[j] divides b[i], of the sum Σ_{i=0}^{len(nums)-1} (b[i] - nums[i]). Here target[j] divides b[i] means b[i] = q * target[j] for some positive integer q.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_1 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    (∀ b : List Int, IsFeasible nums.val target.val b → totalIncrement b nums.val ≤ r.val) ∧
      ∃ b : List Int,
        IsFeasible nums.val target.val b ∧ totalIncrement b nums.val = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), (∀ b : List Int, IsFeasible nums.val target.val b → totalIncrement b nums.val ≤ r.val) ∧
      ∃ b : List Int,
        IsFeasible nums.val target.val b ∧ totalIncrement b nums.val = r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, panic, or access an out-of-bounds index.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_2 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000) :
    ∃ r : Std.I64, minimum_increments nums target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000), ∃ r : Std.I64, minimum_increments nums target = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_3 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every 0 <= j < len(target) there exists 0 <= i < len(nums) such that target[j] divides nums[i].
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_4 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    r.val = 0 ↔
      ∀ j, j < target.val.length →
        ∃ i, i < nums.val.length ∧ DvdPos (target.val[j]!).val (nums.val[i]!).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), r.val = 0 ↔
      ∀ j, j < target.val.length →
        ∃ i, i < nums.val.length ∧ DvdPos (target.val[j]!).val (nums.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r, for each 0 <= j < len(target) let c_j be the least nonnegative integer such that nums[j] + c_j is a multiple of target[j]. Then r <= Σ_{j=0}^{len(target)-1} c_j.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_5 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∀ c : List Int, c.length = target.val.length →
      (∀ j, j < target.val.length →
        IsLeastInc (target.val[j]!).val (nums.val[j]!).val c[j]!) →
      r.val ≤ c.sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∀ c : List Int, c.length = target.val.length →
      (∀ j, j < target.val.length →
        IsLeastInc (target.val[j]!).val (nums.val[j]!).val c[j]!) →
      r.val ≤ c.sum) := by
  sorry

/-- Whenever the function returns a result r, r = min_{0 <= i < len(nums)} c_i, where c_i is the least nonnegative integer such that nums[i] + c_i is a multiple of target[0].
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000; there exists t with 1 <= t <= 10000 such that target[j] = t for every 0 <= j < len(target). -/
theorem spec_6 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (t : Std.I64) (ht1 : 1 ≤ t.val) (ht2 : t.val ≤ 10000)
    (hconst : ∀ j, j < target.val.length → (target.val[j]!).val = t.val)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    (∃ i, i < nums.val.length ∧ IsLeastInc t.val (nums.val[i]!).val r.val) ∧
      ∀ i, i < nums.val.length → ∀ c : Int,
        IsLeastInc t.val (nums.val[i]!).val c → r.val ≤ c := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (t : Std.I64) (ht1 : 1 ≤ t.val) (ht2 : t.val ≤ 10000)
    (hconst : ∀ j, j < target.val.length → (target.val[j]!).val = t.val)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), (∃ i, i < nums.val.length ∧ IsLeastInc t.val (nums.val[i]!).val r.val) ∧
      ∀ i, i < nums.val.length → ∀ c : Int,
        IsLeastInc t.val (nums.val[i]!).val c → r.val ≤ c) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer array b of length len(nums) such that (a) b[i] >= nums[i] for every 0 <= i < len(nums), (b) for every 0 <= j < len(target) there exists 0 <= i < len(nums) such that target[j] divides b[i], and (c) Σ_{i=0}^{len(nums)-1} (b[i] - nums[i]) = r.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_7 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∃ b : List Int,
      IsFeasible nums.val target.val b ∧ totalIncrement b nums.val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∃ b : List Int,
      IsFeasible nums.val target.val b ∧ totalIncrement b nums.val = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer array b of length len(nums) such that (a) b[i] >= nums[i] for every 0 <= i < len(nums) and (b) for every 0 <= j < len(target) there exists 0 <= i < len(nums) such that target[j] divides b[i], we have Σ_{i=0}^{len(nums)-1} (b[i] - nums[i]) >= r.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_8 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∀ b : List Int, IsFeasible nums.val target.val b → r.val ≤ totalIncrement b nums.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∀ b : List Int, IsFeasible nums.val target.val b → r.val ≤ totalIncrement b nums.val) := by
  sorry

/-- Whenever the function returns r on (nums,target), for every slice target' such that 1 <= len(target') <= 4, len(target') <= len(nums), every target'[h] is between 1 and 10000, and the set of values occurring in target' equals the set of values occurring in target, whenever the function returns r' on (nums,target'), we have r' = r.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_9 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∀ target' : Slice Std.I64,
      1 ≤ target'.val.length → target'.val.length ≤ 4 →
      target'.val.length ≤ nums.val.length →
      (∀ h, h < target'.val.length →
        1 ≤ (target'.val[h]!).val ∧ (target'.val[h]!).val ≤ 10000) →
      (∀ v : Int, OccursIn v target'.val ↔ OccursIn v target.val) →
      ∀ r' : Std.I64, minimum_increments nums target' = ok r' → r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∀ target' : Slice Std.I64,
      1 ≤ target'.val.length → target'.val.length ≤ 4 →
      target'.val.length ≤ nums.val.length →
      (∀ h, h < target'.val.length →
        1 ≤ (target'.val[h]!).val ∧ (target'.val[h]!).val ≤ 10000) →
      (∀ v : Int, OccursIn v target'.val ↔ OccursIn v target.val) →
      ∀ r' : Std.I64, minimum_increments nums target' = ok r' → r'.val = r.val) := by
  sorry

/-- Whenever the function returns r on (nums,target), for every permutation σ of the indices {0,...,len(nums)-1}, let nums' be the slice of length len(nums) with nums'[i] = nums[σ(i)] for every 0 <= i < len(nums). Whenever the function returns r' on (nums',target), we have r' = r.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000. -/
theorem spec_10 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∀ (σ : Equiv.Perm (Fin nums.val.length)) (nums' : Slice Std.I64),
      nums'.val.length = nums.val.length →
      (∀ (i : Nat) (hi : i < nums.val.length),
        (nums'.val[i]!).val = (nums.val[(σ ⟨i, hi⟩).val]!).val) →
      ∀ r' : Std.I64, minimum_increments nums' target = ok r' → r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∀ (σ : Equiv.Perm (Fin nums.val.length)) (nums' : Slice Std.I64),
      nums'.val.length = nums.val.length →
      (∀ (i : Nat) (hi : i < nums.val.length),
        (nums'.val[i]!).val = (nums.val[(σ ⟨i, hi⟩).val]!).val) →
      ∀ r' : Std.I64, minimum_increments nums' target = ok r' → r'.val = r.val) := by
  sorry

/-- Whenever the function returns r on (nums,target), let target' be the slice obtained from target by deleting every entry whose value is 1. Whenever the function returns r' on (nums,target'), we have r' = r.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000; there exists j with target[j] = 1 and there exists k with target[k] != 1. -/
theorem spec_11 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (hone : ∃ j, j < target.val.length ∧ (target.val[j]!).val = 1)
    (hother : ∃ k, k < target.val.length ∧ (target.val[k]!).val ≠ 1)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∀ target' : Slice Std.I64,
      target'.val = target.val.filter (fun x => x.val ≠ 1) →
      ∀ r' : Std.I64, minimum_increments nums target' = ok r' → r'.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (hone : ∃ j, j < target.val.length ∧ (target.val[j]!).val = 1)
    (hother : ∃ k, k < target.val.length ∧ (target.val[k]!).val ≠ 1)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∀ target' : Slice Std.I64,
      target'.val = target.val.filter (fun x => x.val ≠ 1) →
      ∀ r' : Std.I64, minimum_increments nums target' = ok r' → r'.val = r.val) := by
  sorry

/-- Whenever the function returns r on (nums,target), for every integer t with 1 <= t <= 10000, let target' be the slice of length len(target)+1 with target'[h] = target[h] for 0 <= h < len(target) and target'[len(target)] = t. Whenever the function returns r' on (nums,target'), we have r' >= r.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000; len(target) < len(nums) and len(target) <= 3. -/
theorem spec_12 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (hlt : target.val.length < nums.val.length) (h3 : target.val.length ≤ 3)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∀ (t : Std.I64) (ht1 : 1 ≤ t.val) (ht2 : t.val ≤ 10000) (target' : Slice Std.I64),
      target'.val = target.val ++ [t] →
      ∀ r' : Std.I64, minimum_increments nums target' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (hlt : target.val.length < nums.val.length) (h3 : target.val.length ≤ 3)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∀ (t : Std.I64) (ht1 : 1 ≤ t.val) (ht2 : t.val ≤ 10000) (target' : Slice Std.I64),
      target'.val = target.val ++ [t] →
      ∀ r' : Std.I64, minimum_increments nums target' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns r on (nums,target), for every integer v with 1 <= v <= 10000, let nums' be the slice of length len(nums)+1 with nums'[i] = nums[i] for 0 <= i < len(nums) and nums'[len(nums)] = v. Whenever the function returns r' on (nums',target), we have r' <= r.
  Preconditions: len(nums) and len(target) are integers with 1 <= len(nums) <= 50000, 1 <= len(target) <= 4, and len(target) <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; for every j with 0 <= j < len(target), 1 <= target[j] <= 10000; len(nums) < 50000. -/
theorem spec_13 (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (hlt : nums.val.length < 50000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r) :
    ∀ (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 10000) (nums' : Slice Std.I64),
      nums'.val = nums.val ++ [v] →
      ∀ r' : Std.I64, minimum_increments nums' target = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums target : Slice Std.I64)
    (hN1 : 1 ≤ nums.val.length) (hN2 : nums.val.length ≤ 50000)
    (hT1 : 1 ≤ target.val.length) (hT2 : target.val.length ≤ 4)
    (hle : target.val.length ≤ nums.val.length)
    (hnums : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (htarget : ∀ j, j < target.val.length → 1 ≤ (target.val[j]!).val ∧ (target.val[j]!).val ≤ 10000)
    (hlt : nums.val.length < 50000)
    (r : Std.I64) (hr : minimum_increments nums target = ok r), ∀ (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 10000) (nums' : Slice Std.I64),
      nums'.val = nums.val ++ [v] →
      ∀ r' : Std.I64, minimum_increments nums' target = ok r' → r'.val ≤ r.val) := by
  sorry

end AegisSpec.MinimumIncrements
