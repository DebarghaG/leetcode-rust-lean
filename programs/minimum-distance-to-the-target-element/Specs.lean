import Aegis.GetMinDistance.Code.Funs

/-!
# Specifications of `Aegis.GetMinDistance.get_min_distance`

LeetCode problem `minimum-distance-to-the-target-element`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetMinDistance

  def nth (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some v => v.val
    | none => 0

  def nthStart (nums : Slice Std.I64) (start : Std.I64) : Int :=
    nth nums start.val.toNat

  def distSet (nums : Slice Std.I64) (target start : Std.I64) (d : Int) : Prop :=
    (∃ i : Nat, (i : Int) < start.val ∧ nth nums i = target.val ∧ d = start.val - (i : Int)) ∨
    (∃ i : Nat, start.val < (i : Int) ∧ (i : Int) < (nums.val.length : Int) ∧
      nth nums i = target.val ∧ d = (i : Int) - start.val)

  /-- The function returns a result r such that: (a) there exists i with 0 <= i < len(nums), nums[i] = target, and r = abs(i - start); and (b) for every j with 0 <= j < len(nums) and nums[j] = target, r <= abs(j - start). Equivalently, r is the minimum of abs(i - start) over all indices i with nums[i] = target.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_1 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (r : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r) :
      (∃ i, i < nums.val.length ∧ nth nums i = target.val ∧ r.val = |(i : Int) - start.val|) ∧
        (∀ j, j < nums.val.length → nth nums j = target.val →
          r.val ≤ |(j : Int) - start.val|) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (r : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r), (∃ i, i < nums.val.length ∧ nth nums i = target.val ∧ r.val = |(i : Int) - start.val|) ∧
          (∀ j, j < nums.val.length → nth nums j = target.val →
            r.val ≤ |(j : Int) - start.val|)) := by
    sorry

  /-- For every input satisfying the preconditions, get_min_distance(nums, target, start) returns a result r; it does not fail, panic, or overflow.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_2 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val) :
      ∃ r, Aegis.GetMinDistance.get_min_distance nums target start = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val), ∃ r, Aegis.GetMinDistance.get_min_distance nums target start = ok r) := by
    sorry

  /-- Whenever get_min_distance(nums, target, start) returns a result r, there exists an index i with 0 <= i < len(nums), nums[i] = target, and r = abs(i - start).
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_3 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (r : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r) :
      ∃ i, i < nums.val.length ∧ nth nums i = target.val ∧ r.val = |(i : Int) - start.val| := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (r : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r), ∃ i, i < nums.val.length ∧ nth nums i = target.val ∧ r.val = |(i : Int) - start.val|) := by
    sorry

  /-- Whenever get_min_distance(nums, target, start) returns a result r, for every index j with 0 <= j < len(nums) and nums[j] = target, we have r <= abs(j - start).
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_4 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (r : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r) :
      ∀ j, j < nums.val.length → nth nums j = target.val →
        r.val ≤ |(j : Int) - start.val| := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (r : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r), ∀ j, j < nums.val.length → nth nums j = target.val →
          r.val ≤ |(j : Int) - start.val|) := by
    sorry

  /-- Whenever get_min_distance(nums, target, start) returns a result r, 0 <= r <= max(start, (len(nums) - 1) - start).
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_5 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (r : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r) :
      0 ≤ r.val ∧ r.val ≤ max start.val ((nums.val.length : Int) - 1 - start.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (r : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r), 0 ≤ r.val ∧ r.val ≤ max start.val ((nums.val.length : Int) - 1 - start.val)) := by
    sorry

  /-- Whenever get_min_distance(nums, target, start) returns a result r and nums[start] = target, we have r = 0.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_6 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (r : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
      (hat : nthStart nums start = target.val) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (r : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
        (hat : nthStart nums start = target.val), r.val = 0) := by
    sorry

  /-- Whenever get_min_distance(nums, target, start) returns a result r and r = 0, we have nums[start] = target.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_7 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (r : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
      (hr0 : r.val = 0) :
      nthStart nums start = target.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (r : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
        (hr0 : r.val = 0), nthStart nums start = target.val) := by
    sorry

  /-- Whenever get_min_distance(nums, target, start) returns a result r and get_min_distance(nums', target, start) returns a result r', we have r = r'.
    Preconditions: The original input satisfies: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. Also nums' is a slice of i64 with len(nums') = len(nums); 1 <= len(nums') <= 1000; for every i with 0 <= i < len(nums'), 1 <= nums'[i] <= 10000; 0 <= start < len(nums'); and for every i with 0 <= i < len(nums), nums[i] = target if and only if nums'[i] = target. -/
  theorem spec_8 (nums nums' : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (hlen' : nums'.val.length = nums.val.length)
      (hlen'_lo : 1 ≤ nums'.val.length) (hlen'_hi : nums'.val.length ≤ 1000)
      (hval' : ∀ i, i < nums'.val.length → 1 ≤ nth nums' i ∧ nth nums' i ≤ 10000)
      (hstart'_hi : start.val < (nums'.val.length : Int))
      (htarget' : ∀ i, i < nums.val.length →
        (nth nums i = target.val ↔ nth nums' i = target.val))
      (r r' : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
      (hr' : Aegis.GetMinDistance.get_min_distance nums' target start = ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (hlen' : nums'.val.length = nums.val.length)
        (hlen'_lo : 1 ≤ nums'.val.length) (hlen'_hi : nums'.val.length ≤ 1000)
        (hval' : ∀ i, i < nums'.val.length → 1 ≤ nth nums' i ∧ nth nums' i ≤ 10000)
        (hstart'_hi : start.val < (nums'.val.length : Int))
        (htarget' : ∀ i, i < nums.val.length →
          (nth nums i = target.val ↔ nth nums' i = target.val))
        (r r' : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
        (hr' : Aegis.GetMinDistance.get_min_distance nums' target start = ok r'), r = r') := by
    sorry

  /-- Define nums_rev by len(nums_rev) = len(nums) and nums_rev[i] = nums[(len(nums) - 1) - i] for every 0 <= i < len(nums), and define start_rev = (len(nums) - 1) - start. Whenever get_min_distance(nums, target, start) returns a result r and get_min_distance(nums_rev, target, start_rev) returns a result r', we have r = r'.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_9 (nums nums_rev : Slice Std.I64) (target start start_rev : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (hrev_len : nums_rev.val.length = nums.val.length)
      (hrev : ∀ i, i < nums.val.length →
        nth nums_rev i = nth nums (nums.val.length - 1 - i))
      (hrev_start : start_rev.val = (nums.val.length : Int) - 1 - start.val)
      (r r' : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
      (hr' : Aegis.GetMinDistance.get_min_distance nums_rev target start_rev = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums_rev : Slice Std.I64) (target start start_rev : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (hrev_len : nums_rev.val.length = nums.val.length)
        (hrev : ∀ i, i < nums.val.length →
          nth nums_rev i = nth nums (nums.val.length - 1 - i))
        (hrev_start : start_rev.val = (nums.val.length : Int) - 1 - start.val)
        (r r' : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
        (hr' : Aegis.GetMinDistance.get_min_distance nums_rev target start_rev = ok r'), r = r') := by
    sorry

  /-- Whenever get_min_distance(nums, target, start) returns a result r and nums[start] != target, r is the minimum of the nonempty set { start - i | 0 <= i < start and nums[i] = target } union { i - start | start < i < len(nums) and nums[i] = target }.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000; 0 <= start < len(nums); there exists k with 0 <= k < len(nums) and nums[k] = target. -/
  theorem spec_10 (nums : Slice Std.I64) (target start : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
      (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
      (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
      (r : Std.I64)
      (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
      (hne : nthStart nums start ≠ target.val) :
      distSet nums target start r.val ∧
        ∀ d, distSet nums target start d → r.val ≤ d := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (target start : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000)
        (hstart_lo : 0 ≤ start.val) (hstart_hi : start.val < (nums.val.length : Int))
        (htarget : ∃ k, k < nums.val.length ∧ nth nums k = target.val)
        (r : Std.I64)
        (hr : Aegis.GetMinDistance.get_min_distance nums target start = ok r)
        (hne : nthStart nums start ≠ target.val), distSet nums target start r.val ∧
          ∀ d, distSet nums target start d → r.val ≤ d) := by
    sorry

  end AegisSpec.GetMinDistance
