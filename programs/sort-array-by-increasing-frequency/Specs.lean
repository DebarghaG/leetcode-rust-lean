import Aegis.FrequencySort.Code.Funs

/-!
# Specifications of `Aegis.FrequencySort.frequency_sort`

LeetCode problem `sort-array-by-increasing-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FrequencySort

  def freq (xs : List Std.I64) (v : Int) : Nat :=
    xs.countP (fun x => x.val = v)

  def occurs (xs : List Std.I64) (v : Int) : Prop :=
    ∃ x ∈ xs, x.val = v

  def lmin : List Std.I64 → Int
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => min acc y.val) x.val

  def lmax : List Std.I64 → Int
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => max acc y.val) x.val

  /-- Let n = len(nums), and for any list xs and integer v let freq(xs, v) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. The function returns a result r (it does not fail), and: (1) len(r) = n; (2) for every integer v, freq(r, v) = freq(nums, v); (3) for every i and j with 0 <= i < j < n, either freq(nums, r[i]) < freq(nums, r[j]), or freq(nums, r[i]) = freq(nums, r[j]) and r[i] >= r[j].
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.FrequencySort.frequency_sort nums = ok r ∧
        r.val.length = nums.val.length ∧
        (∀ v : Int, freq r.val v = freq nums.val v) ∧
        (∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
          freq nums.val (r.val[i]).val < freq nums.val (r.val[j]).val ∨
            (freq nums.val (r.val[i]).val = freq nums.val (r.val[j]).val ∧
              (r.val[j]).val ≤ (r.val[i]).val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.FrequencySort.frequency_sort nums = ok r ∧
          r.val.length = nums.val.length ∧
          (∀ v : Int, freq r.val v = freq nums.val v) ∧
          (∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
            freq nums.val (r.val[i]).val < freq nums.val (r.val[j]).val ∨
              (freq nums.val (r.val[i]).val = freq nums.val (r.val[j]).val ∧
                (r.val[j]).val ≤ (r.val[i]).val))) := by
    sorry

  /-- The function returns a result r; no failure (overflow, out-of-bounds access, panic, or other failure) occurs for any input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.FrequencySort.frequency_sort nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ r : alloc.vec.Vec Std.I64, Aegis.FrequencySort.frequency_sort nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, freq(r, v) = freq(nums, v), where freq(xs, v) is the number of indices i with 0 <= i < len(xs) and xs[i] = v. Equivalently, r is a permutation (multiset rearrangement) of nums.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      ∀ v : Int, freq r.val v = freq nums.val v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), ∀ v : Int, freq r.val v = freq nums.val v) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(r), freq(nums, r[i]) <= freq(nums, r[j]), where freq(nums, v) is the number of indices k with 0 <= k < len(nums) and nums[k] = v.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
        freq nums.val (r.val[i]).val ≤ freq nums.val (r.val[j]).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
          freq nums.val (r.val[i]).val ≤ freq nums.val (r.val[j]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(r), if freq(nums, r[i]) = freq(nums, r[j]), then r[i] >= r[j], where freq(nums, v) is the number of indices k with 0 <= k < len(nums) and nums[k] = v.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length)
        (hfreq : freq nums.val (r.val[i]).val = freq nums.val (r.val[j]).val),
        (r.val[j]).val ≤ (r.val[i]).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length)
          (hfreq : freq nums.val (r.val[i]).val = freq nums.val (r.val[j]).val),
          (r.val[j]).val ≤ (r.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v and all indices i, j, k with 0 <= i < j < k < len(r), if r[i] = v and r[k] = v, then r[j] = v.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      ∀ (v : Int) (i j k : Nat) (hij : i < j) (hjk : j < k) (hk : k < r.val.length),
        (r.val[i]).val = v → (r.val[k]).val = v → (r.val[j]).val = v := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), ∀ (v : Int) (i j k : Nat) (hij : i < j) (hjk : j < k) (hk : k < r.val.length),
          (r.val[i]).val = v → (r.val[k]).val = v → (r.val[j]).val = v) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= 1. Let f0 = freq(nums, r[0]), where freq(nums, v) is the number of indices k with 0 <= k < len(nums) and nums[k] = v. Then for every j with 0 <= j < len(r), f0 <= freq(nums, r[j]); and for every j with 0 <= j < len(r) and freq(nums, r[j]) = f0, r[0] >= r[j].
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      1 ≤ r.val.length ∧
        (∀ (hpos : 0 < r.val.length) (j : Nat) (hj : j < r.val.length),
          freq nums.val (r.val.get ⟨0, hpos⟩).val ≤ freq nums.val (r.val[j]).val ∧
            (freq nums.val (r.val[j]).val = freq nums.val (r.val.get ⟨0, hpos⟩).val →
              (r.val[j]).val ≤ (r.val.get ⟨0, hpos⟩).val)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), 1 ≤ r.val.length ∧
          (∀ (hpos : 0 < r.val.length) (j : Nat) (hj : j < r.val.length),
            freq nums.val (r.val.get ⟨0, hpos⟩).val ≤ freq nums.val (r.val[j]).val ∧
              (freq nums.val (r.val[j]).val = freq nums.val (r.val.get ⟨0, hpos⟩).val →
                (r.val[j]).val ≤ (r.val.get ⟨0, hpos⟩).val))) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), min(nums) <= r[j] <= max(nums), where min(nums) is the minimum of nums[i] over 0 <= i < len(nums) and max(nums) is the maximum of nums[i] over 0 <= i < len(nums).
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      ∀ (j : Nat) (hj : j < r.val.length),
        lmin nums.val ≤ (r.val[j]).val ∧ (r.val[j]).val ≤ lmax nums.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), ∀ (j : Nat) (hj : j < r.val.length),
          lmin nums.val ≤ (r.val[j]).val ∧ (r.val[j]).val ≤ lmax nums.val) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of integers v and w that both occur in nums and satisfy freq(nums, v) < freq(nums, w), every occurrence of v in r precedes every occurrence of w in r; that is, for all i and j with 0 <= i < len(r), 0 <= j < len(r), if r[i] = v and r[j] = w, then i < j. Here freq(nums, x) is the number of indices k with 0 <= k < len(nums) and nums[k] = x.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.FrequencySort.frequency_sort nums = ok r) :
      ∀ (v w : Int) (hv : occurs nums.val v) (hw : occurs nums.val w)
        (hfreq : freq nums.val v < freq nums.val w)
        (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length)
        (hvi : (r.val[i]).val = v) (hwj : (r.val[j]).val = w),
        i < j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.FrequencySort.frequency_sort nums = ok r), ∀ (v w : Int) (hv : occurs nums.val v) (hw : occurs nums.val w)
          (hfreq : freq nums.val v < freq nums.val w)
          (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length)
          (hvi : (r.val[i]).val = v) (hwj : (r.val[j]).val = w),
          i < j) := by
    sorry

  end AegisSpec.FrequencySort
