import Aegis.ValidSubarrays.Code.Funs

/-!
# Specifications of `Aegis.ValidSubarrays.valid_subarrays`

LeetCode problem `number-of-valid-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidSubarrays

  def entry (nums : Slice Std.I64) (i : Nat) : Int := (nums.val[i]!).val

  @[reducible] def IsValidSub (nums : Slice Std.I64) (l e : Nat) : Prop :=
    l ≤ e ∧ e < nums.val.length ∧ ∀ k, l ≤ k → k ≤ e → entry nums l ≤ entry nums k

  def countAt (nums : Slice Std.I64) (l : Nat) : Nat :=
    (List.range nums.val.length).countP (fun e => decide (IsValidSub nums l e))

  def countValid (nums : Slice Std.I64) : Nat :=
    ((List.range nums.val.length).map (countAt nums)).sum

  def firstSmaller (nums : Slice Std.I64) (l : Nat) : Nat :=
    ((List.range nums.val.length).find?
      (fun j => decide (l < j ∧ entry nums j < entry nums l))).getD nums.val.length

  def countAscents (nums : Slice Std.I64) : Nat :=
    (List.range (nums.val.length - 1)).countP
      (fun i => decide (entry nums i ≤ entry nums (i + 1)))

  def countExtendable (nums : Slice Std.I64) (x : Std.I64) : Nat :=
    (List.range nums.val.length).countP
      (fun l => decide (entry nums l ≤ x.val ∧
        ∀ k, l ≤ k → k < nums.val.length → entry nums l ≤ entry nums k))

  noncomputable section

  /-- The function returns a result r and r equals the number of pairs (l,e) of integers such that 0 <= l <= e < n and, for every k with l <= k <= e, nums[l] <= nums[k]. Equivalently, r is the number of non-empty contiguous subarrays nums[l..e] (inclusive endpoints) whose leftmost element is not larger than every element of the subarray; subarrays with equal element values but different positions are counted separately.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
        r.val = (countValid nums : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
          r.val = (countValid nums : Int)) := by
    sorry

  /-- The function returns a result r and r <= n*(n+1)/2, where the right-hand side is the total number of non-empty contiguous subarrays of an array of length n, evaluated over mathematical integers.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
        r.val ≤ ((n : Int) * ((n : Int) + 1)) / 2 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
          r.val ≤ ((n : Int) * ((n : Int) + 1)) / 2) := by
    sorry

  /-- If n = 1, then the function returns a result r and r = 1.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h1 : n = 1) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h1 : n = 1), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧ r.val = 1) := by
    sorry

  /-- If n = 2, then the function returns a result r and: r = 3 when nums[0] <= nums[1], and r = 2 when nums[0] > nums[1].
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (h2 : n = 2) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
        (entry nums 0 ≤ entry nums 1 → r.val = 3) ∧
        (entry nums 0 > entry nums 1 → r.val = 2) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (h2 : n = 2), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
          (entry nums 0 ≤ entry nums 1 → r.val = 3) ∧
          (entry nums 0 > entry nums 1 → r.val = 2)) := by
    sorry

  /-- The function returns a result r and the following equivalence holds: r = n*(n+1)/2 if and only if for every i with 0 <= i < n-1, nums[i] <= nums[i+1] (that is, nums is non-decreasing).
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
        (r.val = ((n : Int) * ((n : Int) + 1)) / 2 ↔
          ∀ i, i < n - 1 → entry nums i ≤ entry nums (i + 1)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
          (r.val = ((n : Int) * ((n : Int) + 1)) / 2 ↔
            ∀ i, i < n - 1 → entry nums i ≤ entry nums (i + 1))) := by
    sorry

  /-- The function returns a result r and the following equivalence holds: r = n if and only if for every i with 0 <= i < n-1, nums[i] > nums[i+1] (that is, nums is strictly decreasing).
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
        (r.val = (n : Int) ↔
          ∀ i, i < n - 1 → entry nums i > entry nums (i + 1)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
          (r.val = (n : Int) ↔
            ∀ i, i < n - 1 → entry nums i > entry nums (i + 1))) := by
    sorry

  /-- For every l with 0 <= l < n, let m(l) be the smallest index j such that l < j < n and nums[j] < nums[l], or let m(l) = n if there is no such j. Then the function returns a result r and, for every l with 0 <= l < n, the subarrays counted in r that have left endpoint l are exactly nums[l..e] for the integers e with l <= e < m(l).
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
        r.val = (countValid nums : Int) ∧
        (∀ l, l < n → ∀ e, l ≤ e → e < n →
          (IsValidSub nums l e ↔ e < firstSmaller nums l)) ∧
        (∀ l, l < n → countAt nums l = firstSmaller nums l - l) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
          r.val = (countValid nums : Int) ∧
          (∀ l, l < n → ∀ e, l ≤ e → e < n →
            (IsValidSub nums l e ↔ e < firstSmaller nums l)) ∧
          (∀ l, l < n → countAt nums l = firstSmaller nums l - l)) := by
    sorry

  /-- Let A be the number of indices i with 0 <= i < n-1 and nums[i] <= nums[i+1]. For every i with 0 <= i < n, the singleton subarray nums[i..i] satisfies the validity condition, and for every i with 0 <= i < n-1 and nums[i] <= nums[i+1], the length-2 subarray nums[i..i+1] also satisfies the validity condition. Consequently these n + A distinct non-empty subarrays are counted in the result r, so the function returns a result r and r >= n + A.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
        (n : Int) + (countAscents nums : Int) ≤ r.val ∧
        (∀ i, i < n → IsValidSub nums i i) ∧
        (∀ i, i < n - 1 → entry nums i ≤ entry nums (i + 1) →
          IsValidSub nums i (i + 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r ∧
          (n : Int) + (countAscents nums : Int) ≤ r.val ∧
          (∀ i, i < n → IsValidSub nums i i) ∧
          (∀ i, i < n - 1 → entry nums i ≤ entry nums (i + 1) →
            IsValidSub nums i (i + 1))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000) :
      ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r : Std.I64, Aegis.ValidSubarrays.valid_subarrays nums = ok r) := by
    sorry

  /-- Suppose there is an integer c such that nums2[i] = nums[i] + c for every i with 0 <= i < n. If valid_subarrays(nums) returns r1 and valid_subarrays(nums2) returns r2, then r1 = r2.
    Preconditions: nums and nums2 are slices of 64-bit integers, len(nums) = len(nums2) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= nums2[i] <= 100000. -/
  theorem spec_10 (nums nums2 : Slice Std.I64) (n : Nat) (c : Int)
      (hn : nums.val.length = n) (hn2 : nums2.val.length = n)
      (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (hbound2 : ∀ i, i < n → 0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100000)
      (hc : ∀ i, i < n → entry nums2 i = entry nums i + c) :
      ∀ r1 r2 : Std.I64,
        Aegis.ValidSubarrays.valid_subarrays nums = ok r1 →
        Aegis.ValidSubarrays.valid_subarrays nums2 = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat) (c : Int)
        (hn : nums.val.length = n) (hn2 : nums2.val.length = n)
        (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (hbound2 : ∀ i, i < n → 0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100000)
        (hc : ∀ i, i < n → entry nums2 i = entry nums i + c), ∀ r1 r2 : Std.I64,
          Aegis.ValidSubarrays.valid_subarrays nums = ok r1 →
          Aegis.ValidSubarrays.valid_subarrays nums2 = ok r2 → r1.val = r2.val) := by
    sorry

  /-- Suppose there is a positive integer c such that nums2[i] = c * nums[i] for every i with 0 <= i < n. If valid_subarrays(nums) returns r1 and valid_subarrays(nums2) returns r2, then r1 = r2.
    Preconditions: nums and nums2 are slices of 64-bit integers, len(nums) = len(nums2) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= nums2[i] <= 100000. -/
  theorem spec_11 (nums nums2 : Slice Std.I64) (n : Nat) (c : Int)
      (hn : nums.val.length = n) (hn2 : nums2.val.length = n)
      (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (hbound2 : ∀ i, i < n → 0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100000)
      (hcpos : 0 < c)
      (hc : ∀ i, i < n → entry nums2 i = c * entry nums i) :
      ∀ r1 r2 : Std.I64,
        Aegis.ValidSubarrays.valid_subarrays nums = ok r1 →
        Aegis.ValidSubarrays.valid_subarrays nums2 = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat) (c : Int)
        (hn : nums.val.length = n) (hn2 : nums2.val.length = n)
        (hnpos : 1 ≤ n) (hnle : n ≤ 50000)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (hbound2 : ∀ i, i < n → 0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100000)
        (hcpos : 0 < c)
        (hc : ∀ i, i < n → entry nums2 i = c * entry nums i), ∀ r1 r2 : Std.I64,
          Aegis.ValidSubarrays.valid_subarrays nums = ok r1 →
          Aegis.ValidSubarrays.valid_subarrays nums2 = ok r2 → r1.val = r2.val) := by
    sorry

  /-- Let nums2 be the slice of length n+1 with nums2[i] = nums[i] for 0 <= i < n and nums2[n] = x. If valid_subarrays(nums) returns r and valid_subarrays(nums2) returns r2, then r2 = r + 1 + B, where B is the number of indices l with 0 <= l < n such that nums[l] <= x and nums[l] <= nums[k] for every k with l <= k < n.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 49999, for every i with 0 <= i < n, 0 <= nums[i] <= 100000, and x is a 64-bit integer with 0 <= x <= 100000. -/
  theorem spec_12 (nums nums2 : Slice Std.I64) (n : Nat) (x : Std.I64)
      (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 49999)
      (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
      (hx : 0 ≤ x.val ∧ x.val ≤ 100000)
      (hnums2 : nums2.val = nums.val ++ [x]) :
      ∀ r r2 : Std.I64,
        Aegis.ValidSubarrays.valid_subarrays nums = ok r →
        Aegis.ValidSubarrays.valid_subarrays nums2 = ok r2 →
        r2.val = r.val + 1 + (countExtendable nums x : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat) (x : Std.I64)
        (hn : nums.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 49999)
        (hbound : ∀ i, i < n → 0 ≤ entry nums i ∧ entry nums i ≤ 100000)
        (hx : 0 ≤ x.val ∧ x.val ≤ 100000)
        (hnums2 : nums2.val = nums.val ++ [x]), ∀ r r2 : Std.I64,
          Aegis.ValidSubarrays.valid_subarrays nums = ok r →
          Aegis.ValidSubarrays.valid_subarrays nums2 = ok r2 →
          r2.val = r.val + 1 + (countExtendable nums x : Int)) := by
    sorry

  end

  end AegisSpec.ValidSubarrays
