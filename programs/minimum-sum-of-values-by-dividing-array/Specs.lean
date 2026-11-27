import Aegis.MinimumValueSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumValueSum.minimum_value_sum`

LeetCode problem `minimum-sum-of-values-by-dividing-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumValueSum

  def listAnd : List Std.I64 → Option Std.I64
    | [] => none
    | x :: xs => some (xs.foldl (fun a b => a &&& b) x)

  def lastVal (l : List Std.I64) : ℤ :=
    match l.getLast? with
    | some x => x.val
    | none => 0

  def sumLast (ps : List (List Std.I64)) : ℤ := (ps.map lastVal).sum

  def ValidPartition (nums targets : List Std.I64) (ps : List (List Std.I64)) : Prop :=
    ps.flatten = nums ∧
      (∀ p ∈ ps, p ≠ []) ∧
      List.Forall₂ (fun p t => listAnd p = some t) ps targets

  def IsMinLastSum (nums targets : List Std.I64) (r : ℤ) : Prop :=
    (∃ ps, ValidPartition nums targets ps ∧ sumLast ps = r) ∧
      ∀ ps, ValidPartition nums targets ps → r ≤ sumLast ps

  def SumAtIndices (nums : List Std.I64) (k : Nat → Nat) (m : Nat)
      (hk : ∀ i, i < m → k i < nums.length) : ℤ :=
    (List.ofFn (fun i : Fin m => (nums[k i]'(hk i i.isLt)).val)).sum

  /-- Whenever the function returns a result r, the following holds. Call a partition of nums into m contiguous subarrays valid if the subarrays are ordered left to right, the first starts at index 0, the last ends at index len(nums)-1, consecutive subarrays are adjacent (each next subarray starts one index after the previous ends), each subarray is nonempty, and for every i with 0 <= i < m the bitwise AND of the elements of the i-th subarray equals andValues[i]. If at least one valid partition exists, then r equals the minimum, over all valid partitions, of the sum of the last elements of the m subarrays. If no valid partition exists, then r = -1.
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_1
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r) :
      IsMinLastSum nums.val andValues.val r.val ∨
        (r.val = -1 ∧ ¬ ∃ ps, ValidPartition nums.val andValues.val ps) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r), IsMinLastSum nums.val andValues.val r.val ∨
          (r.val = -1 ∧ ¬ ∃ ps, ValidPartition nums.val andValues.val ps)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or panic.
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_2
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000) :
      ∃ r : Std.I64, Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000), ∃ r : Std.I64, Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1, or m <= r <= sum_{i=0}^{len(nums)-1} nums[i].
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_3
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r) :
      r.val = -1 ∨ ((m : ℤ) ≤ r.val ∧ r.val ≤ (nums.val.map (fun x => x.val)).sum) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r), r.val = -1 ∨ ((m : ℤ) ≤ r.val ∧ r.val ≤ (nums.val.map (fun x => x.val)).sum)) := by
    sorry

  /-- Whenever the function returns a result r, if the bitwise AND of all elements of nums equals andValues[0], then r = nums[len(nums)-1]; otherwise r = -1.
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); m = 1; for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_4
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hm1 : m = 1)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r) :
      (listAnd nums.val = andValues.val.head? → r.val = (nums.val[n - 1]'(by omega)).val) ∧
        (listAnd nums.val ≠ andValues.val.head? → r.val = -1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hm1 : m = 1)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r), (listAnd nums.val = andValues.val.head? → r.val = (nums.val[n - 1]'(by omega)).val) ∧
          (listAnd nums.val ≠ andValues.val.head? → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} nums[i] if nums[i] = andValues[i] for every i with 0 <= i < n; otherwise r = -1.
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); m = len(nums); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_5
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hmn : m = nums.val.length)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r) :
      (nums.val = andValues.val → r.val = (nums.val.map (fun x => x.val)).sum) ∧
        (nums.val ≠ andValues.val → r.val = -1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hmn : m = nums.val.length)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r), (nums.val = andValues.val → r.val = (nums.val.map (fun x => x.val)).sum) ∧
          (nums.val ≠ andValues.val → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists a valid partition of nums into m contiguous subarrays (ordered left to right, first starting at index 0, last ending at index len(nums)-1, consecutive and nonempty, with the i-th subarray bitwise AND equal to andValues[i]) whose sum of last elements is exactly r.
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_6
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val ≠ -1) :
      ∃ ps, ValidPartition nums.val andValues.val ps ∧ sumLast ps = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val ≠ -1), ∃ ps, ValidPartition nums.val andValues.val ps ∧ sumLast ps = r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every valid partition of nums into m contiguous subarrays (ordered left to right, first starting at index 0, last ending at index len(nums)-1, consecutive and nonempty, with the i-th subarray bitwise AND equal to andValues[i]) with sum of last elements S, we have r <= S.
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_7
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val ≠ -1) :
      ∀ ps, ValidPartition nums.val andValues.val ps → r.val ≤ sumLast ps := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val ≠ -1), ∀ ps, ValidPartition nums.val andValues.val ps → r.val ≤ sumLast ps) := by
    sorry

  /-- Whenever the function returns a result r with r = -1, there does not exist any valid partition of nums into m contiguous subarrays (ordered left to right, first starting at index 0, last ending at index len(nums)-1, consecutive and nonempty, with the i-th subarray bitwise AND equal to andValues[i]).
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_8
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val = -1) :
      ¬ ∃ ps, ValidPartition nums.val andValues.val ps := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val = -1), ¬ ∃ ps, ValidPartition nums.val andValues.val ps) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r >= nums[len(nums)-1] + (m - 1).
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_9
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val ≠ -1) :
      r.val ≥ (nums.val[n - 1]'(by omega)).val + ((m : ℤ) - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val ≠ -1), r.val ≥ (nums.val[n - 1]'(by omega)).val + ((m : ℤ) - 1)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, (andValues[0] & nums[0]) = andValues[0] and (andValues[m-1] & nums[len(nums)-1]) = andValues[m-1], where & denotes bitwise AND.
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_10
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val ≠ -1) :
      (andValues.val[0]'(by omega) &&& nums.val[0]'(by omega)) =
          andValues.val[0]'(by omega) ∧
        (andValues.val[m - 1]'(by omega) &&& nums.val[n - 1]'(by omega)) =
          andValues.val[m - 1]'(by omega) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val ≠ -1), (andValues.val[0]'(by omega) &&& nums.val[0]'(by omega)) =
            andValues.val[0]'(by omega) ∧
          (andValues.val[m - 1]'(by omega) &&& nums.val[n - 1]'(by omega)) =
            andValues.val[m - 1]'(by omega)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist m integers k_0 < k_1 < ... < k_{m-1} with 0 <= k_0 and k_{m-1} = len(nums)-1 such that r = sum_{i=0}^{m-1} nums[k_i].
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_11
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val ≠ -1) :
      ∃ (k : Nat → Nat) (hk : ∀ i, i < m → k i < nums.val.length),
          (∀ i j, i < j → j < m → k i < k j) ∧
            k (m - 1) = nums.val.length - 1 ∧
              r.val = SumAtIndices nums.val k m hk := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val ≠ -1), ∃ (k : Nat → Nat) (hk : ∀ i, i < m → k i < nums.val.length),
            (∀ i j, i < j → j < m → k i < k j) ∧
              k (m - 1) = nums.val.length - 1 ∧
                r.val = SumAtIndices nums.val k m hk) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, the bitwise AND of all elements of nums equals the bitwise AND of all elements of andValues, i.e., nums[0] & ... & nums[n-1] = andValues[0] & ... & andValues[m-1].
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_12
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val ≠ -1) :
      listAnd nums.val = listAnd andValues.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val ≠ -1), listAnd nums.val = listAnd andValues.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r >= sum_{j=0}^{m-1} andValues[j].
    Preconditions: len(nums) = n with 1 <= n <= 10^4; len(andValues) = m with 1 <= m <= min(n, 10); for every i with 0 <= i < n, 1 <= nums[i] < 10^5; for every j with 0 <= j < m, 0 <= andValues[j] < 10^5. -/
  theorem spec_13
      (nums andValues : Slice Std.I64) (n m : Nat)
      (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
      (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
      (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
      (r : Std.I64)
      (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
      (hr : r.val ≠ -1) :
      r.val ≥ (andValues.val.map (fun y => y.val)).sum := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums andValues : Slice Std.I64) (n m : Nat)
        (hlen_n : nums.val.length = n) (hn : 1 ≤ n) (hnmax : n ≤ 10000)
        (hlen_m : andValues.val.length = m) (hm : 1 ≤ m) (hmmax : m ≤ min n 10)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val < 100000)
        (hand : ∀ y ∈ andValues.val, 0 ≤ y.val ∧ y.val < 100000)
        (r : Std.I64)
        (hret : Aegis.MinimumValueSum.minimum_value_sum nums andValues = ok r)
        (hr : r.val ≠ -1), r.val ≥ (andValues.val.map (fun y => y.val)).sum) := by
    sorry

  end AegisSpec.MinimumValueSum
